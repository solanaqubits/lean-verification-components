import Verification.QuantumBeamSplitterTransform

open QuantumBeamSplitterTransform

noncomputable section

private def transparent : BeamSplitter := ⟨0, 1, by norm_num⟩
private def reflecting : BeamSplitter := ⟨1, 0, by norm_num⟩
private def unbalanced : BeamSplitter := ⟨3 / 5, 4 / 5, by norm_num⟩
private def signedBalanced : BeamSplitter :=
  ⟨-(1 / Real.sqrt 2), 1 / Real.sqrt 2, by
    rw [neg_sq, inv_sqrt_two_sq]; norm_num⟩

-- Endpoint cases cannot display HOM suppression.
example : coincidenceProbability transparent = 1 ∧ coincidenceProbability reflecting = 1 := by
  norm_num [coincidence_formula, transparent, reflecting]

-- Exact non-balanced case and single-photon output partition.
example : coincidenceProbability unbalanced = 49 / 625 ∧
    singlePhotonProbabilities unbalanced = (16 / 25, 9 / 25) := by
  norm_num [coincidence_formula, singlePhotonProbabilities, bs_transform, unbalanced]

-- Arbitrary real vectors are not assumed unit-normalized.
example : twoPhotonNormSq (twoPhotonTransform unbalanced ⟨1, -2, 3⟩) = 14 := by
  rw [two_photon_norm_conservation]
  norm_num [twoPhotonNormSq]

-- Balanced bunched outcomes each carry 1/2 of the norm; coincidence has zero norm.
example : (twoPhotonTransform symmetricBS oneEach).a20 ^ 2 = 1 / 2 ∧
    coincidenceProbability symmetricBS = 0 ∧
    (twoPhotonTransform symmetricBS oneEach).a02 ^ 2 = 1 / 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [symmetric_hom, two_photon_one_each]
  norm_num [symmetricBS, mul_pow, inv_sqrt_two_sq, hs]

-- The chosen sign convention permits negative reflection amplitude.
example : coincidenceProbability signedBalanced = 0 := by
  apply (hom_coincidence_suppression signedBalanced inv_sqrt_two_sq ?_).2
  change (-(1 / Real.sqrt 2) : ℝ) ^ 2 = 1 / 2
  rw [neg_sq, inv_sqrt_two_sq]

-- Mode-level interference: equal real input amplitudes cancel at the first output.
example : (bs_transform symmetricBS 1 1).1 = 0 ∧
    (bs_transform symmetricBS 1 1).2 ^ 2 = 2 := by
  have h := energy_conservation symmetricBS 1 1
  have hz : (bs_transform symmetricBS 1 1).1 = 0 := by
    norm_num [bs_transform, symmetricBS]
  exact ⟨hz, by rw [hz] at h; norm_num at h; exact h⟩

-- Squaring paths independently loses the interference term. It gives 1/2, not HOM zero.
example : symmetricBS.t ^ 4 + symmetricBS.r ^ 4 = 1 / 2 ∧
    coincidenceProbability symmetricBS ≠ symmetricBS.t ^ 4 + symmetricBS.r ^ 4 := by
  have ht : symmetricBS.t ^ 2 = 1 / 2 := inv_sqrt_two_sq
  have hr : symmetricBS.r ^ 2 = 1 / 2 := inv_sqrt_two_sq
  have he : symmetricBS.t ^ 4 + symmetricBS.r ^ 4 = 1 / 2 := by
    calc
      _ = (symmetricBS.t ^ 2) ^ 2 + (symmetricBS.r ^ 2) ^ 2 := by ring
      _ = _ := by rw [ht, hr]; norm_num
  exact ⟨he, by rw [symmetric_hom, he]; norm_num⟩

-- The lift agrees with input-mode substitution, including a bunched input.
example (x y : ℝ) :
    statePolynomial (twoPhotonTransform unbalanced ⟨1, 0, 0⟩) x y =
      ((4 / 5 * x + 3 / 5 * y) ^ 2) / Real.sqrt 2 := by
  rw [two_photon_polynomial_substitution]
  norm_num [statePolynomial, unbalanced]
