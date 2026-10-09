import Verification.PhotonicsHongOuMandelInterference

open PhotonicsHongOuMandelInterference

example (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : TwoPhotonState) :
    normSquared ((U_two_photon T).mulVec v) = normSquared v :=
  two_photon_norm_preserved T hT hT1 v

example (A : ModeMatrix) (v : TwoPhotonState) (x y : ℂ) :
    statePolynomial ((symmetricSquare A).mulVec v) x y =
      statePolynomial v (A 0 0 * x + A 1 0 * y) (A 0 1 * x + A 1 1 * y) :=
  symmetric_square_substitution A v x y

example : outcomeProbability (1 / 2) 1 = 0 ∧
    homOutput (1 / 2) = (Complex.I / (Real.sqrt 2 : ℂ)) • (basis20 + basis02) :=
  hom_balanced_bunching

example : outcomeProbability (1 / 4) 0 = 3 / 8 ∧
    outcomeProbability (1 / 4) 1 = 1 / 4 ∧ outcomeProbability (1 / 4) 2 = 3 / 8 := by
  have h := hom_probabilities_exact (1 / 4) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

example : distinguishableCoincidence (1 / 4) = 5 / 8 ∧ homVisibility (1 / 4) = 3 / 5 := by
  rw [(hom_distinguishable_baseline (1 / 4) (by norm_num) (by norm_num)).1,
    hom_visibility_formula (1 / 4) (by norm_num) (by norm_num)]
  norm_num

example : distinguishableCoincidence (1 / 2) = 1 / 2 ∧ homVisibility (1 / 2) = 1 := by
  rw [(hom_distinguishable_baseline (1 / 2) (by norm_num) (by norm_num)).1,
    hom_visibility_formula (1 / 2) (by norm_num) (by norm_num)]
  norm_num

example : outcomeProbability 0 1 = 1 ∧ homVisibility 0 = 0 ∧
    outcomeProbability 1 1 = 1 ∧ homVisibility 1 = 0 := by
  rw [(hom_probabilities_exact 0 (by norm_num) (by norm_num)).2.1,
    (hom_probabilities_exact 1 (by norm_num) (by norm_num)).2.1,
    hom_visibility_formula 0 (by norm_num) (by norm_num),
    hom_visibility_formula 1 (by norm_num) (by norm_num)]
  norm_num

example (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : Fin 3) :
    outcomeProbability T j = Complex.normSq (embedReal
      (QuantumBeamSplitterTransform.twoPhotonTransform (realSplitter T hT hT1)
        QuantumBeamSplitterTransform.oneEach) j) :=
  hom_real_convention_probabilities T hT hT1 j

example (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : TwoPhotonState) (j : Fin 3) :
    Complex.normSq ((U_two_photon T).mulVec (occupationGauge.mulVec v) j) =
      Complex.normSq ((symmetricSquare (realModeMatrix (realSplitter T hT hT1))).mulVec v j) :=
  phase_convention_probabilities T hT hT1 v j

example (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j k : Fin 2) :
    labeledWeight T j k = (∑ b : Fin 2, labeledWeight T j b) *
      (∑ a : Fin 2, labeledWeight T a k) :=
  labeled_weight_independence T hT hT1 j k

example (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    ∑ j : Fin 2, ∑ k : Fin 2, labeledWeight T j k = 1 :=
  labeled_weight_normalization T hT hT1

example : PhotonicsHongOuMandelInterferenceSuite := photonics_hong_ou_mandel_master_suite
