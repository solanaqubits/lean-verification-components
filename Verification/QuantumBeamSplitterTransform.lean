/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Real lossless beam splitter and its finite two-boson lift

The chosen real phase convention is U = [[t, -r], [r, t]]. This is an
orthogonal two-mode model, not a complex scattering implementation. The finite
three-coordinate lift uses the normalized basis |2,0>, |1,1>, |0,2> and is
linked explicitly to substitution in a homogeneous quadratic polynomial.
Indistinguishability and the Born-rule interpretation of squared amplitudes
are modeling assumptions; no wave packets, detectors or full Fock space occur.
-/

noncomputable section
namespace QuantumBeamSplitterTransform

structure BeamSplitter where
  r : ℝ
  t : ℝ
  h_unitary : r ^ 2 + t ^ 2 = 1

def bs_transform (bs : BeamSplitter) (a b : ℝ) : ℝ × ℝ :=
  (bs.t * a - bs.r * b, bs.r * a + bs.t * b)

/-- The two transformed input basis modes have zero real inner product. -/
theorem channels_orthogonal (bs : BeamSplitter) :
    (bs_transform bs 1 0).1 * (bs_transform bs 0 1).1 +
      (bs_transform bs 1 0).2 * (bs_transform bs 0 1).2 = 0 := by
  dsimp [bs_transform]
  ring

theorem energy_conservation (bs : BeamSplitter) (a b : ℝ) :
    (bs_transform bs a b).1 ^ 2 + (bs_transform bs a b).2 ^ 2 = a ^ 2 + b ^ 2 := by
  calc
    _ = (bs.r ^ 2 + bs.t ^ 2) * (a ^ 2 + b ^ 2) := by dsimp [bs_transform]; ring
    _ = _ := by rw [bs.h_unitary, one_mul]

theorem transform_add (bs : BeamSplitter) (a b c d : ℝ) :
    bs_transform bs (a + c) (b + d) =
      ((bs_transform bs a b).1 + (bs_transform bs c d).1,
       (bs_transform bs a b).2 + (bs_transform bs c d).2) := by
  dsimp [bs_transform]
  congr 1 <;> ring

theorem transform_smul (bs : BeamSplitter) (k a b : ℝ) :
    bs_transform bs (k * a) (k * b) =
      (k * (bs_transform bs a b).1, k * (bs_transform bs a b).2) := by
  dsimp [bs_transform]
  congr 1 <;> ring

/-- Interference terms cancel in total power, but not in each output separately. -/
theorem interference_terms (bs : BeamSplitter) (a b : ℝ) :
    (bs_transform bs a b).1 ^ 2 = bs.t ^ 2 * a ^ 2 + bs.r ^ 2 * b ^ 2 -
      2 * bs.t * bs.r * a * b ∧
    (bs_transform bs a b).2 ^ 2 = bs.r ^ 2 * a ^ 2 + bs.t ^ 2 * b ^ 2 +
      2 * bs.t * bs.r * a * b := by
  constructor <;> dsimp [bs_transform] <;> ring

lemma inv_sqrt_two_sq : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

def symmetricBS : BeamSplitter where
  r := 1 / Real.sqrt 2
  t := 1 / Real.sqrt 2
  h_unitary := by rw [inv_sqrt_two_sq]; norm_num

theorem symmetric_bs_properties (a b : ℝ) :
    symmetricBS.r ^ 2 = 1 / 2 ∧ symmetricBS.t ^ 2 = 1 / 2 ∧
      bs_transform symmetricBS a b = ((a - b) / Real.sqrt 2, (a + b) / Real.sqrt 2) := by
  refine ⟨inv_sqrt_two_sq, inv_sqrt_two_sq, ?_⟩
  dsimp [bs_transform, symmetricBS]
  congr 1 <;> ring

/-- Squared one-photon amplitudes in the two output basis modes. -/
def singlePhotonProbabilities (bs : BeamSplitter) : ℝ × ℝ :=
  ((bs_transform bs 1 0).1 ^ 2, (bs_transform bs 1 0).2 ^ 2)

theorem single_photon_partition (bs : BeamSplitter) :
    singlePhotonProbabilities bs = (bs.t ^ 2, bs.r ^ 2) ∧
    0 ≤ (singlePhotonProbabilities bs).1 ∧ 0 ≤ (singlePhotonProbabilities bs).2 ∧
    (singlePhotonProbabilities bs).1 + (singlePhotonProbabilities bs).2 = 1 := by
  simp only [singlePhotonProbabilities, bs_transform, mul_one, mul_zero, sub_zero, add_zero]
  exact ⟨True.intro, sq_nonneg _, sq_nonneg _, by linarith [bs.h_unitary]⟩

/-- Real amplitudes in the orthonormal occupation basis |2,0>, |1,1>, |0,2>. -/
structure TwoPhotonState where
  a20 : ℝ
  a11 : ℝ
  a02 : ℝ

def twoPhotonNormSq (v : TwoPhotonState) : ℝ := v.a20 ^ 2 + v.a11 ^ 2 + v.a02 ^ 2

/-- Polynomial encoding includes the factorial normalization sqrt(2!) of bunched states. -/
def statePolynomial (v : TwoPhotonState) (x y : ℝ) : ℝ :=
  v.a20 * x ^ 2 / Real.sqrt 2 + v.a11 * x * y + v.a02 * y ^ 2 / Real.sqrt 2

/-- Symmetric-square lift of the same input-mode transformation. -/
def twoPhotonTransform (bs : BeamSplitter) (v : TwoPhotonState) : TwoPhotonState :=
  ⟨bs.t ^ 2 * v.a20 - Real.sqrt 2 * bs.t * bs.r * v.a11 + bs.r ^ 2 * v.a02,
   Real.sqrt 2 * bs.t * bs.r * v.a20 + (bs.t ^ 2 - bs.r ^ 2) * v.a11 -
     Real.sqrt 2 * bs.t * bs.r * v.a02,
   bs.r ^ 2 * v.a20 + Real.sqrt 2 * bs.t * bs.r * v.a11 + bs.t ^ 2 * v.a02⟩

/-- The lift is obtained by substituting the images of both input basis modes. -/
theorem two_photon_polynomial_substitution (bs : BeamSplitter) (v : TwoPhotonState) (x y : ℝ) :
    statePolynomial (twoPhotonTransform bs v) x y =
      statePolynomial v (bs.t * x + bs.r * y) (-bs.r * x + bs.t * y) := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  dsimp [statePolynomial, twoPhotonTransform]
  field_simp
  ring_nf
  simp only [hs]
  ring

/-- Orthogonality of the normalized finite two-photon lift. -/
theorem two_photon_norm_conservation (bs : BeamSplitter) (v : TwoPhotonState) :
    twoPhotonNormSq (twoPhotonTransform bs v) = twoPhotonNormSq v := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  calc
    _ = (bs.r ^ 2 + bs.t ^ 2) ^ 2 * twoPhotonNormSq v := by
      dsimp [twoPhotonNormSq, twoPhotonTransform]
      ring_nf
      simp only [hs]
      ring
    _ = _ := by rw [bs.h_unitary]; ring

def oneEach : TwoPhotonState := ⟨0, 1, 0⟩

/-- Coincidence amplitude is derived from the two-mode lift applied to |1,1>. -/
theorem two_photon_one_each (bs : BeamSplitter) :
    twoPhotonTransform bs oneEach =
      ⟨-Real.sqrt 2 * bs.t * bs.r, bs.t ^ 2 - bs.r ^ 2, Real.sqrt 2 * bs.t * bs.r⟩ := by
  simp [twoPhotonTransform, oneEach]

def coincidenceProbability (bs : BeamSplitter) : ℝ :=
  (twoPhotonTransform bs oneEach).a11 ^ 2

theorem coincidence_formula (bs : BeamSplitter) :
    coincidenceProbability bs = (bs.t ^ 2 - bs.r ^ 2) ^ 2 := by
  simp [coincidenceProbability, two_photon_one_each]

theorem two_photon_probability_partition (bs : BeamSplitter) :
    (twoPhotonTransform bs oneEach).a20 ^ 2 + coincidenceProbability bs +
      (twoPhotonTransform bs oneEach).a02 ^ 2 = 1 := by
  have h := two_photon_norm_conservation bs oneEach
  simpa [twoPhotonNormSq, coincidenceProbability, oneEach] using h

theorem coincidence_bounds (bs : BeamSplitter) :
    0 ≤ coincidenceProbability bs ∧ coincidenceProbability bs ≤ 1 := by
  have h := two_photon_probability_partition bs
  have h20 := sq_nonneg ((twoPhotonTransform bs oneEach).a20)
  have h02 := sq_nonneg ((twoPhotonTransform bs oneEach).a02)
  exact ⟨sq_nonneg _, by linarith⟩

/-- Ideal HOM zero in the indistinguishable two-boson model. -/
theorem hom_coincidence_suppression (bs : BeamSplitter)
    (ht : bs.t ^ 2 = 1 / 2) (hr : bs.r ^ 2 = 1 / 2) :
    (twoPhotonTransform bs oneEach).a11 = 0 ∧ coincidenceProbability bs = 0 := by
  simp [two_photon_one_each, coincidence_formula, ht, hr]

theorem symmetric_hom : coincidenceProbability symmetricBS = 0 :=
  (hom_coincidence_suppression symmetricBS inv_sqrt_two_sq inv_sqrt_two_sq).2

/-- With losslessness, the ideal coincidence zero occurs exactly at balanced power splitting. -/
theorem hom_zero_iff_balanced (bs : BeamSplitter) :
    coincidenceProbability bs = 0 ↔ bs.t ^ 2 = 1 / 2 ∧ bs.r ^ 2 = 1 / 2 := by
  rw [coincidence_formula]
  constructor
  · intro h
    have he : bs.t ^ 2 - bs.r ^ 2 = 0 := (sq_eq_zero_iff).mp h
    constructor <;> linarith [bs.h_unitary]
  · rintro ⟨ht, hr⟩
    rw [ht, hr]
    norm_num

structure BeamSplitterFormalSuite : Prop where
  h_energy : ∀ bs a b, (bs_transform bs a b).1 ^ 2 + (bs_transform bs a b).2 ^ 2 = a ^ 2 + b ^ 2
  h_orthogonal : ∀ bs, (bs_transform bs 1 0).1 * (bs_transform bs 0 1).1 +
    (bs_transform bs 1 0).2 * (bs_transform bs 0 1).2 = 0
  h_symmetric : ∀ a b, symmetricBS.r ^ 2 = 1 / 2 ∧ symmetricBS.t ^ 2 = 1 / 2 ∧
    bs_transform symmetricBS a b = ((a - b) / Real.sqrt 2, (a + b) / Real.sqrt 2)
  h_single : ∀ bs, singlePhotonProbabilities bs = (bs.t ^ 2, bs.r ^ 2) ∧
    0 ≤ (singlePhotonProbabilities bs).1 ∧ 0 ≤ (singlePhotonProbabilities bs).2 ∧
    (singlePhotonProbabilities bs).1 + (singlePhotonProbabilities bs).2 = 1
  h_lift : ∀ bs v x y, statePolynomial (twoPhotonTransform bs v) x y =
    statePolynomial v (bs.t * x + bs.r * y) (-bs.r * x + bs.t * y)
  h_two_norm : ∀ bs v, twoPhotonNormSq (twoPhotonTransform bs v) = twoPhotonNormSq v
  h_hom : ∀ bs, bs.t ^ 2 = 1 / 2 → bs.r ^ 2 = 1 / 2 →
    (twoPhotonTransform bs oneEach).a11 = 0 ∧ coincidenceProbability bs = 0
  h_zero_iff : ∀ bs, coincidenceProbability bs = 0 ↔ bs.t ^ 2 = 1 / 2 ∧ bs.r ^ 2 = 1 / 2

theorem beam_splitter_master_suite : BeamSplitterFormalSuite := {
  h_energy := energy_conservation
  h_orthogonal := channels_orthogonal
  h_symmetric := symmetric_bs_properties
  h_single := single_photon_partition
  h_lift := two_photon_polynomial_substitution
  h_two_norm := two_photon_norm_conservation
  h_hom := hom_coincidence_suppression
  h_zero_iff := hom_zero_iff_balanced
}

end QuantumBeamSplitterTransform
