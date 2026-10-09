/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PhotonicsBeamSplitterPhaseShift
import Verification.QuantumBeamSplitterTransform

/-! Finite normalized two-boson sector of the specified lossless complex splitter.
Independent labeled paths supply the distinguishable reference; no temporal dip is modeled. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace PhotonicsHongOuMandelInterference

abbrev TwoPhotonBasis := Fin 3
abbrev TwoPhotonState := TwoPhotonBasis → ℂ
abbrev TwoPhotonMatrix := Matrix TwoPhotonBasis TwoPhotonBasis ℂ
abbrev ModeMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- Normalized occupation basis: x²/√2, xy, y²/√2. -/
def statePolynomial (v : TwoPhotonState) (x y : ℂ) : ℂ :=
  v 0 * x ^ 2 / (Real.sqrt 2 : ℂ) + v 1 * x * y + v 2 * y ^ 2 / (Real.sqrt 2 : ℂ)

/-- Symmetric square in the normalized occupation basis, with output rows and input columns. -/
def symmetricSquare (A : ModeMatrix) : TwoPhotonMatrix :=
  ![![A 0 0 ^ 2, (Real.sqrt 2 : ℂ) * A 0 0 * A 0 1, A 0 1 ^ 2],
    ![(Real.sqrt 2 : ℂ) * A 0 0 * A 1 0, A 0 0 * A 1 1 + A 0 1 * A 1 0,
      (Real.sqrt 2 : ℂ) * A 0 1 * A 1 1],
    ![A 1 0 ^ 2, (Real.sqrt 2 : ℂ) * A 1 0 * A 1 1, A 1 1 ^ 2]]

def U_two_photon (T : ℝ) : TwoPhotonMatrix :=
  symmetricSquare (PhotonicsBeamSplitterPhaseShift.splitter T)

def basis20 : TwoPhotonState := ![1, 0, 0]
def basis11 : TwoPhotonState := ![0, 1, 0]
def basis02 : TwoPhotonState := ![0, 0, 1]
def homOutput (T : ℝ) : TwoPhotonState := (U_two_photon T).mulVec basis11
def outcomeProbability (T : ℝ) (j : TwoPhotonBasis) : ℝ := Complex.normSq (homOutput T j)

theorem symmetric_square_substitution (A : ModeMatrix) (v : TwoPhotonState) (x y : ℂ) :
    statePolynomial ((symmetricSquare A).mulVec v) x y =
      statePolynomial v (A 0 0 * x + A 1 0 * y) (A 0 1 * x + A 1 1 * y) := by
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    norm_cast
    exact Real.sq_sqrt (by norm_num)
  have hn : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
  simp only [statePolynomial, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  simp only [symmetricSquare, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  field_simp
  ring_nf
  simp only [hs]
  ring

theorem bunching_coefficient (T : ℝ) (hT : 0 ≤ T) :
    Real.sqrt (2 * T * (1 - T)) = Real.sqrt 2 * Real.sqrt T * Real.sqrt (1 - T) := by
  rw [Real.sqrt_mul (mul_nonneg (by norm_num) hT), Real.sqrt_mul (by norm_num)]

def closedMatrix (T : ℝ) : TwoPhotonMatrix :=
  let k : ℂ := Complex.I * (Real.sqrt (2 * T * (1 - T)) : ℂ)
  ![![(T : ℂ), k, -(1 - (T : ℂ))],
    ![k, (2 * (T : ℂ) - 1), k],
    ![-(1 - (T : ℂ)), k, (T : ℂ)]]

theorem two_photon_matrix_exact (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    U_two_photon T = closedMatrix T := by
  have ht := Real.sq_sqrt hT
  have hr := Real.sq_sqrt (by linarith : 0 ≤ 1 - T)
  ext i j : 2
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [U_two_photon, symmetricSquare, PhotonicsBeamSplitterPhaseShift.splitter,
      closedMatrix, bunching_coefficient T hT, pow_two, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem two_photon_unitary (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (U_two_photon T).conjTranspose * U_two_photon T = 1 ∧
    U_two_photon T * (U_two_photon T).conjTranspose = 1 := by
  have hk := Real.sq_sqrt (by positivity : 0 ≤ 2 * T * (1 - T))
  rw [two_photon_matrix_exact T hT hT1]
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp [closedMatrix, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem hom_output_state_exact (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    homOutput T = ![Complex.I * (Real.sqrt (2 * T * (1 - T)) : ℂ),
      (T - (1 - T) : ℝ), Complex.I * (Real.sqrt (2 * T * (1 - T)) : ℂ)] := by
  rw [homOutput, two_photon_matrix_exact T hT hT1]
  ext j
  fin_cases j <;> simp [closedMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three, basis11]
  ring

theorem hom_probabilities_exact (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    outcomeProbability T 0 = 2 * T * (1 - T) ∧
    outcomeProbability T 1 = (2 * T - 1) ^ 2 ∧
    outcomeProbability T 2 = 2 * T * (1 - T) := by
  have hk := Real.mul_self_sqrt (by positivity : 0 ≤ 2 * T * (1 - T))
  simp [outcomeProbability, hom_output_state_exact T hT hT1, Complex.normSq_apply, hk]
  ring

theorem hom_prob_normalization (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    outcomeProbability T 0 + outcomeProbability T 1 + outcomeProbability T 2 = 1 := by
  obtain ⟨h₀, h₁, h₂⟩ := hom_probabilities_exact T hT hT1
  rw [h₀, h₁, h₂]
  ring

theorem hom_probability_bounds (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : Fin 3) :
    0 ≤ outcomeProbability T j ∧ outcomeProbability T j ≤ 1 := by
  have h₀ := Complex.normSq_nonneg (homOutput T 0)
  have h₁ := Complex.normSq_nonneg (homOutput T 1)
  have h₂ := Complex.normSq_nonneg (homOutput T 2)
  have hn := hom_prob_normalization T hT hT1
  change 0 ≤ outcomeProbability T 0 at h₀
  change 0 ≤ outcomeProbability T 1 at h₁
  change 0 ≤ outcomeProbability T 2 at h₂
  refine ⟨Complex.normSq_nonneg _, ?_⟩
  fin_cases j
  · change outcomeProbability T 0 ≤ 1
    linarith
  · change outcomeProbability T 1 ≤ 1
    linarith
  · change outcomeProbability T 2 ≤ 1
    linarith

theorem hom_balanced_bunching :
    outcomeProbability (1 / 2) 1 = 0 ∧
    homOutput (1 / 2) = (Complex.I / (Real.sqrt 2 : ℂ)) • (basis20 + basis02) := by
  have hs : Real.sqrt (1 / 2) = 1 / Real.sqrt 2 := by
    rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one]
  constructor
  · rw [(hom_probabilities_exact (1 / 2) (by norm_num) (by norm_num)).2.1]
    norm_num
  · rw [hom_output_state_exact (1 / 2) (by norm_num) (by norm_num)]
    ext j
    fin_cases j <;> norm_num [basis20, basis02, hs, div_eq_mul_inv]

/-- Single-mode phase convention Q=diag(1,i). -/
def modeGauge : ModeMatrix := ![![1, 0], ![0, Complex.I]]
/-- Its induced occupation-basis phase is diag(1,i,-1). -/
def occupationGauge : TwoPhotonMatrix := ![![1, 0, 0], ![0, Complex.I, 0], ![0, 0, -1]]

def realModeMatrix (bs : QuantumBeamSplitterTransform.BeamSplitter) : ModeMatrix :=
  ![![(bs.t : ℂ), -(bs.r : ℂ)], ![(bs.r : ℂ), (bs.t : ℂ)]]

def realSplitter (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    QuantumBeamSplitterTransform.BeamSplitter where
  r := Real.sqrt (1 - T)
  t := Real.sqrt T
  h_unitary := by rw [Real.sq_sqrt hT, Real.sq_sqrt (by linarith)]; ring

def embedReal (v : QuantumBeamSplitterTransform.TwoPhotonState) : TwoPhotonState :=
  ![(v.a20 : ℂ), (v.a11 : ℂ), (v.a02 : ℂ)]

theorem real_lift_agrees (bs : QuantumBeamSplitterTransform.BeamSplitter)
    (v : QuantumBeamSplitterTransform.TwoPhotonState) :
    (symmetricSquare (realModeMatrix bs)).mulVec (embedReal v) =
      embedReal (QuantumBeamSplitterTransform.twoPhotonTransform bs v) := by
  ext j
  fin_cases j <;> apply Complex.ext <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, symmetricSquare, realModeMatrix,
      embedReal, QuantumBeamSplitterTransform.twoPhotonTransform,
      pow_two, Complex.mul_re, Complex.mul_im]
  all_goals ring_nf
  all_goals simp

theorem mode_phase_bridge (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    PhotonicsBeamSplitterPhaseShift.splitter T =
      modeGauge * realModeMatrix (realSplitter T hT hT1) * modeGauge.conjTranspose := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;>
    simp [PhotonicsBeamSplitterPhaseShift.splitter, modeGauge, realModeMatrix, realSplitter,
      Complex.mul_re, Complex.mul_im]

theorem occupation_gauge_induced : symmetricSquare modeGauge = occupationGauge := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;> simp [symmetricSquare, modeGauge, occupationGauge]

theorem occupation_gauge_unitary :
    occupationGauge.conjTranspose * occupationGauge = 1 ∧
    occupationGauge * occupationGauge.conjTranspose = 1 := by
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] <;>
    simp [occupationGauge]

/-- This is a matrix identity for all inputs, not just a coincidence-probability comparison. -/
theorem phase_convention_bridge (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    U_two_photon T = occupationGauge *
      symmetricSquare (realModeMatrix (realSplitter T hT hT1)) * occupationGauge.conjTranspose := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;>
    simp [U_two_photon, symmetricSquare, PhotonicsBeamSplitterPhaseShift.splitter,
      occupationGauge, realModeMatrix, realSplitter, pow_two, Complex.mul_re, Complex.mul_im]

theorem occupation_gauge_probability (v : TwoPhotonState) (j : Fin 3) :
    Complex.normSq (occupationGauge.mulVec v j) = Complex.normSq (v j) := by
  fin_cases j <;>
    simp [occupationGauge, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Complex.normSq_mul]

/-- Inputs must also be rephased when comparing the two conventions. -/
theorem phase_convention_probabilities (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (v : TwoPhotonState) (j : Fin 3) :
    Complex.normSq ((U_two_photon T).mulVec (occupationGauge.mulVec v) j) =
      Complex.normSq ((symmetricSquare (realModeMatrix (realSplitter T hT hT1))).mulVec v j) := by
  rw [phase_convention_bridge T hT hT1]
  have h : (occupationGauge * symmetricSquare (realModeMatrix (realSplitter T hT hT1)) *
      occupationGauge.conjTranspose) * occupationGauge =
      occupationGauge * symmetricSquare (realModeMatrix (realSplitter T hT hT1)) := by
    rw [Matrix.mul_assoc, occupation_gauge_unitary.1, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]
  exact occupation_gauge_probability _ j

/-- Independent labeled photons: one enters column 0 and the other column 1.
The two output labels are retained, so the exchanged alternatives are exclusive. -/
def labeledWeight (T : ℝ) (j k : Fin 2) : ℝ :=
  Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T j 0) *
    Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T k 1)

def distinguishableCoincidence (T : ℝ) : ℝ :=
  ∑ j : Fin 2, ∑ k : Fin 2, if j ≠ k then labeledWeight T j k else 0

theorem labeled_weight_nonnegative (T : ℝ) (j k : Fin 2) : 0 ≤ labeledWeight T j k :=
  mul_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem single_mode_weights (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T 0 0) = T ∧
    Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T 1 0) = 1 - T ∧
    Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T 0 1) = 1 - T ∧
    Complex.normSq (PhotonicsBeamSplitterPhaseShift.splitter T 1 1) = T := by
  simp [PhotonicsBeamSplitterPhaseShift.splitter, Complex.normSq_apply,
    Real.mul_self_sqrt hT, Real.mul_self_sqrt (by linarith : 0 ≤ 1 - T)]

theorem labeled_weight_normalization (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    ∑ j : Fin 2, ∑ k : Fin 2, labeledWeight T j k = 1 := by
  obtain ⟨ha, hb, hc, hd⟩ := single_mode_weights T hT hT1
  simp only [Fin.sum_univ_two, labeledWeight, ha, hb, hc, hd]
  ring

/-- The joint weights equal the product of their actual marginals. -/
theorem labeled_weight_independence (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j k : Fin 2) :
    labeledWeight T j k = (∑ b : Fin 2, labeledWeight T j b) *
      (∑ a : Fin 2, labeledWeight T a k) := by
  obtain ⟨ha, hb, hc, hd⟩ := single_mode_weights T hT hT1
  simp only [Fin.sum_univ_two, labeledWeight, ha, hb, hc, hd]
  ring

theorem hom_distinguishable_baseline (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    distinguishableCoincidence T = T ^ 2 + (1 - T) ^ 2 ∧
    1 / 2 ≤ distinguishableCoincidence T ∧ 0 < distinguishableCoincidence T := by
  obtain ⟨ha, hb, hc, hd⟩ := single_mode_weights T hT hT1
  have he : distinguishableCoincidence T = T ^ 2 + (1 - T) ^ 2 := by
    simp [distinguishableCoincidence, Fin.sum_univ_two, labeledWeight, ha, hb, hc, hd, pow_two]
  refine ⟨he, ?_, ?_⟩ <;> rw [he] <;> nlinarith [sq_nonneg (T - 1 / 2)]

/-- HOM visibility uses the distinguishable reference, not Michelson's max+min denominator. -/
def homVisibility (T : ℝ) : ℝ :=
  (distinguishableCoincidence T - outcomeProbability T 1) / distinguishableCoincidence T

theorem hom_visibility_formula (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    homVisibility T = 2 * T * (1 - T) / (T ^ 2 + (1 - T) ^ 2) := by
  rw [homVisibility, (hom_distinguishable_baseline T hT hT1).1,
    (hom_probabilities_exact T hT hT1).2.1]
  congr 1
  ring

theorem hom_visibility_exact (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    homVisibility T = 2 * T * (1 - T) / (T ^ 2 + (1 - T) ^ 2) ∧
    (0 ≤ homVisibility T ∧ homVisibility T ≤ 1) ∧
    (homVisibility T = 1 ↔ T = 1 / 2) := by
  have hp : 0 < T ^ 2 + (1 - T) ^ 2 := by nlinarith [sq_nonneg (T - 1 / 2)]
  have he := hom_visibility_formula T hT hT1
  refine ⟨he, ?_, ?_⟩
  · rw [he]
    constructor
    · apply div_nonneg _ hp.le
      positivity
    · apply (div_le_one hp).mpr
      nlinarith [sq_nonneg (2 * T - 1)]
  · rw [he, (div_eq_one_iff_eq hp.ne')]
    constructor
    · intro h
      nlinarith [sq_nonneg (2 * T - 1)]
    · intro h
      rw [h]
      norm_num

theorem occupation_gauge_one_each : occupationGauge.mulVec basis11 = Complex.I • basis11 := by
  ext j
  fin_cases j <;> simp [occupationGauge, Matrix.mulVec, dotProduct, Fin.sum_univ_three, basis11]

/-- For |1,1>, rephasing the input only contributes a global phase. -/
theorem hom_real_convention_probabilities (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : Fin 3) :
    outcomeProbability T j = Complex.normSq (embedReal
      (QuantumBeamSplitterTransform.twoPhotonTransform (realSplitter T hT hT1)
        QuantumBeamSplitterTransform.oneEach) j) := by
  rw [← real_lift_agrees]
  have h := phase_convention_probabilities T hT hT1 basis11 j
  rw [occupation_gauge_one_each, Matrix.mulVec_smul] at h
  simpa [outcomeProbability, homOutput, Pi.smul_apply, Complex.normSq_mul,
    basis11, embedReal, QuantumBeamSplitterTransform.oneEach] using h

/-- Squared Hermitian Euclidean norm on the finite occupation sector. -/
def normSquared (v : TwoPhotonState) : ℝ := ∑ j, Complex.normSq (v j)

theorem hermitian_norm_identity (v : TwoPhotonState) :
    (normSquared v : ℂ) = star v ⬝ᵥ v := by
  simp only [normSquared, Complex.ofReal_sum, dotProduct, Pi.star_apply,
    Complex.normSq_eq_conj_mul_self, Complex.star_def]

theorem two_photon_norm_preserved (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (v : TwoPhotonState) : normSquared ((U_two_photon T).mulVec v) = normSquared v := by
  apply Complex.ofReal_injective
  rw [hermitian_norm_identity, hermitian_norm_identity, Matrix.star_mulVec]
  rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, (two_photon_unitary T hT hT1).1,
    Matrix.one_mulVec]

theorem mode_gauge_unitary : modeGauge.conjTranspose * modeGauge = 1 ∧
    modeGauge * modeGauge.conjTranspose = 1 := by
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    simp [modeGauge]

structure PhotonicsHongOuMandelInterferenceSuite : Prop where
  normalized_substitution : ∀ T v x y,
    statePolynomial ((U_two_photon T).mulVec v) x y = statePolynomial v
      (PhotonicsBeamSplitterPhaseShift.splitter T 0 0 * x +
        PhotonicsBeamSplitterPhaseShift.splitter T 1 0 * y)
      (PhotonicsBeamSplitterPhaseShift.splitter T 0 1 * x +
        PhotonicsBeamSplitterPhaseShift.splitter T 1 1 * y)
  unitary : ∀ T, 0 ≤ T → T ≤ 1 →
    (U_two_photon T).conjTranspose * U_two_photon T = 1 ∧
    U_two_photon T * (U_two_photon T).conjTranspose = 1
  norm_preservation : ∀ T, 0 ≤ T → T ≤ 1 → ∀ v,
    normSquared ((U_two_photon T).mulVec v) = normSquared v
  exact_output : ∀ T, 0 ≤ T → T ≤ 1 →
    homOutput T = ![Complex.I * (Real.sqrt (2 * T * (1 - T)) : ℂ),
      (T - (1 - T) : ℝ), Complex.I * (Real.sqrt (2 * T * (1 - T)) : ℂ)]
  probabilities : ∀ T, 0 ≤ T → T ≤ 1 →
    outcomeProbability T 0 = 2 * T * (1 - T) ∧
    outcomeProbability T 1 = (2 * T - 1) ^ 2 ∧
    outcomeProbability T 2 = 2 * T * (1 - T)
  normalization : ∀ T, 0 ≤ T → T ≤ 1 →
    outcomeProbability T 0 + outcomeProbability T 1 + outcomeProbability T 2 = 1
  balanced_bunching : outcomeProbability (1 / 2) 1 = 0 ∧
    homOutput (1 / 2) = (Complex.I / (Real.sqrt 2 : ℂ)) • (basis20 + basis02)
  phase_bridge : ∀ T (hT : 0 ≤ T) (hT1 : T ≤ 1), U_two_photon T = occupationGauge *
    symmetricSquare (realModeMatrix (realSplitter T hT hT1)) * occupationGauge.conjTranspose
  probability_bridge : ∀ T (hT : 0 ≤ T) (hT1 : T ≤ 1) j,
    outcomeProbability T j = Complex.normSq (embedReal
      (QuantumBeamSplitterTransform.twoPhotonTransform (realSplitter T hT hT1)
        QuantumBeamSplitterTransform.oneEach) j)
  distinguishable_normalization : ∀ T, 0 ≤ T → T ≤ 1 →
    ∑ j : Fin 2, ∑ k : Fin 2, labeledWeight T j k = 1
  independent_paths : ∀ T, 0 ≤ T → T ≤ 1 → ∀ j k,
    labeledWeight T j k = (∑ b : Fin 2, labeledWeight T j b) *
      (∑ a : Fin 2, labeledWeight T a k)
  distinguishable_baseline : ∀ T, 0 ≤ T → T ≤ 1 →
    distinguishableCoincidence T = T ^ 2 + (1 - T) ^ 2 ∧
    1 / 2 ≤ distinguishableCoincidence T ∧ 0 < distinguishableCoincidence T
  visibility : ∀ T, 0 ≤ T → T ≤ 1 →
    homVisibility T = 2 * T * (1 - T) / (T ^ 2 + (1 - T) ^ 2) ∧
    (0 ≤ homVisibility T ∧ homVisibility T ≤ 1) ∧
    (homVisibility T = 1 ↔ T = 1 / 2)

theorem photonics_hong_ou_mandel_master_suite : PhotonicsHongOuMandelInterferenceSuite where
  normalized_substitution := fun T =>
    symmetric_square_substitution (PhotonicsBeamSplitterPhaseShift.splitter T)
  unitary := two_photon_unitary
  norm_preservation := two_photon_norm_preserved
  exact_output := hom_output_state_exact
  probabilities := hom_probabilities_exact
  normalization := hom_prob_normalization
  balanced_bunching := hom_balanced_bunching
  phase_bridge := phase_convention_bridge
  probability_bridge := hom_real_convention_probabilities
  distinguishable_normalization := labeled_weight_normalization
  independent_paths := labeled_weight_independence
  distinguishable_baseline := hom_distinguishable_baseline
  visibility := hom_visibility_exact

end PhotonicsHongOuMandelInterference
