/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.SolarisMithraCore
import Verification.MithraicPhaseCollapse
import Verification.QuantumBeamSplitterTransform
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Tactic.FinCases

/-! A fixed symmetric lossless two-mode convention, with an inverse second splitter.
The affine propagation law is an external premise, not a consequence of Maxwell's equations. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace PhotonicsBeamSplitterPhaseShift

abbrev Vec := Fin 2 → ℂ
abbrev Mat := Matrix (Fin 2) (Fin 2) ℂ

def splitter (T : ℝ) : Mat :=
  ![![(Real.sqrt T : ℂ), Complex.I * (Real.sqrt (1 - T) : ℂ)],
    ![Complex.I * (Real.sqrt (1 - T) : ℂ), (Real.sqrt T : ℂ)]]

def phase (φ : ℝ) : ℂ := Complex.exp (Complex.I * (φ : ℂ))
def phaseShift (φ : ℝ) : Mat := ![![phase φ, 0], ![0, 1]]
def mzi (T φ : ℝ) : Mat := (splitter T).conjTranspose * phaseShift φ * splitter T

/-- Squared Hermitian (Euclidean) norm, not the function space's supremum norm. -/
def normSquared (v : Vec) : ℝ := Complex.normSq (v 0) + Complex.normSq (v 1)
def input : Vec := ![1, 0]
def output (T φ : ℝ) : Vec := (mzi T φ).mulVec input
def probability (T φ : ℝ) (j : Fin 2) : ℝ := Complex.normSq (output T φ j)
def intensity (I₀ T φ : ℝ) (j : Fin 2) : ℝ := I₀ * probability T φ j

@[simp] theorem phase_re (φ : ℝ) : (phase φ).re = Real.cos φ := by
  simpa only [phase, mul_comm Complex.I] using Complex.exp_ofReal_mul_I_re φ
@[simp] theorem phase_im (φ : ℝ) : (phase φ).im = Real.sin φ := by
  simpa only [phase, mul_comm Complex.I] using Complex.exp_ofReal_mul_I_im φ

@[simp] theorem phase_normSq (φ : ℝ) : Complex.normSq (phase φ) = 1 := by
  simp only [Complex.normSq_apply, phase_re, phase_im]
  nlinarith [Real.sin_sq_add_cos_sq φ]

theorem splitter_unitary (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (splitter T).conjTranspose * splitter T = 1 ∧
      splitter T * (splitter T).conjTranspose = 1 := by
  have ht := Real.sq_sqrt hT
  have hr := Real.sq_sqrt (by linarith : 0 ≤ 1 - T)
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp [splitter, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem phaseShift_unitary (φ : ℝ) :
    (phaseShift φ).conjTranspose * phaseShift φ = 1 ∧
      phaseShift φ * (phaseShift φ).conjTranspose = 1 := by
  have h := Real.sin_sq_add_cos_sq φ
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp [phaseShift, Complex.mul_re, Complex.mul_im] <;> nlinarith

theorem splitter_norm_preserved (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : Vec) :
    normSquared ((splitter T).mulVec v) = normSquared v := by
  have ht := Real.sq_sqrt hT
  have hr := Real.sq_sqrt (by linarith : 0 ≤ 1 - T)
  simp [normSquared, splitter, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg (v 0).re, sq_nonneg (v 0).im, sq_nonneg (v 1).re, sq_nonneg (v 1).im]

theorem mzi_unitary (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (mzi T φ).conjTranspose * mzi T φ = 1 ∧ mzi T φ * (mzi T φ).conjTranspose = 1 := by
  obtain ⟨h₁, h₂⟩ := splitter_unitary T hT hT1
  obtain ⟨h₃, h₄⟩ := phaseShift_unitary φ
  constructor
  · calc
      _ = (splitter T).conjTranspose * (phaseShift φ).conjTranspose *
          (splitter T * (splitter T).conjTranspose) * phaseShift φ * splitter T := by
        simp only [mzi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by
        rw [h₂, Matrix.mul_one]
        rw [Matrix.mul_assoc (splitter T).conjTranspose, h₃, Matrix.mul_one, h₁]
  · calc
      _ = (splitter T).conjTranspose * phaseShift φ *
          (splitter T * (splitter T).conjTranspose) *
            (phaseShift φ).conjTranspose * splitter T := by
        simp only [mzi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mul_assoc]
      _ = 1 := by
        rw [h₂, Matrix.mul_one]
        rw [Matrix.mul_assoc (splitter T).conjTranspose, h₄, Matrix.mul_one, h₁]

theorem inverse_splitter_norm_preserved (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (v : Vec) : normSquared ((splitter T).conjTranspose.mulVec v) = normSquared v := by
  have h := splitter_norm_preserved T hT hT1 ((splitter T).conjTranspose.mulVec v)
  rw [Matrix.mulVec_mulVec, (splitter_unitary T hT hT1).2, Matrix.one_mulVec] at h
  exact h.symm

theorem phaseShift_norm_preserved (φ : ℝ) (v : Vec) :
    normSquared ((phaseShift φ).mulVec v) = normSquared v := by
  simp [normSquared, phaseShift, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
    Complex.normSq_mul]

theorem mzi_norm_preserved (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : Vec) :
    normSquared ((mzi T φ).mulVec v) = normSquared v := by
  simp only [mzi, ← Matrix.mulVec_mulVec]
  rw [inverse_splitter_norm_preserved T hT hT1, phaseShift_norm_preserved,
    splitter_norm_preserved T hT hT1]

theorem mzi_output_amplitudes (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    output T φ 0 = (T : ℂ) * phase φ + (1 - (T : ℂ)) ∧
    output T φ 1 = Complex.I * (Real.sqrt T : ℂ) * (Real.sqrt (1 - T) : ℂ) *
      (1 - phase φ) := by
  have ht := Real.sq_sqrt hT
  have hr := Real.sq_sqrt (by linarith : 0 ≤ 1 - T)
  have htc := congrArg (fun x => x * Real.cos φ) ht
  have hts := congrArg (fun x => x * Real.sin φ) ht
  constructor <;>
    simp only [output, mzi, Matrix.mulVec, dotProduct, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
    apply Complex.ext <;> simp [splitter, phaseShift, input, Complex.mul_re, Complex.mul_im] <;>
    nlinarith

theorem mzi_total_probability (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    probability T φ 0 + probability T φ 1 = 1 := by
  have h := mzi_norm_preserved T φ hT hT1 input
  simpa [normSquared, probability, output, input] using h

theorem mzi_probabilities_exact (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    probability T φ 0 = 1 - 4 * T * (1 - T) * (Real.sin (φ / 2)) ^ 2 ∧
    probability T φ 1 = 4 * T * (1 - T) * (Real.sin (φ / 2)) ^ 2 := by
  have hc : 1 - Real.cos φ = 2 * Real.sin (φ / 2) ^ 2 := by
    have h := Real.cos_two_mul (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]
  have hp : probability T φ 1 = 4 * T * (1 - T) * (Real.sin (φ / 2)) ^ 2 := by
    rw [probability, (mzi_output_amplitudes T φ hT hT1).2]
    simp only [Complex.normSq_mul]
    have he : (1 - Real.cos φ) * (1 - Real.cos φ) + Real.sin φ * Real.sin φ =
        4 * Real.sin (φ / 2) ^ 2 := by
      nlinarith [Real.sin_sq_add_cos_sq φ]
    simp [Complex.normSq_apply, Real.mul_self_sqrt hT,
      Real.mul_self_sqrt (by linarith : 0 ≤ 1 - T), he]
    ring
  exact ⟨by linarith [mzi_total_probability T φ hT hT1], hp⟩

theorem probability_nonneg (T φ : ℝ) (j : Fin 2) : 0 ≤ probability T φ j :=
  Complex.normSq_nonneg _

theorem mzi_probability_periodic (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : Fin 2) :
    probability T (φ + 2 * Real.pi) j = probability T φ j := by
  have hs : Real.sin ((φ + 2 * Real.pi) / 2) ^ 2 = Real.sin (φ / 2) ^ 2 := by
    rw [show (φ + 2 * Real.pi) / 2 = φ / 2 + Real.pi by ring, Real.sin_add_pi]
    ring
  fin_cases j <;> dsimp only
  · change probability T (φ + 2 * Real.pi) 0 = probability T φ 0
    rw [(mzi_probabilities_exact T (φ + 2 * Real.pi) hT hT1).1,
      (mzi_probabilities_exact T φ hT hT1).1, hs]
  · change probability T (φ + 2 * Real.pi) 1 = probability T φ 1
    rw [(mzi_probabilities_exact T (φ + 2 * Real.pi) hT hT1).2,
      (mzi_probabilities_exact T φ hT hT1).2, hs]

theorem mzi_endpoint_probabilities (φ : ℝ) :
    probability 0 φ 0 = 1 ∧ probability 0 φ 1 = 0 ∧
    probability 1 φ 0 = 1 ∧ probability 1 φ 1 = 0 := by
  have h₀ := mzi_probabilities_exact 0 φ (by norm_num) (by norm_num)
  have h₁ := mzi_probabilities_exact 1 φ (by norm_num) (by norm_num)
  norm_num at h₀ h₁
  exact ⟨h₀.1, h₀.2, h₁⟩

theorem mzi_prob_properties (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∀ j, 0 ≤ probability T φ j ∧ probability T φ j ≤ 1) ∧
    probability T φ 0 + probability T φ 1 = 1 ∧
    (∀ j, probability T (φ + 2 * Real.pi) j = probability T φ j) := by
  refine ⟨?_, mzi_total_probability T φ hT hT1, mzi_probability_periodic T φ hT hT1⟩
  intro j
  refine ⟨probability_nonneg T φ j, ?_⟩
  have h := mzi_total_probability T φ hT hT1
  have h₀ := probability_nonneg T φ 0
  have h₁ := probability_nonneg T φ 1
  fin_cases j
  · change probability T φ 0 ≤ 1
    linarith
  · change probability T φ 1 ≤ 1
    linarith

theorem mzi_balanced_probabilities (φ : ℝ) :
    probability (1 / 2) φ 0 = Real.cos (φ / 2) ^ 2 ∧
    probability (1 / 2) φ 1 = Real.sin (φ / 2) ^ 2 := by
  obtain ⟨h₀, h₁⟩ := mzi_probabilities_exact (1 / 2) φ (by norm_num) (by norm_num)
  constructor <;> nlinarith [Real.sin_sq_add_cos_sq (φ / 2)]

theorem mzi_balanced_bridge_to_solaris (I₀ φ : ℝ) (hI : 0 ≤ I₀) :
    intensity I₀ (1 / 2) φ 0 = SolarisMithraCore.constructive_intensity ⟨I₀, φ⟩ ∧
    intensity I₀ (1 / 2) φ 1 = SolarisMithraCore.destructive_intensity ⟨I₀, φ⟩ ∧
    intensity I₀ (1 / 2) φ 0 + intensity I₀ (1 / 2) φ 1 = I₀ ∧
    (∀ j, 0 ≤ intensity I₀ (1 / 2) φ j) := by
  obtain ⟨h₀, h₁⟩ := mzi_balanced_probabilities φ
  refine ⟨?_, ?_, ?_, fun j => mul_nonneg hI (probability_nonneg _ _ j)⟩
  · exact congrArg (I₀ * ·) h₀
  · exact congrArg (I₀ * ·) h₁
  · simp only [intensity, ← mul_add, mzi_total_probability (1 / 2) φ (by norm_num) (by norm_num),
      mul_one]

theorem mzi_intensity_extrema (I₀ T : ℝ) (hI : 0 < I₀) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∀ φ, I₀ * (2 * T - 1) ^ 2 ≤ intensity I₀ T φ 0 ∧ intensity I₀ T φ 0 ≤ I₀) ∧
    intensity I₀ T 0 0 = I₀ ∧ intensity I₀ T Real.pi 0 = I₀ * (2 * T - 1) ^ 2 := by
  have ha : 0 ≤ 4 * T * (1 - T) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · intro φ
    have hs : Real.sin (φ / 2) ^ 2 ≤ 1 := by
      nlinarith [Real.sin_sq_add_cos_sq (φ / 2), sq_nonneg (Real.cos (φ / 2))]
    have hp := (mzi_probabilities_exact T φ hT hT1).1
    have hl := mul_le_mul_of_nonneg_left hs ha
    have hu := mul_nonneg ha (sq_nonneg (Real.sin (φ / 2)))
    have hlo : (2 * T - 1) ^ 2 ≤ probability T φ 0 := by nlinarith
    have hhi : probability T φ 0 ≤ 1 := by linarith
    exact ⟨mul_le_mul_of_nonneg_left hlo hI.le,
      by simpa [intensity] using mul_le_mul_of_nonneg_left hhi hI.le⟩
  · simp [intensity, (mzi_probabilities_exact T 0 hT hT1).1]
  · rw [intensity, (mzi_probabilities_exact T Real.pi hT hT1).1]
    simp only [Real.sin_pi_div_two, one_pow, mul_one]
    ring

/-- The extrema are certified bounds with attainable phases, not arbitrary labels. -/
def visibilityPattern (I₀ T : ℝ) (hI : 0 < I₀) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    MithraicPhaseCollapse.InterferencePattern where
  i_max := I₀
  i_min := I₀ * (2 * T - 1) ^ 2
  h_min_nonneg := mul_nonneg hI.le (sq_nonneg _)
  h_ordered := by
    have h := (mzi_intensity_extrema I₀ T hI hT hT1).1 Real.pi
    rw [(mzi_intensity_extrema I₀ T hI hT hT1).2.2] at h
    exact h.2
  h_pos := by positivity

theorem mzi_visibility_pattern_bridge (I₀ T : ℝ) (hI : 0 < I₀)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    MithraicPhaseCollapse.visibility (visibilityPattern I₀ T hI hT hT1) =
      (1 - (2 * T - 1) ^ 2) / (1 + (2 * T - 1) ^ 2) ∧
    MithraicPhaseCollapse.visibility (visibilityPattern I₀ T hI hT hT1) =
      4 * T * (1 - T) / (1 + (2 * T - 1) ^ 2) := by
  have hd : 1 + (2 * T - 1) ^ 2 ≠ 0 := by positivity
  have hp : I₀ + I₀ * (2 * T - 1) ^ 2 ≠ 0 := by positivity
  constructor <;> simp only [MithraicPhaseCollapse.visibility, visibilityPattern] <;>
    field_simp; ring

theorem mzi_balanced_visibility (I₀ : ℝ) (hI : 0 < I₀) :
    MithraicPhaseCollapse.visibility
      (visibilityPattern I₀ (1 / 2) hI (by norm_num) (by norm_num)) = 1 := by
  rw [(mzi_visibility_pattern_bridge I₀ (1 / 2) hI (by norm_num) (by norm_num)).1]
  norm_num

/-- A constant phase offset changes attainment points but leaves both extrema unchanged. -/
theorem mzi_static_phase_extrema (I₀ T offset : ℝ) (hI : 0 < I₀)
    (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (∀ φ, I₀ * (2 * T - 1) ^ 2 ≤ intensity I₀ T (φ + offset) 0 ∧
      intensity I₀ T (φ + offset) 0 ≤ I₀) ∧
    intensity I₀ T (-offset + offset) 0 = I₀ ∧
    intensity I₀ T ((Real.pi - offset) + offset) 0 = I₀ * (2 * T - 1) ^ 2 := by
  obtain ⟨hb, hmax, hmin⟩ := mzi_intensity_extrema I₀ T hI hT hT1
  exact ⟨fun φ => hb (φ + offset), by simpa using hmax, by simpa using hmin⟩

theorem mzi_phase_geometric_affine (I₀ T φ κ ΔL φ₀ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hphase : φ = κ * ΔL + φ₀) :
    intensity I₀ T φ 0 = I₀ * (1 - 4 * T * (1 - T) *
      Real.sin ((κ * ΔL + φ₀) / 2) ^ 2) ∧
    intensity I₀ T φ 1 = I₀ * (4 * T * (1 - T) *
      Real.sin ((κ * ΔL + φ₀) / 2) ^ 2) := by
  subst φ
  exact ⟨congrArg (I₀ * ·) (mzi_probabilities_exact T _ hT hT1).1,
    congrArg (I₀ * ·) (mzi_probabilities_exact T _ hT hT1).2⟩

/-- The chosen reflection factor is the unit phase at π/2. -/
theorem reflection_phase_convention : phase (Real.pi / 2) = Complex.I := by
  apply Complex.ext <;> simp

theorem splitter_reflection_entry (T : ℝ) :
    splitter T 0 1 = phase (Real.pi / 2) * (Real.sqrt (1 - T) : ℂ) := by
  rw [reflection_phase_convention]
  rfl

def euclideanNorm (v : Vec) : ℝ := Real.sqrt (normSquared v)

theorem splitter_euclidean_norm (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : Vec) :
    euclideanNorm ((splitter T).mulVec v) = euclideanNorm v :=
  congrArg Real.sqrt (splitter_norm_preserved T hT hT1 v)

theorem mzi_euclidean_norm (T φ : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (v : Vec) :
    euclideanNorm ((mzi T φ).mulVec v) = euclideanNorm v :=
  congrArg Real.sqrt (mzi_norm_preserved T φ hT hT1 v)

structure PhotonicsBeamSplitterPhaseShiftSuite : Prop where
  splitter_unitarity : ∀ T, 0 ≤ T → T ≤ 1 →
    (splitter T).conjTranspose * splitter T = 1 ∧
    splitter T * (splitter T).conjTranspose = 1
  circuit_unitarity : ∀ T φ, 0 ≤ T → T ≤ 1 →
    (mzi T φ).conjTranspose * mzi T φ = 1 ∧ mzi T φ * (mzi T φ).conjTranspose = 1
  norm_preservation : ∀ T φ, 0 ≤ T → T ≤ 1 → ∀ v,
    euclideanNorm ((mzi T φ).mulVec v) = euclideanNorm v
  reflection_phase : phase (Real.pi / 2) = Complex.I
  probabilities : ∀ T φ, 0 ≤ T → T ≤ 1 →
    probability T φ 0 = 1 - 4 * T * (1 - T) * Real.sin (φ / 2) ^ 2 ∧
    probability T φ 1 = 4 * T * (1 - T) * Real.sin (φ / 2) ^ 2
  probability_laws : ∀ T φ, 0 ≤ T → T ≤ 1 →
    (∀ j, 0 ≤ probability T φ j ∧ probability T φ j ≤ 1) ∧
    probability T φ 0 + probability T φ 1 = 1 ∧
    (∀ j, probability T (φ + 2 * Real.pi) j = probability T φ j)
  solaris_bridge : ∀ I₀ φ, 0 ≤ I₀ →
    intensity I₀ (1 / 2) φ 0 = SolarisMithraCore.constructive_intensity ⟨I₀, φ⟩ ∧
    intensity I₀ (1 / 2) φ 1 = SolarisMithraCore.destructive_intensity ⟨I₀, φ⟩ ∧
    intensity I₀ (1 / 2) φ 0 + intensity I₀ (1 / 2) φ 1 = I₀ ∧
    (∀ j, 0 ≤ intensity I₀ (1 / 2) φ j)
  extrema : ∀ I₀ T, 0 < I₀ → 0 ≤ T → T ≤ 1 →
    (∀ φ, I₀ * (2 * T - 1) ^ 2 ≤ intensity I₀ T φ 0 ∧ intensity I₀ T φ 0 ≤ I₀) ∧
    intensity I₀ T 0 0 = I₀ ∧ intensity I₀ T Real.pi 0 = I₀ * (2 * T - 1) ^ 2
  contrast : ∀ I₀ T (hI : 0 < I₀) (hT : 0 ≤ T) (hT1 : T ≤ 1),
    MithraicPhaseCollapse.visibility (visibilityPattern I₀ T hI hT hT1) =
      (1 - (2 * T - 1) ^ 2) / (1 + (2 * T - 1) ^ 2) ∧
    MithraicPhaseCollapse.visibility (visibilityPattern I₀ T hI hT hT1) =
      4 * T * (1 - T) / (1 + (2 * T - 1) ^ 2)
  geometric_phase : ∀ I₀ T φ κ ΔL φ₀, 0 ≤ T → T ≤ 1 → φ = κ * ΔL + φ₀ →
    intensity I₀ T φ 0 = I₀ * (1 - 4 * T * (1 - T) *
      Real.sin ((κ * ΔL + φ₀) / 2) ^ 2) ∧
    intensity I₀ T φ 1 = I₀ * (4 * T * (1 - T) * Real.sin ((κ * ΔL + φ₀) / 2) ^ 2)

theorem photonics_beam_splitter_phase_shift_master_suite :
    PhotonicsBeamSplitterPhaseShiftSuite where
  splitter_unitarity := splitter_unitary
  circuit_unitarity := mzi_unitary
  norm_preservation := mzi_euclidean_norm
  reflection_phase := reflection_phase_convention
  probabilities := mzi_probabilities_exact
  probability_laws := mzi_prob_properties
  solaris_bridge := mzi_balanced_bridge_to_solaris
  extrema := mzi_intensity_extrema
  contrast := mzi_visibility_pattern_bridge
  geometric_phase := mzi_phase_geometric_affine

end PhotonicsBeamSplitterPhaseShift
