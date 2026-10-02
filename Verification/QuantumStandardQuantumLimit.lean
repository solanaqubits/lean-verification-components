/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Conditional scalar measurement-noise optimization

The variance is prescribed as A / I + B * I with positive parameters. Omitting
noise cross correlations is a modeling choice, not a derived quantum statement.
The SQL-shaped bound below assumes its calibration inequality explicitly; no
commutator, stochastic process, spectral density, or physical detector is modeled.
-/
namespace QuantumStandardQuantumLimit

noncomputable section

/-- Prescribed sum of an inverse-power contribution and a linear contribution. -/
def noiseVariance (A B I : ℝ) : ℝ := A / I + B * I

/-- Exact nonnegative remainder above the candidate minimum. -/
theorem noiseVariance_gap_identity (A B I : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) :
    noiseVariance A B I - 2 * Real.sqrt (A * B) =
      (Real.sqrt A - I * Real.sqrt B) ^ 2 / I := by
  have hexpand : (Real.sqrt A - I * Real.sqrt B) ^ 2 =
      A - 2 * I * (Real.sqrt A * Real.sqrt B) + B * I ^ 2 := by
    ring_nf
    rw [Real.sq_sqrt hA.le, Real.sq_sqrt hB.le]
    ring
  rw [hexpand, Real.sqrt_mul hA.le B]
  dsimp [noiseVariance]
  field_simp
  ring

/-- The minimum is a nonstrict lower bound; equality is attained. -/
theorem noiseVariance_lower_bound (A B I : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) :
    2 * Real.sqrt (A * B) ≤ noiseVariance A B I := by
  have hgap := noiseVariance_gap_identity A B I hA hB hI
  have hnonneg := div_nonneg (sq_nonneg (Real.sqrt A - I * Real.sqrt B)) hI.le
  linarith

theorem optimum_intensity_pos (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < Real.sqrt (A / B) := Real.sqrt_pos.mpr (div_pos hA hB)

/-- Both positive noise contributions coincide at the positive optimum. -/
theorem noiseVariance_balance_at_optimum (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    A / Real.sqrt (A / B) = B * Real.sqrt (A / B) := by
  have hsq := Real.sq_sqrt (le_of_lt (div_pos hA hB))
  have hmul := (eq_div_iff (ne_of_gt hB)).mp hsq
  apply (div_eq_iff (ne_of_gt (optimum_intensity_pos A B hA hB))).mpr
  nlinarith [hmul]

/-- The lower bound is attained at sqrt(A/B). -/
theorem noiseVariance_optimum_value (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    noiseVariance A B (Real.sqrt (A / B)) = 2 * Real.sqrt (A * B) := by
  have hgap := noiseVariance_gap_identity A B (Real.sqrt (A / B)) hA hB
    (optimum_intensity_pos A B hA hB)
  have hzero : Real.sqrt A - Real.sqrt (A / B) * Real.sqrt B = 0 := by
    rw [Real.sqrt_div hA.le B, div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr hB)), sub_self]
  rw [hzero, zero_pow (by decide : 2 ≠ 0), zero_div] at hgap
  linarith

/-- The positive optimum is unique. -/
theorem noiseVariance_unique_min (A B I : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) :
    noiseVariance A B I = 2 * Real.sqrt (A * B) ↔ I = Real.sqrt (A / B) := by
  constructor
  · intro hmin
    have hgap := noiseVariance_gap_identity A B I hA hB hI
    have hsquare : (Real.sqrt A - I * Real.sqrt B) ^ 2 = 0 := by
      have hdiv : (Real.sqrt A - I * Real.sqrt B) ^ 2 / I = 0 := by linarith
      exact (div_eq_zero_iff.mp hdiv).resolve_right (ne_of_gt hI)
    have hzero : Real.sqrt A - I * Real.sqrt B = 0 := sq_eq_zero_iff.mp hsquare
    rw [Real.sqrt_div hA.le B]
    apply (eq_div_iff (ne_of_gt (Real.sqrt_pos.mpr hB))).mpr
    exact (sub_eq_zero.mp hzero).symm
  · intro hIopt
    rw [hIopt]
    exact noiseVariance_optimum_value A B hA hB

/-- Away from the unique positive optimizer the bound is strict. -/
theorem noiseVariance_strict_away (A B I : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) (hne : I ≠ Real.sqrt (A / B)) :
    2 * Real.sqrt (A * B) < noiseVariance A B I := by
  apply lt_of_le_of_ne (noiseVariance_lower_bound A B I hA hB hI)
  intro heq
  exact hne ((noiseVariance_unique_min A B I hA hB hI).mp heq.symm)

/-- Conditional calibration bound; the calibration is not derived from quantum mechanics. -/
theorem sql_variance_bound (A B I hbar m omega_m : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I)
    (hhbar : 0 < hbar) (hm : 0 < m) (homega : 0 < omega_m)
    (hcal : (hbar / (2 * m * omega_m)) ^ 2 ≤ A * B) :
    hbar / (m * omega_m) ≤ noiseVariance A B I := by
  have hroot := Real.sq_sqrt (le_of_lt (mul_pos hA hB))
  have hroot_nonneg := Real.sqrt_nonneg (A * B)
  have hcal_nonneg : 0 ≤ hbar / (2 * m * omega_m) := by positivity
  have hhalf : hbar / (2 * m * omega_m) ≤ Real.sqrt (A * B) := by nlinarith
  have hscale : hbar / (m * omega_m) = 2 * (hbar / (2 * m * omega_m)) := by
    field_simp
  rw [hscale]
  exact le_trans (mul_le_mul_of_nonneg_left hhalf (by norm_num))
    (noiseVariance_lower_bound A B I hA hB hI)

/-- Monotonicity of sqrt transports the calibrated variance bound to standard deviation. -/
theorem sql_standard_deviation_bound (A B I hbar m omega_m : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I)
    (hhbar : 0 < hbar) (hm : 0 < m) (homega : 0 < omega_m)
    (hcal : (hbar / (2 * m * omega_m)) ^ 2 ≤ A * B) :
    Real.sqrt (hbar / (m * omega_m)) ≤ Real.sqrt (noiseVariance A B I) :=
  Real.sqrt_le_sqrt (sql_variance_bound A B I hbar m omega_m hA hB hI hhbar hm homega hcal)

structure QuantumSQLFormalSuite : Prop where
  h_gap : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I →
    noiseVariance A B I - 2 * Real.sqrt (A * B) =
      (Real.sqrt A - I * Real.sqrt B) ^ 2 / I
  h_lower : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I →
    2 * Real.sqrt (A * B) ≤ noiseVariance A B I
  h_optimum : ∀ A B : ℝ, 0 < A → 0 < B →
    noiseVariance A B (Real.sqrt (A / B)) = 2 * Real.sqrt (A * B)
  h_balance : ∀ A B : ℝ, 0 < A → 0 < B →
    A / Real.sqrt (A / B) = B * Real.sqrt (A / B)
  h_unique : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I →
    (noiseVariance A B I = 2 * Real.sqrt (A * B) ↔ I = Real.sqrt (A / B))
  h_variance : ∀ A B I hbar m omega_m : ℝ,
    0 < A → 0 < B → 0 < I → 0 < hbar → 0 < m → 0 < omega_m →
    (hbar / (2 * m * omega_m)) ^ 2 ≤ A * B →
    hbar / (m * omega_m) ≤ noiseVariance A B I
  h_deviation : ∀ A B I hbar m omega_m : ℝ,
    0 < A → 0 < B → 0 < I → 0 < hbar → 0 < m → 0 < omega_m →
    (hbar / (2 * m * omega_m)) ^ 2 ≤ A * B →
    Real.sqrt (hbar / (m * omega_m)) ≤ Real.sqrt (noiseVariance A B I)

theorem quantum_sql_master_suite : QuantumSQLFormalSuite := {
  h_gap := noiseVariance_gap_identity
  h_lower := noiseVariance_lower_bound
  h_optimum := noiseVariance_optimum_value
  h_balance := noiseVariance_balance_at_optimum
  h_unique := noiseVariance_unique_min
  h_variance := sql_variance_bound
  h_deviation := sql_standard_deviation_bound
}

end

end QuantumStandardQuantumLimit
