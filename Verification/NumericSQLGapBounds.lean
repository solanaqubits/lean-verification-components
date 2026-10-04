/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumStandardQuantumLimit
import Verification.NumericRealRounding
import Verification.NumericRoundingCertificates
import Verification.NumericSQLIntervalBounds

/-!
# Affine enclosures of the scalar SQL optimization gap

This target is A/I + B*I - 2*sqrt(A*B), not sqrt(hbar/(mass*frequency)).
Exact zero is not a midpoint. Rational root witnesses and affine endpoints feed
into the existing real rounding semantics without an exclusion of boundary ties.
Python, JSON, SHA-256, external byte binding, and detector physics are not verified.
Rationalized enclosures and adaptive termination remain separate work.
-/

namespace NumericSQLGapBounds

open NumericRoundingCertificates NumericRealRounding NumericSQLIntervalBounds

noncomputable def sqlNoiseGap (A B I : ℝ) : ℝ :=
  A / I + B * I - 2 * Real.sqrt (A * B)

/-- Affine endpoint reversal needs only root containment, not parameter positivity. -/
theorem sql_gap_affine_enclosure (A B I L U : ℝ)
    (h_bound : L ≤ Real.sqrt (A * B) ∧ Real.sqrt (A * B) ≤ U) :
    A / I + B * I - 2 * U ≤ sqlNoiseGap A B I ∧
    sqlNoiseGap A B I ≤ A / I + B * I - 2 * L := by
  dsimp [sqlNoiseGap]
  constructor <;> linarith [h_bound.1, h_bound.2]

theorem sql_gap_nonneg (A B I : ℝ) (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) :
    0 ≤ sqlNoiseGap A B I :=
  sub_nonneg.mpr (QuantumStandardQuantumLimit.noiseVariance_lower_bound A B I hA hB hI)

/-- Balance characterizes exact zero for positive parameters. -/
theorem sql_gap_zero_iff (A B I : ℝ) (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) :
    sqlNoiseGap A B I = 0 ↔ A = B * I ^ 2 := by
  have hmin := QuantumStandardQuantumLimit.noiseVariance_unique_min A B I hA hB hI
  change (QuantumStandardQuantumLimit.noiseVariance A B I - 2 * Real.sqrt (A * B) = 0) ↔ _
  rw [sub_eq_zero, hmin]
  constructor
  · intro heq
    have hs := Real.sq_sqrt (le_of_lt (div_pos hA hB))
    rw [← heq] at hs
    have hm := (eq_div_iff (ne_of_gt hB)).mp hs
    nlinarith [hm]
  · intro hbalance
    have hdiv : A / B = I ^ 2 := by rw [hbalance]; field_simp
    rw [hdiv, Real.sqrt_sq hI.le]

/-- Exact Zero → Canonical +0, using the existing binary64 encoding. -/
theorem sql_gap_exact_zero_rounding (A B I : ℝ)
    (hA : 0 < A) (hB : 0 < B) (hI : 0 < I) (hbalance : A = B * I ^ 2) :
    realRound binary64 (sqlNoiseGap A B I) = positiveZero := by
  rw [(sql_gap_zero_iff A B I hA hB hI).mpr hbalance]
  simpa using (realRound_ratCast binary64 0).trans binary64_exact_zero

/-- Real endpoint semantics: ties at boundaries are governed by the existing rounding rule. -/
theorem sql_gap_real_bounds_rounding (g : MagnitudeGrid) (A B I lo hi : ℝ)
    (f : FloatRepresentation g) (hlo : lo ≤ sqlNoiseGap A B I)
    (hhi : sqlNoiseGap A B I ≤ hi)
    (hl : realRound g lo = f) (hu : realRound g hi = f) :
    realRound g (sqlNoiseGap A B I) = f :=
  real_interval_rounding_soundness g lo hi _ f hlo hhi hl hu

/-- Executable rational certificates certify the enclosed real gap. -/
theorem sql_gap_rounding_soundness (g : MagnitudeGrid) (A B I : ℝ) (lo hi : ℚ)
    (f : FloatRepresentation g) (hlo : (lo : ℝ) ≤ sqlNoiseGap A B I)
    (hhi : sqlNoiseGap A B I ≤ (hi : ℝ))
    (hc : checkIntervalCertificate g lo hi f = .decided f) :
    realRound g (sqlNoiseGap A B I) = f :=
  interval_certificate_real_sound g lo hi _ f hc hlo hhi

/-- Exact rational parameters give executable affine endpoints. -/
def gapInterval (A B I : ℚ) (R : RatInterval) : RatInterval :=
  ⟨A / I + B * I - 2 * R.hi, A / I + B * I - 2 * R.lo, by linarith [R.h_le]⟩

/-- Square-check input for sqrt(A*B); a point interval preserves the exact product. -/
def productInterval (A B : ℚ) : RatInterval := ⟨A * B, A * B, le_refl _⟩

/-- Root witness acceptance actually derives inclusion of this gap in these endpoints. -/
theorem sql_gap_checked_enclosure (A B I : ℚ) (R : RatInterval)
    (hc : checkSqrtWitness (productInterval A B) R = true) :
    containsReal (gapInterval A B I R) (sqlNoiseGap (A : ℝ) (B : ℝ) (I : ℝ)) := by
  have hp : containsReal (productInterval A B) ((A : ℝ) * (B : ℝ)) := by
    simp [containsReal, productInterval]
  have hr := check_sqrt_witness_sound (productInterval A B) R _ hp hc
  have he := sql_gap_affine_enclosure (A : ℝ) (B : ℝ) (I : ℝ) R.lo R.hi hr
  simpa [containsReal, gapInterval] using he

/-- Fully composed path: checked squares → affine enclosure → real rounding of G. -/
theorem sql_gap_affine_rounding_soundness (g : MagnitudeGrid) (A B I : ℚ)
    (R : RatInterval) (hc : checkSqrtWitness (productInterval A B) R = true)
    (f : FloatRepresentation g)
    (hf : checkIntervalCertificate g (gapInterval A B I R).lo
      (gapInterval A B I R).hi f = .decided f) :
    realRound g (sqlNoiseGap (A : ℝ) (B : ℝ) (I : ℝ)) = f := by
  have he := sql_gap_checked_enclosure A B I R hc
  exact sql_gap_rounding_soundness g _ _ _ _ _ f he.1 he.2 hf

structure NumericSQLGapBoundsSuite : Prop where
  affine : ∀ A B I L U : ℝ, L ≤ Real.sqrt (A * B) ∧ Real.sqrt (A * B) ≤ U →
    A / I + B * I - 2 * U ≤ sqlNoiseGap A B I ∧
    sqlNoiseGap A B I ≤ A / I + B * I - 2 * L
  nonneg : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I → 0 ≤ sqlNoiseGap A B I
  zero_iff : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I →
    (sqlNoiseGap A B I = 0 ↔ A = B * I ^ 2)
  positive_zero : ∀ A B I : ℝ, 0 < A → 0 < B → 0 < I → A = B * I ^ 2 →
    realRound binary64 (sqlNoiseGap A B I) = positiveZero
  rounding : ∀ g : MagnitudeGrid, ∀ A B I : ℚ, ∀ R : RatInterval,
    checkSqrtWitness (productInterval A B) R = true → ∀ f : FloatRepresentation g,
    checkIntervalCertificate g (gapInterval A B I R).lo (gapInterval A B I R).hi f =
      .decided f → realRound g (sqlNoiseGap (A : ℝ) (B : ℝ) (I : ℝ)) = f

theorem numeric_sql_gap_master_suite : NumericSQLGapBoundsSuite := {
  affine := sql_gap_affine_enclosure
  nonneg := sql_gap_nonneg
  zero_iff := sql_gap_zero_iff
  positive_zero := sql_gap_exact_zero_rounding
  rounding := sql_gap_affine_rounding_soundness
}

end NumericSQLGapBounds
