import Verification.CollatzLogPotential
import Verification.CollatzRemainderBound
import Verification.CollatzBranchSeven

set_option linter.style.header false

namespace CollatzEffectiveDrift

open CollatzBase CollatzAttractor CollatzBranchSeven CollatzLogPotential CollatzRemainderBound

/-- Ratio of integer powers viewed in the reals. -/
noncomputable def drift_ratio_real : ℝ := ((2 : ℝ) ^ 49) / ((3 : ℝ) ^ 30)

theorem drift_ratio_pos : 0 < drift_ratio_real := by
  unfold drift_ratio_real
  positivity

/-- Algebraic lower bound on the logarithmic gap. -/
theorem log_drift_gap_algebraic_lower_bound :
    (1 - ((3 : ℝ) ^ 30) / ((2 : ℝ) ^ 49)) ≤ 49 * Real.log 2 - 30 * Real.log 3 := by
  have h := Real.one_sub_inv_le_log_of_pos drift_ratio_pos
  have hi : drift_ratio_real⁻¹ = ((3 : ℝ) ^ 30) / ((2 : ℝ) ^ 49) := by
    simp only [drift_ratio_real, inv_div]
  have hl : Real.log drift_ratio_real = 49 * Real.log 2 - 30 * Real.log 3 := by
    unfold drift_ratio_real
    rw [Real.log_div (by positivity) (by positivity), log_pow49_eq, log_pow30_eq]
  rwa [hi, hl] at h

/-- Strict rational margin at the sufficient threshold thirteen. -/
theorem rational_drift_threshold_thirteen_strict :
    (640 / 1053 : ℚ) < (((2 : ℚ) ^ 49 - (3 : ℚ) ^ 30) / ((2 : ℚ) ^ 49)) := by
  norm_num

/-- Non-strict version of the threshold comparison. -/
theorem rational_drift_threshold_thirteen :
    (640 / 1053 : ℚ) ≤ (((2 : ℚ) ^ 49 - (3 : ℚ) ^ 30) / ((2 : ℚ) ^ 49)) :=
  le_of_lt rational_drift_threshold_thirteen_strict

/-- The leading logarithmic term plus its linear remainder bound is negative.
This is a scalar inequality, not yet a drift theorem for a transition kernel.
-/
theorem effective_drift_strictly_negative (n : ℕ) (hn : 13 ≤ n) :
    ((15 / 8 : ℝ) * Real.log 3 - (49 / 16 : ℝ) * Real.log 2) +
    ((expected_remainder : ℝ) * (1 / (n : ℝ))) < 0 := by
  have hr : (expected_remainder : ℝ) = 40 / 81 := by
    rw [expected_remainder_eq]
    norm_num
  rw [hr]
  have hn_real : (13 : ℝ) ≤ n := by exact_mod_cast hn
  have hn_pos : (0 : ℝ) < n := by linarith
  have hi : (1 / (n : ℝ)) ≤ 1 / 13 := by
    apply (div_le_iff₀ hn_pos).2
    linarith
  have hp : (40 / 81 : ℝ) * (1 / (n : ℝ)) ≤ 40 / 1053 := by nlinarith
  have hrat : (640 / 1053 : ℝ) < 1 - (3 : ℝ)^30 / (2 : ℝ)^49 := by
    norm_num
  have hg := log_drift_gap_algebraic_lower_bound
  linarith

/-- Nine reaches five after fourteen steps. -/
theorem collatzIter_nine_reaches_five : collatzIter 14 9 = 5 := by decide

theorem collatz_nine_reaches_one : ∃ m : ℕ, collatzIter m 9 = 1 := by
  apply collatz_reaches_one_if_enters_compact 9 14
  · rw [collatzIter_nine_reaches_five]
    omega
  · rw [collatzIter_nine_reaches_five]

/-- Eleven reaches five after nine steps, rather than fourteen. -/
theorem collatzIter_eleven_reaches_five : collatzIter 9 11 = 5 := by decide

theorem collatz_eleven_reaches_one : ∃ m : ℕ, collatzIter m 11 = 1 := by
  apply collatz_reaches_one_if_enters_compact 11 9
  · rw [collatzIter_eleven_reaches_five]
    omega
  · rw [collatzIter_eleven_reaches_five]

/-- Every positive natural number below thirteen eventually reaches one. -/
theorem collatz_finite_prefix_to_one (n : ℕ) (h_pos : 1 ≤ n) (h_le : n ≤ 12) :
    ∃ m : ℕ, collatzIter m n = 1 := by
  interval_cases n
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨5, rfl⟩
  · exact ⟨8, rfl⟩
  · exact collatz_seven_reaches_one
  · exact ⟨3, rfl⟩
  · exact collatz_nine_reaches_one
  · exact ⟨6, rfl⟩
  · exact collatz_eleven_reaches_one
  · exact ⟨9, rfl⟩

#print axioms log_drift_gap_algebraic_lower_bound
#print axioms effective_drift_strictly_negative
#print axioms collatz_finite_prefix_to_one

end CollatzEffectiveDrift
