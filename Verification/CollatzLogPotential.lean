import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Verification.CollatzGeometricDrift

set_option linter.style.header false

namespace CollatzLogPotential

open CollatzGeometricDrift

/-- Positivity of the natural power of three, viewed in the reals. -/
theorem rpow3_pos : 0 < (3 : ℝ) ^ 30 := by positivity

/-- Positivity of the natural power of two, viewed in the reals. -/
theorem rpow2_pos : 0 < (2 : ℝ) ^ 49 := by positivity

/-- Transfer the verified integer comparison to real logarithms. -/
theorem log_pow30_three_lt_log_pow49_two :
    Real.log ((3 : ℝ) ^ 30) < Real.log ((2 : ℝ) ^ 49) := by
  have h_nat := collatz_tree32_integer_drift_strict_contraction
  have h_real : (3 : ℝ) ^ 30 < (2 : ℝ) ^ 49 := by exact_mod_cast h_nat
  exact Real.log_lt_log rpow3_pos h_real

/-- Expand the logarithm of the thirtieth power of three. -/
theorem log_pow30_eq : Real.log ((3 : ℝ) ^ 30) = 30 * Real.log 3 := by
  exact Real.log_pow 3 30

/-- Expand the logarithm of the forty-ninth power of two. -/
theorem log_pow49_eq : Real.log ((2 : ℝ) ^ 49) = 49 * Real.log 2 := by
  exact Real.log_pow 2 49

/-- The scaled logarithmic gap for the selected leading coefficients is negative. -/
theorem log_drift_gap_negative :
    30 * Real.log 3 - 49 * Real.log 2 < 0 := by
  have h_lt := log_pow30_three_lt_log_pow49_two
  rw [log_pow30_eq, log_pow49_eq] at h_lt
  linarith

/-- Normalize the gap by the common denominator of the specified branch weights. -/
theorem expected_log_drift_tree32_eq :
    (15 / 8 : ℝ) * Real.log 3 - (49 / 16 : ℝ) * Real.log 2 =
      (1 / 16 : ℝ) * (30 * Real.log 3 - 49 * Real.log 2) := by
  ring

/-- The weighted logarithmic leading term is negative.
This does not include additive corrections or normalize by branch durations.
-/
theorem expected_log_drift_tree32_negative :
    (15 / 8 : ℝ) * Real.log 3 - (49 / 16 : ℝ) * Real.log 2 < 0 := by
  rw [expected_log_drift_tree32_eq]
  exact mul_neg_of_pos_of_neg (by norm_num) log_drift_gap_negative

#print axioms log_pow30_three_lt_log_pow49_two
#print axioms log_drift_gap_negative
#print axioms expected_log_drift_tree32_negative

end CollatzLogPotential
