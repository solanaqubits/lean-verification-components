import Mathlib.Tactic.Linarith
import Verification.CollatzGeometricDrift

set_option linter.style.header false

namespace CollatzRemainderBound

/-- Relative additive coefficient for branch 1. -/
def rem_b1 : ℚ := 1 / 3

/-- Relative additive coefficient for branch 5. -/
def rem_b5 : ℚ := 1 / 3

/-- Relative additive coefficient for branch 3. -/
def rem_b3 : ℚ := 5 / 9

/-- Relative additive coefficient for branch 7. -/
def rem_b7 : ℚ := 19 / 27

/-- Relative additive coefficient for branch 15. -/
def rem_b15 : ℚ := 65 / 81

/-- Relative additive coefficient for branch 31. -/
def rem_b31 : ℚ := 65 / 81

/-- Weighted remainder under the specified six rational weights. -/
def expected_remainder : ℚ :=
  (1 / 4 : ℚ) * rem_b1 +
  (1 / 4 : ℚ) * rem_b5 +
  (1 / 4 : ℚ) * rem_b3 +
  (1 / 8 : ℚ) * rem_b7 +
  (1 / 16 : ℚ) * rem_b15 +
  (1 / 16 : ℚ) * rem_b31

/-- Exact weighted sum of the relative additive coefficients. -/
theorem expected_remainder_eq : expected_remainder = 40 / 81 := by
  norm_num [expected_remainder, rem_b1, rem_b5, rem_b3, rem_b7, rem_b15, rem_b31]

/-- Every relative additive coefficient is strictly below one. -/
theorem remainder_uniform_lt_one :
    rem_b1 < 1 ∧ rem_b5 < 1 ∧ rem_b3 < 1 ∧
    rem_b7 < 1 ∧ rem_b15 < 1 ∧ rem_b31 < 1 := by
  norm_num [rem_b1, rem_b5, rem_b3, rem_b7, rem_b15, rem_b31]

/-- The weighted linear perturbation is at most eight eighty-firsts for inputs at least five. -/
theorem expected_perturbation_bound_at_five (n : ℕ) (hn : 5 ≤ n) :
    expected_remainder * (1 / (n : ℚ)) ≤ 8 / 81 := by
  rw [expected_remainder_eq]
  have hn_q : (5 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  have hn_pos : (0 : ℚ) < n := by linarith
  have h_inv : (1 / (n : ℚ)) ≤ 1 / 5 := by
    apply (div_le_iff₀ hn_pos).2
    linarith
  nlinarith

/-- A strict one-tenth upper bound for the weighted linear perturbation. -/
theorem expected_perturbation_strict_upper_bound (n : ℕ) (hn : 5 ≤ n) :
    expected_remainder * (1 / (n : ℚ)) < 1 / 10 := by
  exact lt_of_le_of_lt (expected_perturbation_bound_at_five n hn) (by norm_num)

/-- At five the non-strict perturbation bound is attained exactly. -/
theorem expected_perturbation_at_five_eq :
    expected_remainder * (1 / (5 : ℚ)) = 8 / 81 := by
  rw [expected_remainder_eq]
  norm_num

/-- Dividing a coefficient below one by a positive input gives the uniform correction bound. -/
theorem relative_correction_lt (r n : ℚ) (hr : r < 1) (hn : 0 < n) :
    1 + r / n < 1 + 1 / n := by
  have hd := (div_lt_div_iff_of_pos_right hn).2 hr
  linarith

#print axioms expected_remainder_eq
#print axioms remainder_uniform_lt_one
#print axioms expected_perturbation_bound_at_five
#print axioms expected_perturbation_strict_upper_bound

end CollatzRemainderBound
