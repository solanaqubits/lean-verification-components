import Mathlib.Tactic.NormNum
import Verification.CollatzDyadicContract

set_option linter.style.header false

namespace CollatzAverageDrift

open CollatzBase CollatzParity

/-- The exact four-step formula for residue five modulo eight. -/
theorem collatzIter_four_mod8_five (n : ℕ) (h : n % 8 = 5) :
    collatzIter 4 n = (3 * n + 1) / 8 := by
  have h_mod4 : n % 4 = 1 := by omega
  have h3 := collatzIter_three_mod4_one n h_mod4
  change collatz (collatzIter 3 n) = (3 * n + 1) / 8
  rw [h3]
  dsimp [collatz]
  split_ifs with h_even
  · omega
  · have h_contra : ((3 * n + 1) / 4) % 2 = 0 := by omega
    contradiction

/-- Four steps strictly decrease an input in residue five modulo eight. -/
theorem collatzIter_four_strict_decrease (n : ℕ) (hn : 1 ≤ n) (h : n % 8 = 5) :
    collatzIter 4 n < n := by
  rw [collatzIter_four_mod8_five n h]
  omega

/-- Rational weights on the four odd residue classes, constrained to be uniform.
This is a finite weight model; no identification with Haar measure is asserted.
-/
structure DyadicMeasure8 where
  w1 : ℚ := 1 / 4
  w3 : ℚ := 1 / 4
  w5 : ℚ := 1 / 4
  w7 : ℚ := 1 / 4
  w1_eq : w1 = 1 / 4
  w3_eq : w3 = 1 / 4
  w5_eq : w5 = 1 / 4
  w7_eq : w7 = 1 / 4

/-- The uniform weights on the four odd residue classes. -/
def uniformDyadicMeasure8 : DyadicMeasure8 where
  w1_eq := rfl
  w3_eq := rfl
  w5_eq := rfl
  w7_eq := rfl

/-- Every constrained uniform weight model has total weight one. -/
theorem dyadic_measure8_normalized (m : DyadicMeasure8) :
    m.w1 + m.w3 + m.w5 + m.w7 = 1 := by
  rw [m.w1_eq, m.w3_eq, m.w5_eq, m.w7_eq]
  norm_num

/-- Leading coefficient in the three-step formula for residue one modulo eight. -/
def coeff_mod8_one : ℚ := 3 / 4

/-- Leading coefficient in the four-step formula for residue five modulo eight. -/
def coeff_mod8_five : ℚ := 3 / 8

/-- Leading coefficient in the five-step formula for residue three modulo eight. -/
def coeff_mod8_three : ℚ := 9 / 8

/-- The arithmetic mean of the two specified decreasing-branch coefficients. -/
theorem direct_contracting_branches_mean :
    (coeff_mod8_one + coeff_mod8_five) / 2 = 9 / 16 := by
  norm_num [coeff_mod8_one, coeff_mod8_five]

/-- The mean of the three specified leading coefficients is three quarters. -/
theorem resolved_three_branches_mean_contract :
    (coeff_mod8_one + coeff_mod8_five + coeff_mod8_three) / 3 = 3 / 4 ∧
    (coeff_mod8_one + coeff_mod8_five + coeff_mod8_three) / 3 < 1 := by
  norm_num [coeff_mod8_one, coeff_mod8_five, coeff_mod8_three]

/-- A rational identity with a hypothetical fourth coefficient of `9/8`.
Despite the historical name, this does not bound the Collatz branch seven modulo eight.
-/
theorem total_four_branch_weighted_drift_bound :
    (1 / 4 : ℚ) * coeff_mod8_one +
    (1 / 4 : ℚ) * coeff_mod8_five +
    (1 / 4 : ℚ) * coeff_mod8_three +
    (1 / 4 : ℚ) * (9 / 8 : ℚ) = 27 / 32 ∧
    (1 / 4 : ℚ) * coeff_mod8_one +
    (1 / 4 : ℚ) * coeff_mod8_five +
    (1 / 4 : ℚ) * coeff_mod8_three +
    (1 / 4 : ℚ) * (9 / 8 : ℚ) < 1 := by
  norm_num [coeff_mod8_one, coeff_mod8_five, coeff_mod8_three]

#print axioms collatzIter_four_mod8_five
#print axioms dyadic_measure8_normalized
#print axioms total_four_branch_weighted_drift_bound

end CollatzAverageDrift
