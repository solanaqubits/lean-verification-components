import Verification.CollatzDyadicContract
import Mathlib.Tactic.NormNum

set_option linter.style.header false

namespace CollatzBranchSeven

open CollatzBase CollatzAttractor CollatzParity

/-- Residue seven modulo eight splits into residues seven and fifteen modulo sixteen. -/
theorem mod8_seven_split_mod16 (n : ℕ) (h : n % 8 = 7) :
    n % 16 = 7 ∨ n % 16 = 15 := by
  omega

/-- The first two-step value is odd and three modulo four. -/
theorem collatz_mod16_seven_stage1 (n : ℕ) (h : n % 16 = 7) :
    ((3 * n + 1) / 2) % 2 = 1 ∧ ((3 * n + 1) / 2) % 4 = 3 := by
  constructor <;> omega

/-- The next two-step value has the stated formula and residue one modulo four. -/
theorem collatz_mod16_seven_stage2 (n : ℕ) (h : n % 16 = 7) :
    (3 * ((3 * n + 1) / 2) + 1) / 2 = (9 * n + 5) / 4 ∧
    ((9 * n + 5) / 4) % 4 = 1 := by
  constructor <;> omega

/-- The exact seven-step formula for residue seven modulo sixteen. -/
theorem collatzIter_seven_mod16_seven (n : ℕ) (h : n % 16 = 7) :
    collatzIter 7 n = (27 * n + 19) / 16 := by
  have h_odd : n % 2 = 1 := by omega
  have h_iter2 := collatzIter_two_odd n h_odd
  have h_st1 := collatz_mod16_seven_stage1 n h
  have h_st2 := collatz_mod16_seven_stage2 n h
  have h_iter4 : collatzIter 4 n = (9 * n + 5) / 4 := by
    calc
      collatzIter 4 n = collatzIter 2 (collatzIter 2 n) := collatzIter_add 2 2 n
      _ = collatzIter 2 ((3 * n + 1) / 2) := by rw [h_iter2]
      _ = (3 * ((3 * n + 1) / 2) + 1) / 2 :=
        collatzIter_two_odd _ h_st1.1
      _ = (9 * n + 5) / 4 := h_st2.1
  have h_iter7 : collatzIter 7 n = collatzIter 3 (collatzIter 4 n) :=
    collatzIter_add 4 3 n
  rw [h_iter7, h_iter4, collatzIter_three_mod4_one _ h_st2.2]
  omega

/-- Starting at seven, the trajectory reaches five after eleven steps. -/
theorem collatzIter_seven_reaches_five :
    collatzIter 11 7 = 5 := by
  have h7 := collatzIter_seven_mod16_seven 7 (by decide)
  have h_add : collatzIter 11 7 = collatzIter 4 (collatzIter 7 7) :=
    collatzIter_add 7 4 7
  rw [h_add, h7]
  decide

/-- Starting at seven, the trajectory eventually reaches one via the finite base interval. -/
theorem collatz_seven_reaches_one :
    ∃ m : ℕ, collatzIter m 7 = 1 := by
  apply collatz_reaches_one_if_enters_compact 7 11
  · rw [collatzIter_seven_reaches_five]
    omega
  · rw [collatzIter_seven_reaches_five]

/-- Rational bookkeeping for a proposed equal split; no Haar-measure identification is asserted. -/
theorem equal_weight_split : (1 / 4 : ℚ) = 1 / 8 + 1 / 8 := by
  norm_num

#print axioms collatzIter_seven_mod16_seven
#print axioms collatz_seven_reaches_one
#print axioms equal_weight_split

end CollatzBranchSeven
