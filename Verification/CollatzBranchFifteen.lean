import Verification.CollatzBranchSeven

set_option linter.style.header false

namespace CollatzBranchFifteen

open CollatzBase CollatzAttractor CollatzParity

/-- The first two-step value is odd and three modulo four. -/
theorem collatz_mod16_fifteen_stage1 (n : ℕ) (h : n % 16 = 15) :
    ((3 * n + 1) / 2) % 2 = 1 ∧ ((3 * n + 1) / 2) % 4 = 3 := by
  constructor <;> omega

/-- The four-step value has the stated formula and remains three modulo four. -/
theorem collatz_mod16_fifteen_stage2 (n : ℕ) (h : n % 16 = 15) :
    (3 * ((3 * n + 1) / 2) + 1) / 2 = (9 * n + 5) / 4 ∧
    ((9 * n + 5) / 4) % 2 = 1 ∧
    ((9 * n + 5) / 4) % 4 = 3 := by
  constructor
  · omega
  constructor <;> omega

/-- The exact six-step formula for residue fifteen modulo sixteen. -/
theorem collatzIter_six_mod16_fifteen (n : ℕ) (h : n % 16 = 15) :
    collatzIter 6 n = (27 * n + 19) / 8 := by
  have h_odd : n % 2 = 1 := by omega
  have h_iter2 := collatzIter_two_odd n h_odd
  have h_st1 := collatz_mod16_fifteen_stage1 n h
  have h_st2 := collatz_mod16_fifteen_stage2 n h
  have h_iter4 : collatzIter 4 n = (9 * n + 5) / 4 := by
    calc
      collatzIter 4 n = collatzIter 2 (collatzIter 2 n) := collatzIter_add 2 2 n
      _ = collatzIter 2 ((3 * n + 1) / 2) := by rw [h_iter2]
      _ = (3 * ((3 * n + 1) / 2) + 1) / 2 := collatzIter_two_odd _ h_st1.1
      _ = (9 * n + 5) / 4 := h_st2.1
  have h_add : collatzIter 6 n = collatzIter 2 (collatzIter 4 n) :=
    collatzIter_add 4 2 n
  rw [h_add, h_iter4, collatzIter_two_odd _ h_st2.2.1]
  omega

/-- Starting at fifteen, the trajectory reaches five after twelve steps. -/
theorem collatzIter_fifteen_reaches_five :
    collatzIter 12 15 = 5 := by
  have h6 := collatzIter_six_mod16_fifteen 15 (by decide)
  have h_add : collatzIter 12 15 = collatzIter 6 (collatzIter 6 15) :=
    collatzIter_add 6 6 15
  rw [h_add, h6]
  decide

/-- Starting at fifteen, the trajectory reaches one via the finite base interval. -/
theorem collatz_fifteen_reaches_one :
    ∃ m : ℕ, collatzIter m 15 = 1 := by
  apply collatz_reaches_one_if_enters_compact 15 12
  · rw [collatzIter_fifteen_reaches_five]
    omega
  · rw [collatzIter_fifteen_reaches_five]

/-- Residue fifteen modulo sixteen splits into residues fifteen and thirty-one modulo thirty-two. -/
theorem mod16_fifteen_split_mod32 (n : ℕ) (h : n % 16 = 15) :
    n % 32 = 15 ∨ n % 32 = 31 := by
  omega

/-- For residue fifteen modulo thirty-two, the six-step value is one modulo four. -/
theorem collatz_mod32_fifteen_stage3 (n : ℕ) (h : n % 32 = 15) :
    ((27 * n + 19) / 8) % 4 = 1 := by
  omega

/-- The exact nine-step formula for residue fifteen modulo thirty-two. -/
theorem collatzIter_nine_mod32_fifteen (n : ℕ) (h : n % 32 = 15) :
    collatzIter 9 n = (81 * n + 65) / 32 := by
  have h_mod16 : n % 16 = 15 := by omega
  have h6 := collatzIter_six_mod16_fifteen n h_mod16
  have h_st3 := collatz_mod32_fifteen_stage3 n h
  have h_iter9 : collatzIter 9 n = collatzIter 3 (collatzIter 6 n) :=
    collatzIter_add 6 3 n
  rw [h_iter9, h6, collatzIter_three_mod4_one _ h_st3]
  omega

#print axioms collatzIter_six_mod16_fifteen
#print axioms collatz_fifteen_reaches_one
#print axioms collatzIter_nine_mod32_fifteen

end CollatzBranchFifteen
