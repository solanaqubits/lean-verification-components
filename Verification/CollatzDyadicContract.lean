import Verification.CollatzBase
import Verification.CollatzAttractor
import Verification.CollatzParity

set_option linter.style.header false

namespace CollatzDyadicContract

open CollatzBase CollatzAttractor CollatzParity

/-- Three steps strictly decrease inputs at least five in residue class one modulo four. -/
theorem collatzIter_three_strict_decrease (n : ℕ) (hn : 5 ≤ n) (h_mod : n % 4 = 1) :
    collatzIter 3 n < n := by
  rw [collatzIter_three_mod4_one n h_mod]
  omega

/-- The three-step decrease is at least one in this residue class. -/
theorem collatzIter_three_le_sub_one (n : ℕ) (hn : 5 ≤ n) (h_mod : n % 4 = 1) :
    collatzIter 3 n ≤ n - 1 := by
  rw [collatzIter_three_mod4_one n h_mod]
  omega

/-- For residue three modulo eight, the two-step value is one modulo four. -/
theorem collatz_mod8_three_intermediate (n : ℕ) (h : n % 8 = 3) :
    ((3 * n + 1) / 2) % 4 = 1 := by
  omega

/-- The exact five-step formula for residue three modulo eight. -/
theorem collatzIter_five_mod8_three (n : ℕ) (h : n % 8 = 3) :
    collatzIter 5 n = (9 * n + 5) / 8 := by
  have h_odd : n % 2 = 1 := by omega
  have h2 : collatzIter 2 n = (3 * n + 1) / 2 := collatzIter_two_odd n h_odd
  have h_inter_mod4 : ((3 * n + 1) / 2) % 4 = 1 := collatz_mod8_three_intermediate n h
  have h_step3 : collatzIter 3 ((3 * n + 1) / 2) = (3 * ((3 * n + 1) / 2) + 1) / 4 :=
    collatzIter_three_mod4_one ((3 * n + 1) / 2) h_inter_mod4
  have h5 : collatzIter 5 n = collatzIter 3 (collatzIter 2 n) :=
    collatzIter_add 2 3 n
  rw [h2] at h5
  rw [h5, h_step3]
  omega

/-- For residue seven modulo eight, the two-step value is three modulo four. -/
theorem collatz_mod8_seven_intermediate (n : ℕ) (h : n % 8 = 7) :
    ((3 * n + 1) / 2) % 4 = 3 := by
  omega

/-- Every odd natural number has residue one, three, five, or seven modulo eight. -/
theorem odd_mod8_partition (n : ℕ) (h : n % 2 = 1) :
    n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
  omega

#print axioms collatzIter_three_strict_decrease
#print axioms collatzIter_five_mod8_three
#print axioms odd_mod8_partition

end CollatzDyadicContract
