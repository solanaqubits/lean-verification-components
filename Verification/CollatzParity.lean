import Verification.CollatzBase

set_option linter.style.header false

namespace CollatzParity

open CollatzBase

/-- The Collatz step from an odd natural number is even. -/
theorem collatz_odd_step_even (n : ℕ) (h : n % 2 = 1) :
    (collatz n) % 2 = 0 := by
  dsimp [collatz]
  split_ifs with h_even
  · omega
  · omega

/-- Two steps from an odd number consist of `3 * n + 1` followed by division by two. -/
theorem collatzIter_two_odd (n : ℕ) (h : n % 2 = 1) :
    collatzIter 2 n = (3 * n + 1) / 2 := by
  have h1 : collatzIter 1 n = 3 * n + 1 := by
    have h_odd : n % 2 ≠ 0 := by omega
    change (if n % 2 = 0 then n / 2 else 3 * n + 1) = 3 * n + 1
    exact if_neg h_odd
  have h2 : collatzIter 2 n = collatz (collatzIter 1 n) := rfl
  rw [h1] at h2
  rw [h2]
  dsimp [collatz]
  split_ifs with h_even2
  · rfl
  · have h_mod : (3 * n + 1) % 2 = 0 := by omega
    contradiction

/-- If `n ≡ 1 (mod 4)`, then `3 * n + 1` is divisible by four. -/
theorem collatz_mod4_one_div4 (n : ℕ) (h : n % 4 = 1) :
    (3 * n + 1) % 4 = 0 := by
  omega

/-- For `n ≡ 1 (mod 4)`, the odd step is followed by two divisions by two. -/
theorem collatzIter_three_mod4_one (n : ℕ) (h : n % 4 = 1) :
    collatzIter 3 n = (3 * n + 1) / 4 := by
  have h_odd : n % 2 = 1 := by omega
  have h2 : collatzIter 2 n = (3 * n + 1) / 2 := collatzIter_two_odd n h_odd
  have h3 : collatzIter 3 n = collatz (collatzIter 2 n) := rfl
  rw [h2] at h3
  rw [h3]
  dsimp [collatz]
  split_ifs with h_even
  · have h_div : ((3 * n + 1) / 2) / 2 = (3 * n + 1) / 4 := by omega
    exact h_div
  · have h_contra : ((3 * n + 1) / 2) % 2 = 0 := by omega
    contradiction

/-- For `n ≡ 3 (mod 4)`, dividing `3 * n + 1` by two gives an odd number. -/
theorem collatz_mod4_three_next_odd (n : ℕ) (h : n % 4 = 3) :
    ((3 * n + 1) / 2) % 2 = 1 := by
  omega

/-- Every odd natural number belongs to one of the two odd residue classes modulo four. -/
theorem odd_dyadic_partition (n : ℕ) (h : n % 2 = 1) :
    n % 4 = 1 ∨ n % 4 = 3 := by
  omega

#print axioms collatzIter_two_odd
#print axioms collatzIter_three_mod4_one
#print axioms odd_dyadic_partition

end CollatzParity
