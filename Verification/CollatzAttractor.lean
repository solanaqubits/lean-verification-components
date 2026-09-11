import Verification.CollatzBase

set_option linter.style.header false

namespace CollatzAttractor

open CollatzBase

/-!
## Composition of Collatz iterations
-/

/-- Iterating for `k₁ + k₂` steps is equivalent to two consecutive iterations. -/
theorem collatzIter_add (k₁ k₂ : ℕ) (n : ℕ) :
    collatzIter (k₁ + k₂) n = collatzIter k₂ (collatzIter k₁ n) := by
  induction k₂ with
  | zero =>
    rw [Nat.add_zero]
    rfl
  | succ k ih =>
    rw [Nat.add_succ]
    dsimp [collatzIter]
    rw [ih]

/-!
## Reduction after reaching the finite base interval
-/

/-- If the trajectory reaches `[1, 5]`, then it reaches `1` after finitely many steps. -/
theorem collatz_reaches_one_if_enters_compact
    (n : ℕ)
    (k : ℕ)
    (h_pos : 1 ≤ collatzIter k n)
    (h_le : collatzIter k n ≤ 5) :
    ∃ m : ℕ, collatzIter m n = 1 := by
  rcases collatz_base_absorption (collatzIter k n) h_pos h_le with ⟨k_base, hk_base⟩
  use k + k_base
  rw [collatzIter_add]
  exact hk_base

/-- A state whose next Collatz value lies in `[1, 5]` eventually reaches `1`. -/
theorem collatz_one_step_reduction
    (n : ℕ)
    (h_pos : 1 ≤ collatz n)
    (h_le : collatz n ≤ 5) :
    ∃ m : ℕ, collatzIter m n = 1 := by
  have h_iter1 : collatzIter 1 n = collatz n := rfl
  rw [← h_iter1] at h_pos h_le
  exact collatz_reaches_one_if_enters_compact n 1 h_pos h_le

#print axioms collatz_reaches_one_if_enters_compact

end CollatzAttractor
