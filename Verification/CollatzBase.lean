import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

namespace CollatzBase

/-- The classical Collatz map on `ℕ`. -/
def collatz (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Apply the Collatz map `k` times. -/
def collatzIter : ℕ → ℕ → ℕ
  | 0, n => n
  | k + 1, n => collatz (collatzIter k n)

/-!
## Computations for the base set

Each trajectory reduces directly from the definitions by kernel computation.
-/

theorem collatz_one : collatzIter 0 1 = 1 := rfl
theorem collatz_two : collatzIter 1 2 = 1 := rfl
theorem collatz_three : collatzIter 7 3 = 1 := rfl
theorem collatz_four : collatzIter 2 4 = 1 := rfl
theorem collatz_five : collatzIter 5 5 = 1 := rfl

/-- Every natural number in `[1, 5]` reaches `1` after finitely many Collatz steps. -/
theorem collatz_base_absorption (n : ℕ) (h_pos : 1 ≤ n) (h_le : n ≤ 5) :
    ∃ k : ℕ, collatzIter k n = 1 := by
  interval_cases n
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨7, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨5, rfl⟩

#print axioms collatz_base_absorption

end CollatzBase
