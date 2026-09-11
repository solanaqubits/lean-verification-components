import Verification.CollatzBase

set_option linter.style.header false

namespace CollatzCycles

open CollatzBase

/-!
## Periodic points
-/

/-- `n` returns to itself after the positive number `k` of Collatz steps. -/
def IsPeriodic (k : ℕ) (n : ℕ) : Prop :=
  0 < k ∧ collatzIter k n = n

/-!
## No positive fixed points
-/

/-- The Collatz map has no positive fixed point. -/
theorem no_fixed_points_pos (n : ℕ) (hn : 0 < n) :
    collatz n ≠ n := by
  intro h
  dsimp [collatz] at h
  split_ifs at h with h_even
  · omega
  · omega

/-- No positive natural number returns to itself after one Collatz step. -/
theorem no_period_one (n : ℕ) (hn : 0 < n) :
    ¬ IsPeriodic 1 n := by
  intro ⟨_, h_per⟩
  have h1 : collatzIter 1 n = collatz n := rfl
  rw [h1] at h_per
  exact no_fixed_points_pos n hn h_per

/-!
## No positive two-step returns
-/

/-- No positive natural number returns to itself after two Collatz steps. -/
theorem no_period_two (n : ℕ) (hn : 0 < n) :
    ¬ IsPeriodic 2 n := by
  intro ⟨_, h_per⟩
  have h2 : collatzIter 2 n = collatz (collatz n) := rfl
  rw [h2] at h_per
  dsimp [collatz] at h_per
  split_ifs at h_per with h1 h2 h3
  · omega
  · omega
  · omega
  · omega

/-!
## The canonical three-step orbit
-/

/-- The trajectory `1 → 4 → 2 → 1` returns to `1` after three steps. -/
theorem trivial_cycle_one : IsPeriodic 3 1 :=
  ⟨by decide, rfl⟩

/-- The trajectory `2 → 1 → 4 → 2` returns to `2` after three steps. -/
theorem trivial_cycle_two : IsPeriodic 3 2 :=
  ⟨by decide, rfl⟩

/-- The trajectory `4 → 2 → 1 → 4` returns to `4` after three steps. -/
theorem trivial_cycle_four : IsPeriodic 3 4 :=
  ⟨by decide, rfl⟩

/-- The positive natural numbers returning after three steps are exactly `1`, `2`, and `4`. -/
theorem period_three_iff (n : ℕ) (hn : 0 < n) :
    IsPeriodic 3 n ↔ n = 1 ∨ n = 2 ∨ n = 4 := by
  constructor
  · rintro ⟨_, h_per⟩
    change collatz (collatz (collatz n)) = n at h_per
    simp only [collatz] at h_per
    split_ifs at h_per <;> omega
  · rintro (rfl | rfl | rfl)
    · exact trivial_cycle_one
    · exact trivial_cycle_two
    · exact trivial_cycle_four

#print axioms no_period_two
#print axioms trivial_cycle_one
#print axioms period_three_iff

end CollatzCycles
