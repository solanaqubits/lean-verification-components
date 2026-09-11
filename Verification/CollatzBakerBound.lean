import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

set_option linter.style.header false

namespace CollatzBakerBound

/-- Prescribed integer denominator for three odd-transition equations. -/
def cycle3Denom (S : ℕ) : ℤ := (2 : ℤ) ^ S - 27

/-- Prescribed numerator; no trajectory equation is derived in this module. -/
def cycle3Numerator (a1 a2 : ℕ) : ℕ := 9 + 3 * 2 ^ a1 + 2 ^ (a1 + a2)

def IsValidPartition3 (a1 a2 a3 S : ℕ) : Prop :=
  1 ≤ a1 ∧ 1 ≤ a2 ∧ 1 ≤ a3 ∧ a1 + a2 + a3 = S

theorem cycle3_denom_nonpos (S : ℕ) (hS : S ≤ 4) : cycle3Denom S ≤ 0 := by
  interval_cases S <;> norm_num [cycle3Denom]

theorem cycle3_denom_pos_iff_ge_five (S : ℕ) : 0 < cycle3Denom S ↔ 5 ≤ S := by
  constructor
  · intro hp
    by_contra hn
    have hle : S ≤ 4 := by omega
    have hnp := cycle3_denom_nonpos S hle
    omega
  · intro hs
    have hp : (2 : ℕ) ^ 5 ≤ (2 : ℕ) ^ S := Nat.pow_le_pow_right (by decide) hs
    have hi : (2 : ℤ) ^ 5 ≤ (2 : ℤ) ^ S := by exact_mod_cast hp
    dsimp [cycle3Denom]
    norm_num at hi
    linarith

/-- Exhaustive numerator values for positive partitions of five. -/
theorem cycle3_numerators_S5 (a1 a2 a3 : ℕ) (h : IsValidPartition3 a1 a2 a3 5) :
    cycle3Numerator a1 a2 = 19 ∨ cycle3Numerator a1 a2 = 23 ∨
    cycle3Numerator a1 a2 = 31 ∨ cycle3Numerator a1 a2 = 29 ∨
    cycle3Numerator a1 a2 = 37 ∨ cycle3Numerator a1 a2 = 49 := by
  rcases h with ⟨h1, h2, h3, hs⟩
  have hb1 : a1 ≤ 3 := by omega
  have hb2 : a2 ≤ 3 := by omega
  interval_cases a1 <;> interval_cases a2 <;>
    norm_num [cycle3Numerator] <;> omega

/-- None of the numerators for total shift five is divisible by its denominator. -/
theorem no_collatz_3cycle_S5 (a1 a2 a3 : ℕ) (h : IsValidPartition3 a1 a2 a3 5) :
    ¬ (5 ∣ cycle3Numerator a1 a2) := by
  rcases cycle3_numerators_S5 a1 a2 a3 h with h | h | h | h | h | h <;>
    rw [h] <;> norm_num

/-- Divisibility for total shift six occurs only at the equal partition. -/
theorem cycle3_numerators_S6_div_37 (a1 a2 a3 : ℕ) (h : IsValidPartition3 a1 a2 a3 6) :
    37 ∣ cycle3Numerator a1 a2 ↔ (a1 = 2 ∧ a2 = 2 ∧ a3 = 2) := by
  rcases h with ⟨h1, h2, h3, hs⟩
  have hb1 : a1 ≤ 4 := by omega
  have hb2 : a2 ≤ 4 := by omega
  interval_cases a1 <;> interval_cases a2 <;>
    norm_num [cycle3Numerator] <;> omega

theorem cycle3_S6_unique_quotient (a1 a2 a3 : ℕ) (h : IsValidPartition3 a1 a2 a3 6)
    (hd : 37 ∣ cycle3Numerator a1 a2) : cycle3Numerator a1 a2 / 37 = 1 := by
  rcases (cycle3_numerators_S6_div_37 a1 a2 a3 h).mp hd with ⟨rfl, rfl, _⟩
  norm_num [cycle3Numerator]

/-- Finite arithmetic guarantees, without a Baker estimate or an all-cycle exclusion. -/
structure CollatzBakerFormalSuite : Prop where
  h_denom_pos : ∀ S : ℕ, 0 < cycle3Denom S ↔ 5 ≤ S
  h_no_cycle_S5 : ∀ a1 a2 a3 : ℕ, IsValidPartition3 a1 a2 a3 5 →
    ¬ (5 ∣ cycle3Numerator a1 a2)
  h_unique_S6 : ∀ a1 a2 a3 : ℕ, IsValidPartition3 a1 a2 a3 6 →
    (37 ∣ cycle3Numerator a1 a2 ↔ (a1 = 2 ∧ a2 = 2 ∧ a3 = 2))
  h_quotient_one : ∀ a1 a2 a3 : ℕ, IsValidPartition3 a1 a2 a3 6 →
    37 ∣ cycle3Numerator a1 a2 → cycle3Numerator a1 a2 / 37 = 1

theorem collatz_baker_master_verification_suite : CollatzBakerFormalSuite := {
  h_denom_pos := cycle3_denom_pos_iff_ge_five
  h_no_cycle_S5 := no_collatz_3cycle_S5
  h_unique_S6 := cycle3_numerators_S6_div_37
  h_quotient_one := cycle3_S6_unique_quotient
}

#print axioms collatz_baker_master_verification_suite

end CollatzBakerBound
