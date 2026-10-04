/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! Exact increasing magnitude grid for binary formats, including a virtual overflow neighbor. -/

namespace NumericBinaryGrid

/-- Magnitude in units of the least subnormal quantum; `B = 2^fractionBits`. -/
def magnitudeUnits (B k : ℕ) : ℕ :=
  if k < B then k else (B + k % B) * 2 ^ (k / B - 1)

/-- Exact rational decoder, before interpreting the terminal code as infinity. -/
def magnitude (B : ℕ) (quantum : ℚ) (k : ℕ) : ℚ :=
  quantum * magnitudeUnits B k

theorem magnitudeUnits_zero (B : ℕ) : magnitudeUnits B 0 = 0 := by
  simp [magnitudeUnits]

theorem magnitude_zero (B : ℕ) (quantum : ℚ) : magnitude B quantum 0 = 0 := by
  simp [magnitude, magnitudeUnits_zero]

theorem magnitudeUnits_lt_succ (B k : ℕ) (hB : 1 < B) :
    magnitudeUnits B k < magnitudeUnits B (k + 1) := by
  by_cases hk : k < B
  · by_cases hk1 : k + 1 < B
    · simp [magnitudeUnits, hk, hk1]
    · have heq : k + 1 = B := by omega
      simp only [magnitudeUnits, if_pos hk, heq, lt_self_iff_false, if_false,
        Nat.mod_self, Nat.add_zero, Nat.div_self (by omega : 0 < B)]
      simpa using hk
  · have hkB : B ≤ k := by omega
    have hq : 1 ≤ k / B := (Nat.le_div_iff_mul_le (by omega : 0 < B)).2 (by simpa using hkB)
    have hmod : k % B < B := Nat.mod_lt k (by omega : 0 < B)
    by_cases hr : k % B + 1 < B
    · have hm : (k + 1) % B = k % B + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hB, Nat.mod_eq_of_lt hr]
      have hd : (k + 1) / B = k / B := by
        rw [Nat.add_div (by omega : 0 < B)]
        simp [Nat.mod_eq_of_lt hB, Nat.div_eq_of_lt hB, show ¬ B ≤ k % B + 1 by omega]
      simp only [magnitudeUnits, if_neg hk, if_neg (show ¬k + 1 < B by omega), hm, hd]
      exact Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
    · have hm : (k + 1) % B = 0 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hB, show k % B + 1 = B by omega, Nat.mod_self]
      have hd : (k + 1) / B = k / B + 1 := by
        rw [Nat.add_div (by omega : 0 < B)]
        simp [Nat.mod_eq_of_lt hB, Nat.div_eq_of_lt hB, show B ≤ k % B + 1 by omega]
      have hr' : k % B + 1 = B := by omega
      have he : k / B + 1 - 1 = (k / B - 1) + 1 := by omega
      simp only [magnitudeUnits, if_neg hk, if_neg (show ¬k + 1 < B by omega), hm, hd,
        Nat.add_zero, he, pow_succ]
      have hpow : 0 < 2 ^ (k / B - 1) := by positivity
      nlinarith

theorem magnitudeUnits_strictMono (B : ℕ) (hB : 1 < B) :
    StrictMono (magnitudeUnits B) :=
  strictMono_nat_of_lt_succ fun k => magnitudeUnits_lt_succ B k hB

theorem magnitude_strictMono (B : ℕ) (quantum : ℚ) (hB : 1 < B)
    (hq : 0 < quantum) : StrictMono (magnitude B quantum) := by
  intro a b hab
  apply mul_lt_mul_of_pos_left _ hq
  exact_mod_cast magnitudeUnits_strictMono B hB hab

/-- The terminal code is decoded as the next binade, not as a rational infinity. -/
theorem magnitudeUnits_virtual (B E : ℕ) (hB : 0 < B) :
    magnitudeUnits B ((E + 1) * B) = B * 2 ^ E := by
  have h : ¬ (E + 1) * B < B := by nlinarith
  simp [magnitudeUnits, h, Nat.mul_div_cancel _ hB]

/-- Number of fraction-field combinations in binary64. -/
def binary64Base : ℕ := 2 ^ 52

/-- The quantum of the binary64 subnormal grid. -/
def binary64Quantum : ℚ := 1 / 2 ^ 1074

/-- All nonnegative finite encodings precede this virtual overflow code. -/
def binary64Last : ℕ := 2047 * binary64Base

/-- Rational decoder of nonnegative binary64 codes, with a virtual final neighbor. -/
def binary64Value : ℕ → ℚ := magnitude binary64Base binary64Quantum

theorem binary64Value_zero : binary64Value 0 = 0 := by
  exact magnitude_zero _ _

theorem binary64Value_strictMono : StrictMono binary64Value := by
  apply magnitude_strictMono
  · norm_num [binary64Base]
  · unfold binary64Quantum
    positivity

theorem binary64Value_least_subnormal : binary64Value 1 = 1 / 2 ^ 1074 := by
  norm_num [binary64Value, magnitude, magnitudeUnits, binary64Base, binary64Quantum]

set_option maxRecDepth 4096 in
set_option exponentiation.threshold 4096 in
theorem binary64Value_virtual : binary64Value binary64Last = 2 ^ 1024 := by
  change binary64Quantum * (magnitudeUnits binary64Base ((2046 + 1) * binary64Base) : ℚ) = _
  rw [magnitudeUnits_virtual _ _ (by norm_num [binary64Base])]
  norm_num [binary64Quantum, binary64Base]

/-- Significand integer, including the virtual next-binade significand. -/
def significand (B k : ℕ) : ℕ := if k < B then k else B + k % B

theorem significand_parity (B k : ℕ) (hB : 2 ∣ B) :
    significand B k % 2 = k % 2 := by
  unfold significand
  split_ifs
  · rfl
  · rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hB, Nat.zero_add,
      Nat.mod_mod_of_dvd k hB, Nat.mod_mod]

theorem binary64_significand_parity (k : ℕ) :
    significand binary64Base k % 2 = k % 2 := by
  apply significand_parity
  norm_num [binary64Base]

theorem binary64_virtual_even : binary64Last % 2 = 0 := by
  norm_num [binary64Last, binary64Base]

theorem binary64_virtual_significand_even :
    significand binary64Base binary64Last % 2 = 0 := by
  rw [binary64_significand_parity, binary64_virtual_even]

theorem magnitude_subnormal (B k : ℕ) (quantum : ℚ) (hk : k < B) :
    magnitude B quantum k = quantum * k := by
  simp [magnitude, magnitudeUnits, hk]

theorem binary64Value_subnormal (k : ℕ) (hk : k < binary64Base) :
    binary64Value k = (k : ℚ) / 2 ^ 1074 := by
  rw [binary64Value, magnitude_subnormal _ _ _ hk]
  simp [binary64Quantum, div_eq_mul_inv, mul_comm]

end NumericBinaryGrid
