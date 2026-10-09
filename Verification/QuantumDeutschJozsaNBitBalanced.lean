/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumDeutschJozsaGeneral
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

/-! Exact classification of balanced Boolean oracles, using the existing circuit model.
The positive-qubit hypothesis is essential for the binomial formula. -/
noncomputable section
open scoped BigOperators
namespace QuantumDeutschJozsaNBitBalanced
open QuantumDeutschJozsaGeneral

variable {n : ℕ}

def BalancedFamily (n : ℕ) := {f : Bits n → Bool // IsBalanced f}

instance (n : ℕ) : Fintype (BalancedFamily n) := by
  classical
  exact inferInstanceAs (Fintype {f : Bits n → Bool // IsBalanced f})

def toSupport (f : Bits n → Bool) : Finset (Bits n) :=
  Finset.univ.filter (fun x => f x = true)

def ofSupport (S : Finset (Bits n)) : Bits n → Bool := fun x => decide (x ∈ S)

@[simp] theorem ofSupport_toSupport (f : Bits n → Bool) : ofSupport (toSupport f) = f := by
  funext x
  cases h : f x <;> simp [ofSupport, toSupport, h]

@[simp] theorem toSupport_ofSupport (S : Finset (Bits n)) : toSupport (ofSupport S) = S := by
  ext x
  simp [toSupport, ofSupport]

def supportEquiv (n : ℕ) : (Bits n → Bool) ≃ Finset (Bits n) where
  toFun := toSupport
  invFun := ofSupport
  left_inv := ofSupport_toSupport
  right_inv := toSupport_ofSupport

theorem balanced_iff_card_support (hn : 1 ≤ n) (f : Bits n → Bool) :
    IsBalanced f ↔ (toSupport f).card = 2 ^ (n - 1) := by
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hn]
    rw [pow_succ, Nat.mul_comm]
  unfold IsBalanced trueCount
  rw [card_bits, hpow]
  change 2 * (toSupport f).card = 2 * 2 ^ (n - 1) ↔ _
  omega

def balanced_family_equiv_powerset (hn : 1 ≤ n) :
    BalancedFamily n ≃ {S : Finset (Bits n) // S.card = 2 ^ (n - 1)} where
  toFun f := ⟨toSupport f.val, (balanced_iff_card_support hn f.val).mp f.property⟩
  invFun S := ⟨ofSupport S.val, (balanced_iff_card_support hn _).mpr (by simpa using S.property)⟩
  left_inv f := by apply Subtype.ext; exact ofSupport_toSupport f.val
  right_inv S := by apply Subtype.ext; exact toSupport_ofSupport S.val

theorem balanced_card_formula_pos (hn : 1 ≤ n) :
    Fintype.card (BalancedFamily n) = Nat.choose (2 ^ n) (2 ^ (n - 1)) := by
  classical
  let e : {S : Finset (Bits n) // S.card = 2 ^ (n - 1)} ≃
      ↥(Finset.univ.powersetCard (2 ^ (n - 1)) : Finset (Finset (Bits n))) :=
    Equiv.subtypeEquivRight (fun S => by simp)
  rw [Fintype.card_congr ((balanced_family_equiv_powerset hn).trans e),
    Fintype.card_coe, Finset.card_powersetCard, Finset.card_univ, card_bits]

theorem balanced_card_zero_qubits : Fintype.card (BalancedFamily 0) = 0 := by
  apply Fintype.card_eq_zero_iff.mpr
  exact ⟨fun f => (bits_zero_result f.val).2.1 f.property⟩

theorem balanced_iff_zero_amplitude (f : Bits n → Bool) :
    IsBalanced f ↔ zeroStateAmplitude f = 0 := by
  constructor
  · intro h; exact (dj_balanced_amplitude f h).1
  · intro h
    have hc : (Fintype.card (Bits n) : ℝ) ≠ 0 := by simp
    rw [zeroStateAmplitude, sum_sign, div_eq_zero_iff] at h
    have he := h.resolve_right hc
    have he' : 2 * (trueCount f : ℝ) = (Fintype.card (Bits n) : ℝ) := by linarith
    exact_mod_cast he'

theorem balanced_iff_zero_prob (f : Bits n → Bool) :
    IsBalanced f ↔ zeroStateProb f = 0 := by
  rw [balanced_iff_zero_amplitude, zeroStateProb]
  constructor
  · intro h; simp [h]
  · intro h; nlinarith [sq_nonneg (zeroStateAmplitude f)]

theorem balanced_iff_run_zero (f : Bits n → Bool) :
    IsBalanced f ↔ runDJ f (zeroBits n) = 0 := by
  rw [zero_amplitude, balanced_iff_zero_amplitude]

theorem balanced_iff_outcome_zero (f : Bits n → Bool) :
    IsBalanced f ↔ outcomeWeight f (zeroBits n) = 0 := by
  rw [zero_weight, balanced_iff_zero_prob]

theorem dj_promise_separation_exact (f : Bits n → Bool) (hp : DJPromise f) :
    (zeroStateProb f = 0 ↔ IsBalanced f) ∧ (zeroStateProb f = 1 ↔ IsConstant f) := by
  exact ⟨(balanced_iff_zero_prob f).symm,
    dj_promise_zero_error_separation f hp (by simp)⟩

theorem balanced_count_n0 : Fintype.card (BalancedFamily 0) = 0 := balanced_card_zero_qubits
theorem balanced_count_n1 : Fintype.card (BalancedFamily 1) = 2 := by
  rw [balanced_card_formula_pos (by decide)]; rfl
theorem balanced_count_n2 : Fintype.card (BalancedFamily 2) = 6 := by
  rw [balanced_card_formula_pos (by decide)]; rfl
theorem balanced_count_n3 : Fintype.card (BalancedFamily 3) = 70 := by
  rw [balanced_card_formula_pos (by decide)]; rfl

theorem constructive_witness_n_pos (hn : 1 ≤ n) :
    IsBalanced (fun x : Bits n => x ⟨0, hn⟩) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  apply (balanced_iff_zero_amplitude _).mpr
  simp [zeroStateAmplitude, sum_bits_succ, signOfBool]

/-- Relabeling the computational basis does not change the oracle truth count. -/
def bitsFinEquiv (n : ℕ) : Bits n ≃ Fin (2 ^ n) := Fintype.equivFinOfCardEq (card_bits n)

def fromFinOracle (f : Fin (2 ^ n) → Bool) : Bits n → Bool := fun x => f (bitsFinEquiv n x)

theorem fin_oracle_trueCount (f : Fin (2 ^ n) → Bool) :
    trueCount (fromFinOracle f) = trueCount f := by
  classical
  let e : {x : Bits n // fromFinOracle f x = true} ≃
      {y : Fin (2 ^ n) // f y = true} :=
    (bitsFinEquiv n).subtypeEquiv (fun _ => Iff.rfl)
  have h := Fintype.card_congr e
  simpa [Fintype.card_subtype, trueCount] using h

theorem fin_oracle_balanced (f : Fin (2 ^ n) → Bool) :
    IsBalanced (fromFinOracle f) ↔ IsBalanced f := by
  unfold IsBalanced
  rw [fin_oracle_trueCount, card_bits, Fintype.card_fin]

/-- Full cardinality, including the exceptional singleton domain. -/
theorem balanced_card_formula (n : ℕ) :
    Fintype.card (BalancedFamily n) =
      if n = 0 then 0 else Nat.choose (2 ^ n) (2 ^ (n - 1)) := by
  split_ifs with h
  · subst n; exact balanced_card_zero_qubits
  · exact balanced_card_formula_pos (by omega)

theorem positive_family_nonempty (hn : 1 ≤ n) : Nonempty (BalancedFamily n) :=
  ⟨⟨_, constructive_witness_n_pos hn⟩⟩

theorem constants_excluded (f : Bits n → Bool) (hc : IsConstant f) : ¬ IsBalanced f := by
  intro hb
  exact constant_not_balanced f (by simp) ⟨hc, hb⟩

structure QuantumDeutschJozsaNBitBalancedSuite : Prop where
  support_inverse : ∀ n (f : Bits n → Bool), ofSupport (toSupport f) = f
  characteristic_inverse : ∀ n (S : Finset (Bits n)), toSupport (ofSupport S) = S
  classification : ∀ n, 1 ≤ n → Nonempty
    (BalancedFamily n ≃ {S : Finset (Bits n) // S.card = 2 ^ (n - 1)})
  cardinality : ∀ n, Fintype.card (BalancedFamily n) =
    if n = 0 then 0 else Nat.choose (2 ^ n) (2 ^ (n - 1))
  circuit_amplitude : ∀ n (f : Bits n → Bool), IsBalanced f ↔ runDJ f (zeroBits n) = 0
  circuit_probability : ∀ n (f : Bits n → Bool), IsBalanced f ↔ outcomeWeight f (zeroBits n) = 0
  promise_separation : ∀ n (f : Bits n → Bool), DJPromise f →
    (zeroStateProb f = 0 ↔ IsBalanced f) ∧ (zeroStateProb f = 1 ↔ IsConstant f)
  witness : ∀ n (hn : 1 ≤ n), IsBalanced (fun x : Bits n => x ⟨0, hn⟩)
  finite_register_bridge : ∀ n (f : Fin (2 ^ n) → Bool),
    IsBalanced (fromFinOracle f) ↔ IsBalanced f
  small_counts : Fintype.card (BalancedFamily 0) = 0 ∧
    Fintype.card (BalancedFamily 1) = 2 ∧
    Fintype.card (BalancedFamily 2) = 6 ∧ Fintype.card (BalancedFamily 3) = 70

theorem quantum_deutsch_jozsa_nbit_balanced_master_suite :
    QuantumDeutschJozsaNBitBalancedSuite where
  support_inverse := fun _ => ofSupport_toSupport
  characteristic_inverse := fun _ => toSupport_ofSupport
  classification := fun _ hn => ⟨balanced_family_equiv_powerset hn⟩
  cardinality := balanced_card_formula
  circuit_amplitude := fun _ => balanced_iff_run_zero
  circuit_probability := fun _ => balanced_iff_outcome_zero
  promise_separation := fun _ => dj_promise_separation_exact
  witness := fun _ => constructive_witness_n_pos
  finite_register_bridge := fun _ => fin_oracle_balanced
  small_counts := ⟨balanced_count_n0, balanced_count_n1, balanced_count_n2, balanced_count_n3⟩

end QuantumDeutschJozsaNBitBalanced
