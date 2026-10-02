/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact counting for randomized scalar Schnorr-equation batching

The discrepancy vector is fixed before coefficients are sampled uniformly from
all vectors over a prime field. Fractions below are exact finite counting ratios,
not an implementation of a random generator or the BIP 340 coefficient algorithm.
-/
namespace CryptoSchnorrBatchVerification

open scoped BigOperators

variable {q n k : ℕ}

/-- Scalar verification residual; no elliptic-curve representation is asserted. -/
def discrepancy (G s R c pk : ZMod q) : ZMod q := s * G - R - c * pk

theorem discrepancy_zero_iff (G s R c pk : ZMod q) :
    discrepancy G s R c pk = 0 ↔ s * G = R + c * pk := by
  simp only [discrepancy, sub_eq_zero]
  exact sub_eq_iff_eq_add.trans (by rw [add_comm])

/-- A weighted sum of the fixed verification residuals vanishes. -/
def batchCheck (z d : Fin n → ZMod q) : Prop := (∑ i, z i * d i) = 0

instance (z d : Fin n → ZMod q) : Decidable (batchCheck z d) :=
  inferInstanceAs (Decidable ((∑ i, z i * d i) = 0))

theorem batch_verification_completeness (d : Fin n → ZMod q)
    (hd : ∀ i, d i = 0) (z : Fin n → ZMod q) : batchCheck z d := by
  simp [batchCheck, hd]

/-- This equality connects residual batching with the weighted verification equation. -/
theorem batch_discrepancy_iff (G : ZMod q) (s R c pk z : Fin n → ZMod q) :
    batchCheck z (fun i => discrepancy G (s i) (R i) (c i) (pk i)) ↔
      (∑ i, z i * s i) * G = (∑ i, z i * R i) + ∑ i, z i * c i * pk i := by
  have hid : (∑ i, z i * discrepancy G (s i) (R i) (c i) (pk i)) =
      (∑ i, z i * s i) * G - (∑ i, z i * R i) - ∑ i, z i * c i * pk i := by
    simp only [discrepancy, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul, mul_assoc]
  unfold batchCheck
  rw [hid, sub_eq_zero, sub_eq_iff_eq_add, add_comm]

variable [Fact (Nat.Prime q)]

/-- All coefficient vectors, including zero coordinates, are in the sample space. -/
theorem coefficient_vectors_card : Fintype.card (Fin n → ZMod q) = q ^ n := by
  simp

/-- The additive map underlying the batch equation. -/
def batchHom (d : Fin n → ZMod q) : (Fin n → ZMod q) →+ ZMod q where
  toFun z := ∑ i, z i * d i
  map_zero' := by simp
  map_add' z w := by simp [add_mul, Finset.sum_add_distrib]

/-- A single nonzero residual lets the batch sum attain any field value. -/
theorem batchHom_surjective (d : Fin n → ZMod q) (j : Fin n) (hj : d j ≠ 0) :
    Function.Surjective (batchHom d) := by
  intro a
  refine ⟨Pi.single j (a / d j), ?_⟩
  simp [batchHom, Pi.single_apply, hj]

/-- Exact size of the accepting hyperplane for a fixed invalid batch. -/
theorem batch_verification_counting_soundness (d : Fin n → ZMod q) (hd : ∃ j, d j ≠ 0) :
    Fintype.card {z // batchCheck z d} = q ^ (n-1) := by
  classical
  obtain ⟨j, hj⟩ := hd
  have h := (batchHom d).ker.card_mul_index
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr (batchHom_surjective d j hj)] at h
  simp only [Nat.card_eq_fintype_card, Fintype.card_pi, ZMod.card,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_congr AddSubgroup.topEquiv.toEquiv] at h
  have hn : n ≠ 0 := by have := j.isLt; omega
  have hq : q ≠ 0 := (Fact.out : q.Prime).ne_zero
  have hexp : q ^ n = q ^ (n - 1) * q := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hexp] at h
  have heq := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq) h
  calc
    Fintype.card {z // batchCheck z d} = Fintype.card (batchHom d).ker := by
      apply Fintype.card_congr
      exact { toFun := fun z => ⟨z.val, z.property⟩
              invFun := fun z => ⟨z.val, z.property⟩
              left_inv := fun _ => rfl
              right_inv := fun _ => rfl }
    _ = _ := heq

/-- Exact fraction for a uniform choice from all coefficient vectors. -/
noncomputable def falsePositiveFraction (d : Fin n → ZMod q) : ℚ :=
  (Fintype.card {z // batchCheck z d} : ℚ) / Fintype.card (Fin n → ZMod q)

/-- For a fixed nonzero residual vector, exactly one in q coefficient vectors accepts. -/
theorem batch_verification_false_positive_prob (d : Fin n → ZMod q)
    (hd : ∃ j, d j ≠ 0) : falsePositiveFraction d = 1 / (q : ℚ) := by
  unfold falsePositiveFraction
  rw [batch_verification_counting_soundness d hd, coefficient_vectors_card]
  obtain ⟨j, _⟩ := hd
  have hq : q ≠ 0 := (Fact.out : Nat.Prime q).ne_zero
  have hexp : q ^ n = q ^ (n - 1) * q := by
    rw [← pow_succ]
    congr 1
    have := j.isLt
    omega
  rw [hexp, Nat.cast_mul, div_mul_eq_div_div,
    div_self (Nat.cast_ne_zero.mpr (pow_ne_zero _ hq))]

/-- Every round checks the same fixed discrepancy vector. -/
def roundsCheck (z : Fin k → Fin n → ZMod q) (d : Fin n → ZMod q) : Prop :=
  ∀ r, batchCheck (z r) d

instance (z : Fin k → Fin n → ZMod q) (d : Fin n → ZMod q) :
    Decidable (roundsCheck z d) := inferInstanceAs (Decidable (∀ r, batchCheck (z r) d))

/-- Uniform independent rounds mean uniform choice from this full product space. -/
noncomputable def roundsFalsePositiveFraction (d : Fin n → ZMod q) (k : ℕ) : ℚ :=
  (Fintype.card {z : Fin k → Fin n → ZMod q // roundsCheck z d} : ℚ) /
    Fintype.card (Fin k → Fin n → ZMod q)

theorem rounds_accepting_card (d : Fin n → ZMod q) (k : ℕ) :
    Fintype.card {z : Fin k → Fin n → ZMod q // roundsCheck z d} =
      Fintype.card {z // batchCheck z d} ^ k := by
  classical
  calc
    _ = Fintype.card (Fin k → {z // batchCheck z d}) :=
      Fintype.card_congr Equiv.subtypePiEquivPi
    _ = _ := by simp

theorem rounds_coefficient_vectors_card (k : ℕ) :
    Fintype.card (Fin k → Fin n → ZMod q) = q ^ (k * n) := by
  simp [pow_mul, Nat.mul_comm]

theorem rounds_fraction_power (d : Fin n → ZMod q) (k : ℕ) :
    roundsFalsePositiveFraction d k = falsePositiveFraction d ^ k := by
  unfold roundsFalsePositiveFraction falsePositiveFraction
  rw [rounds_accepting_card]
  simp [div_pow]

/-- Exact Cartesian-product count of the accepting k-round coefficient arrays. -/
theorem batch_verification_k_rounds_count (d : Fin n → ZMod q)
    (hd : ∃ j, d j ≠ 0) (k : ℕ) :
    Fintype.card {z : Fin k → Fin n → ZMod q // roundsCheck z d} =
      q ^ (k * (n - 1)) := by
  rw [rounds_accepting_card, batch_verification_counting_soundness d hd,
    ← pow_mul, Nat.mul_comm (n - 1) k]

/-- Exact independent-round fraction, including the empty experiment k = 0. -/
theorem batch_verification_k_rounds_bound (d : Fin n → ZMod q)
    (hd : ∃ j, d j ≠ 0) (k : ℕ) :
    roundsFalsePositiveFraction d k = (1 / (q : ℚ)) ^ k := by
  rw [rounds_fraction_power, batch_verification_false_positive_prob d hd]

structure SchnorrBatchVerificationFormalSuite : Prop where
  h_completeness : ∀ (q n : ℕ) (d : Fin n → ZMod q),
    (∀ i, d i = 0) → ∀ z, batchCheck z d
  h_count : ∀ (q n : ℕ) [Fact (Nat.Prime q)] (d : Fin n → ZMod q),
    (∃ j, d j ≠ 0) → Fintype.card {z // batchCheck z d} = q ^ (n - 1)
  h_fraction : ∀ (q n : ℕ) [Fact (Nat.Prime q)] (d : Fin n → ZMod q),
    (∃ j, d j ≠ 0) → falsePositiveFraction d = 1 / (q : ℚ)
  h_round_count : ∀ (q n : ℕ) [Fact (Nat.Prime q)] (d : Fin n → ZMod q),
    (∃ j, d j ≠ 0) → ∀ k,
      Fintype.card {z : Fin k → Fin n → ZMod q // roundsCheck z d} =
        q ^ (k * (n - 1))
  h_round_fraction : ∀ (q n : ℕ) [Fact (Nat.Prime q)] (d : Fin n → ZMod q),
    (∃ j, d j ≠ 0) → ∀ k, roundsFalsePositiveFraction d k = (1 / (q : ℚ)) ^ k

theorem schnorr_batch_verification_master_suite : SchnorrBatchVerificationFormalSuite := {
  h_completeness := fun _ _ => batch_verification_completeness
  h_count := fun _ _ => batch_verification_counting_soundness
  h_fraction := fun _ _ => batch_verification_false_positive_prob
  h_round_count := fun _ _ => batch_verification_k_rounds_count
  h_round_fraction := fun _ _ => batch_verification_k_rounds_bound
}

end CryptoSchnorrBatchVerification
