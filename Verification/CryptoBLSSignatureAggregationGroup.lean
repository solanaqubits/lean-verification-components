/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Algebra.Algebra.Bilinear
import Verification.CryptoBLSSignatureAggregation
import Verification.CryptoSchnorrMultiSignaturesMuSigGroup

/-!
# BLS aggregation in cyclic prime-order bilinear groups

Completeness is independent of message distinctness and computational hardness.
The explicit scalar model witnesses the assumptions but is not cryptographically
secure. Error cancellation is a counterexample to inferring individual validity
from an aggregate equation. The real/modular bridge specializes a ring identity;
there is no claimed homomorphism from the reals to a finite field.
-/

namespace CryptoBLSSignatureAggregationGroup

open scoped BigOperators
open CryptoSchnorrMultiSignaturesMuSigGroup (CyclicSetup)

section Group
variable {q : ℕ} [Fact (Nat.Prime q)]
variable {G₁ G₂ GT : Type} [AddCommGroup G₁] [Module (ZMod q) G₁]
  [AddCommGroup G₂] [Module (ZMod q) G₂] [AddCommGroup GT] [Module (ZMod q) GT]

/-- Three cyclic groups and a genuine bilinear map, in additive target notation. -/
structure PairingSetup (q : ℕ) (G₁ G₂ GT : Type) [Fact (Nat.Prime q)]
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] where
  source₁ : CyclicSetup q G₁
  source₂ : CyclicSetup q G₂
  target : CyclicSetup q GT
  pair : G₁ →ₗ[ZMod q] G₂ →ₗ[ZMod q] GT
  nondegenerate : pair source₁.generator source₂.generator ≠ 0

variable (S : PairingSetup q G₁ G₂ GT)

def publicKey (x : ZMod q) : G₂ := x • S.source₂.generator

def sign (x : ZMod q) (H : G₁) : G₁ := x • H

def Verify (H : G₁) (pk : G₂) (sig : G₁) : Prop :=
  S.pair sig S.source₂.generator = S.pair H pk

/-- Bilinearity transports a scalar between the two arguments. -/
theorem pairing_scalar_swap (x : ZMod q) (H : G₁) (Q : G₂) :
    S.pair (x • H) Q = S.pair H (x • Q) := by
  rw [S.pair.map_smul₂, (S.pair H).map_smul]

/-- Nondegeneracy plus cyclicity derives injectivity; it is not assumed separately. -/
theorem pairing_generator_injective :
    Function.Injective (fun P : G₁ => S.pair P S.source₂.generator) := by
  intro P Q h
  obtain ⟨x, rfl⟩ := S.source₁.generator_bijective.2 P
  obtain ⟨y, rfl⟩ := S.source₁.generator_bijective.2 Q
  simp only [S.pair.map_smul₂] at h
  have he : x = y := smul_left_injective (ZMod q) S.nondegenerate h
  rw [he]

theorem individual_bls_verification (x : ZMod q) (H : G₁) :
    Verify S H (publicKey S x) (sign x H) :=
  pairing_scalar_swap S x H S.source₂.generator

/-- Algebraic uniqueness for a known honestly generated key is not unforgeability. -/
theorem individual_verification_iff (x : ZMod q) (H sig : G₁) :
    Verify S H (publicKey S x) sig ↔ sig = sign x H := by
  constructor
  · intro h
    exact pairing_generator_injective S (h.trans (individual_bls_verification S x H).symm)
  · rintro rfl
    exact individual_bls_verification S x H

variable {ι : Type} (s : Finset ι)

/-- Despite the conventional name, no distinct-message hypothesis is needed. -/
theorem aggregate_bls_distinct_messages (x : ι → ZMod q) (H : ι → G₁) :
    S.pair (∑ i ∈ s, sign (x i) (H i)) S.source₂.generator =
      ∑ i ∈ s, S.pair (H i) (publicKey S (x i)) := by
  rw [S.pair.map_sum₂]
  apply Finset.sum_congr rfl
  intro i hi
  exact individual_bls_verification S (x i) (H i)

theorem aggregate_composition_from_valid_partials (H : ι → G₁) (pk : ι → G₂)
    (sig : ι → G₁) (h : ∀ i ∈ s, Verify S (H i) (pk i) (sig i)) :
    S.pair (∑ i ∈ s, sig i) S.source₂.generator = ∑ i ∈ s, S.pair (H i) (pk i) := by
  rw [S.pair.map_sum₂]
  exact Finset.sum_congr rfl h

theorem aggregate_bls_common_message (x : ι → ZMod q) (H : G₁) :
    Verify S H (∑ i ∈ s, publicKey S (x i)) (∑ i ∈ s, sign (x i) H) := by
  change S.pair _ _ = S.pair H _
  rw [aggregate_bls_distinct_messages S s x (fun _ => H), map_sum]

theorem common_signature_scalar_sum (x : ι → ZMod q) (H : G₁) :
    (∑ i ∈ s, sign (x i) H) = (∑ i ∈ s, x i) • H := by
  simp only [sign, Finset.sum_smul]

/-- Any accepted individual equations compose for a common message as well. -/
theorem common_message_composition (H : G₁) (pk : ι → G₂) (sig : ι → G₁)
    (h : ∀ i ∈ s, Verify S H (pk i) (sig i)) :
    Verify S H (∑ i ∈ s, pk i) (∑ i ∈ s, sig i) := by
  change S.pair _ _ = S.pair H _
  rw [aggregate_composition_from_valid_partials S s (fun _ => H) pk sig h, map_sum]

/-- The witness is computed from the public key, not the honest secret scalar. -/
theorem bls_rogue_key_vulnerability (honest : G₂) (z : ZMod q) (H : G₁) :
    ∃ bad : G₂, bad = publicKey S z - honest ∧ honest + bad = publicKey S z ∧
      Verify S H (honest + bad) (sign z H) := by
  refine ⟨publicKey S z - honest, rfl, ?_, ?_⟩
  · abel
  · have he : honest + (publicKey S z - honest) = publicKey S z := by abel
    rw [he]
    exact individual_bls_verification S z H

/-- Both altered components fail, yet their aggregate passes. -/
theorem bls_error_cancellation_counterexample (H₁ H₂ : G₁) (pk₁ pk₂ : G₂)
    (sig₁ sig₂ δ : G₁) (h₁ : Verify S H₁ pk₁ sig₁) (h₂ : Verify S H₂ pk₂ sig₂)
    (hδ : δ ≠ 0) :
    ¬ Verify S H₁ pk₁ (sig₁ + δ) ∧ ¬ Verify S H₂ pk₂ (sig₂ - δ) ∧
    (sig₁ + δ) + (sig₂ - δ) = sig₁ + sig₂ ∧
    S.pair ((sig₁ + δ) + (sig₂ - δ)) S.source₂.generator =
      S.pair H₁ pk₁ + S.pair H₂ pk₂ := by
  have sum : (sig₁ + δ) + (sig₂ - δ) = sig₁ + sig₂ := by abel
  refine ⟨?_, ?_, sum, ?_⟩
  · intro h
    have he := pairing_generator_injective S (h.trans h₁.symm)
    exact hδ (add_left_cancel (he.trans (add_zero sig₁).symm))
  · intro h
    have he := pairing_generator_injective S (h.trans h₂.symm)
    have hz : -δ = 0 := add_left_cancel (by
      simpa only [sub_eq_add_neg] using he.trans (add_zero sig₂).symm)
    exact hδ (neg_eq_zero.mp hz)
  · rw [sum, S.pair.map_add₂, h₁, h₂]

/-- A reindexing permutes all matching message/key/signature entries together. -/
theorem aggregate_permutation {n : ℕ} (perm : Equiv.Perm (Fin n))
    (sig H : Fin n → G₁) (pk : Fin n → G₂) :
    (∑ i, sig (perm i)) = (∑ i, sig i) ∧
    (∑ i, S.pair (H (perm i)) (pk (perm i))) = ∑ i, S.pair (H i) (pk i) := by
  exact ⟨Equiv.sum_comp perm sig, Equiv.sum_comp perm (fun i => S.pair (H i) (pk i))⟩

theorem zero_secret_contribution (H : G₁) :
    sign (0 : ZMod q) H = 0 ∧ publicKey S 0 = 0 := by simp [sign, publicKey]

theorem one_participant (x : Fin 1 → ZMod q) (H : Fin 1 → G₁) :
    S.pair (∑ i, sign (x i) (H i)) S.source₂.generator =
      S.pair (H 0) (publicKey S (x 0)) := by
  simpa using aggregate_bls_distinct_messages S Finset.univ x H

theorem two_participants (x₁ x₂ : ZMod q) (H₁ H₂ : G₁) :
    S.pair (sign x₁ H₁ + sign x₂ H₂) S.source₂.generator =
      S.pair H₁ (publicKey S x₁) + S.pair H₂ (publicKey S x₂) := by
  rw [S.pair.map_add₂]
  rw [individual_bls_verification S x₁ H₁, individual_bls_verification S x₂ H₂]
/-- The semantic obligations exported to the master suite for every admissible setup. -/
structure GroupProperties : Prop where
  injective_pair : Function.Injective (fun P : G₁ => S.pair P S.source₂.generator)
  individual : ∀ x H, Verify S H (publicKey S x) (sign x H)
  aggregate : ∀ (ι : Type) (s : Finset ι) (x : ι → ZMod q) (H : ι → G₁),
    S.pair (∑ i ∈ s, sign (x i) (H i)) S.source₂.generator =
      ∑ i ∈ s, S.pair (H i) (publicKey S (x i))
  common : ∀ (ι : Type) (s : Finset ι) (x : ι → ZMod q) (H : G₁),
    Verify S H (∑ i ∈ s, publicKey S (x i)) (∑ i ∈ s, sign (x i) H)
  composition : ∀ (ι : Type) (s : Finset ι) (H : ι → G₁) (pk : ι → G₂) (sig : ι → G₁),
    (∀ i ∈ s, Verify S (H i) (pk i) (sig i)) →
    S.pair (∑ i ∈ s, sig i) S.source₂.generator = ∑ i ∈ s, S.pair (H i) (pk i)
  rogue : ∀ honest z H, ∃ bad : G₂, bad = publicKey S z - honest ∧
    honest + bad = publicKey S z ∧ Verify S H (honest + bad) (sign z H)
  cancellation : ∀ H₁ H₂ pk₁ pk₂ sig₁ sig₂ δ,
    Verify S H₁ pk₁ sig₁ → Verify S H₂ pk₂ sig₂ → δ ≠ 0 →
    ¬ Verify S H₁ pk₁ (sig₁ + δ) ∧ ¬ Verify S H₂ pk₂ (sig₂ - δ) ∧
    (sig₁ + δ) + (sig₂ - δ) = sig₁ + sig₂ ∧
    S.pair ((sig₁ + δ) + (sig₂ - δ)) S.source₂.generator = S.pair H₁ pk₁ + S.pair H₂ pk₂

theorem group_properties : GroupProperties S where
  injective_pair := pairing_generator_injective S
  individual := individual_bls_verification S
  aggregate := fun _ => aggregate_bls_distinct_messages S
  common := fun _ => aggregate_bls_common_message S
  composition := fun _ => aggregate_composition_from_valid_partials S
  rogue := bls_rogue_key_vulnerability S
  cancellation := bls_error_cancellation_counterexample S

end Group

/-- Shared polynomial identity, specialized independently over real and modular scalars. -/
theorem ring_bilinear_bridge {R : Type} [CommRing R] {ι : Type} (s : Finset ι)
    (x H : ι → R) (g : R) :
    (∑ i ∈ s, x i * H i) * g = ∑ i ∈ s, H i * (x i * g) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem bridge_to_existing_real_bls {ι : Type} (s : Finset ι)
    (setup : CryptoBLSSignatureAggregation.BLSSetup) (x H : ι → ℝ) :
    CryptoBLSSignatureAggregation.pairing
      (∑ i ∈ s, CryptoBLSSignatureAggregation.sign (x i) (H i)) setup.g2 =
    ∑ i ∈ s, CryptoBLSSignatureAggregation.pairing (H i)
      (CryptoBLSSignatureAggregation.publicKey (x i) setup) :=
  ring_bilinear_bridge s x H setup.g2

/-- A concrete witness, using the cyclic setup already supplied by module 143. -/
def ConsistencyModel (q : ℕ) [Fact (Nat.Prime q)] :
    PairingSetup q (ZMod q) (ZMod q) (ZMod q) where
  source₁ := CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup
  source₂ := CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup
  target := CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup
  pair := LinearMap.mul (ZMod q) (ZMod q)
  nondegenerate := by simp [CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup]

@[simp] theorem consistency_pair (q : ℕ) [Fact (Nat.Prime q)] (a b : ZMod q) :
    (ConsistencyModel q).pair a b = a * b := rfl

theorem consistency_model_exists (q : ℕ) [Fact (Nat.Prime q)] :
    Nonempty (PairingSetup q (ZMod q) (ZMod q) (ZMod q)) := ⟨ConsistencyModel q⟩

theorem bridge_to_modular_bls (q : ℕ) [Fact (Nat.Prime q)] {ι : Type}
    (s : Finset ι) (x H : ι → ZMod q) :
    (ConsistencyModel q).pair (∑ i ∈ s, sign (x i) (H i)) 1 =
      ∑ i ∈ s, (ConsistencyModel q).pair (H i) (publicKey (ConsistencyModel q) (x i)) := by
  simpa [sign, publicKey, ConsistencyModel,
    CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup] using ring_bilinear_bridge s x H 1

/-- Universal group guarantees together with a concrete model and the shared ring bridge. -/
structure CryptoBLSSignatureAggregationGroupSuite : Prop where
  groups : ∀ (q : ℕ) [Fact (Nat.Prime q)] (G₁ G₂ GT : Type)
    [AddCommGroup G₁] [Module (ZMod q) G₁] [AddCommGroup G₂] [Module (ZMod q) G₂]
    [AddCommGroup GT] [Module (ZMod q) GT] (S : PairingSetup q G₁ G₂ GT), GroupProperties S
  model : ∀ (q : ℕ) [Fact (Nat.Prime q)],
    Nonempty (PairingSetup q (ZMod q) (ZMod q) (ZMod q))
  ring_bridge : ∀ (R : Type) [CommRing R] (ι : Type) (s : Finset ι) (x H : ι → R) (g : R),
    (∑ i ∈ s, x i * H i) * g = ∑ i ∈ s, H i * (x i * g)

theorem crypto_bls_group_master_suite : CryptoBLSSignatureAggregationGroupSuite where
  groups := fun _ _ _ _ _ _ _ _ _ _ _ => group_properties
  model := consistency_model_exists
  ring_bridge := fun _ _ _ => ring_bilinear_bridge

end CryptoBLSSignatureAggregationGroup
