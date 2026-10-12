/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Verification.CryptoMuSig2Aggregation
import Verification.DistributedCoordinatedAttackImpossibility

/-!
# Finite-group Schnorr aggregation

Algebraic completeness, not unforgeability or an interactive MuSig2 protocol.
An ordered key vector and two separately typed deterministic functions supply
coefficients and challenges. No security property of those functions is assumed.
The scalar bridge specializes one ring identity independently to real and modular
arithmetic; it does not assert a homomorphism from the reals to a finite field.
-/

namespace CryptoSchnorrMultiSignaturesMuSigGroup

open scoped BigOperators

/-- Algebraic core common to the real two-nonce model and modular arithmetic. -/
theorem two_nonce_ring_identity {R : Type*} [CommRing R]
    (g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c : R) :
    ((r₀₀ + b * r₀₁ + c * a₀ * x₀) + (r₁₀ + b * r₁₁ + c * a₁ * x₁)) * g =
      ((r₀₀ * g + r₁₀ * g) + b * (r₀₁ * g + r₁₁ * g)) +
        c * (a₀ * (x₀ * g) + a₁ * (x₁ * g)) := by ring

section Generic
variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

/-- Completeness needs only the module laws, not cyclicity or hardness. -/
theorem partial_module_identity (G : H) (r x a c : R) :
    (r + c * a * x) • G = r • G + (c * a) • (x • G) := by
  rw [add_smul, mul_smul]

/-- Accepted partial equations with common coefficients and challenge assemble. -/
theorem assemble_module_identity {ι : Type*} [Fintype ι]
    (G : H) (L N : ι → H) (a s : ι → R) (c : R)
    (h : ∀ i, s i • G = N i + (c * a i) • L i) :
    (∑ i, s i) • G = (∑ i, N i) + c • (∑ i, a i • L i) := by
  rw [Finset.sum_smul, Finset.smul_sum]
  simp_rw [h, mul_smul]
  exact Finset.sum_add_distrib
end Generic

section Group
variable {q : ℕ} [Fact (Nat.Prime q)]
variable {𝔾 : Type} [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]

/-- Explicit cyclic prime-order group interface; no efficient inverse is supplied. -/
structure CyclicSetup (q : ℕ) (𝔾 : Type) [Fact (Nat.Prime q)]
    [AddCommGroup 𝔾] [Module (ZMod q) 𝔾] where
  generator : 𝔾
  generator_bijective : Function.Bijective (fun x : ZMod q => x • generator)

theorem scalar_action_injective (setup : CyclicSetup q 𝔾) :
    Function.Injective (fun x : ZMod q => x • setup.generator) :=
  setup.generator_bijective.1

theorem unique_scalar_representation (setup : CyclicSetup q 𝔾) (X : 𝔾) :
    ∃! x : ZMod q, x • setup.generator = X := by
  obtain ⟨x, hx⟩ := setup.generator_bijective.2 X
  exact ⟨x, hx, fun y hy => setup.generator_bijective.1 (hy.trans hx.symm)⟩

theorem generator_ne_zero (setup : CyclicSetup q 𝔾) : setup.generator ≠ 0 := by
  intro h
  have heq : (0 : ZMod q) = 1 := setup.generator_bijective.1 (by simp [h])
  exact zero_ne_one heq

/-- A vector retains participant order and repeated keys. -/
abbrev PublicKeys (n : ℕ) := Fin n → 𝔾

/-- Distinct interfaces for aggregation and message challenge contexts.
These are abstract functions, not a hash implementation or random oracle. -/
structure HashContexts (q n : ℕ) (𝔾 Msg : Type) where
  aggregation : (Fin n → 𝔾) → 𝔾 → ZMod q
  signature : 𝔾 → 𝔾 → Msg → ZMod q

variable {n : ℕ} {Msg : Type}

def agg_coeff (H : HashContexts q n 𝔾 Msg) (L : PublicKeys (𝔾 := 𝔾) n)
    (i : Fin n) : ZMod q := H.aggregation L (L i)

def aggregate_pubkey (H : HashContexts q n 𝔾 Msg) (L : PublicKeys (𝔾 := 𝔾) n) : 𝔾 :=
  ∑ i, agg_coeff H L i • L i

def aggregate_nonce (N : Fin n → 𝔾) : 𝔾 := ∑ i, N i

def partial_sig (r x a c : ZMod q) : ZMod q := r + c * a * x

def aggregate_sig (s : Fin n → ZMod q) : ZMod q := ∑ i, s i

def challenge (H : HashContexts q n 𝔾 Msg) (L N : Fin n → 𝔾) (m : Msg) : ZMod q :=
  H.signature (aggregate_pubkey H L) (aggregate_nonce N) m

def Verify (G X N : 𝔾) (c s : ZMod q) : Prop := s • G = N + c • X

omit [Fact (Nat.Prime q)] in
theorem partial_verify_exact (G : 𝔾) (r x a c : ZMod q) :
    partial_sig r x a c • G = r • G + (c * a) • (x • G) :=
  partial_module_identity G r x a c

omit [Fact (Nat.Prime q)] in
theorem partial_to_aggregate_composition (G : 𝔾) (H : HashContexts q n 𝔾 Msg)
    (L N : Fin n → 𝔾) (s : Fin n → ZMod q) (c : ZMod q)
    (h : ∀ i, s i • G = N i + (c * agg_coeff H L i) • L i) :
    Verify G (aggregate_pubkey H L) (aggregate_nonce N) c (aggregate_sig s) :=
  assemble_module_identity G L N (agg_coeff H L) s c h

/-- The historical name 'soundness' here denotes honest algebraic completeness only. -/
theorem musig_group_aggregation_soundness [Fact (n ≥ 2)] (setup : CyclicSetup q 𝔾)
    (H : HashContexts q n 𝔾 Msg) (L N : Fin n → 𝔾) (x r s : Fin n → ZMod q)
    (m : Msg) (hx : ∀ i, L i = x i • setup.generator)
    (hr : ∀ i, N i = r i • setup.generator)
    (hs : ∀ i, s i = partial_sig (r i) (x i) (agg_coeff H L i) (challenge H L N m)) :
    Verify setup.generator (aggregate_pubkey H L) (aggregate_nonce N)
      (challenge H L N m) (aggregate_sig s) := by
  apply partial_to_aggregate_composition
  intro i
  rw [hs i, partial_verify_exact, ← hr i, ← hx i]

omit [Fact (Nat.Prime q)] in
/-- Cancellation and a valid aggregate response use only the public honest key.
This is a witness against naive aggregation, not a computational security game. -/
theorem rogue_key_naive_aggregation_vulnerability (G honest : 𝔾)
    (Hsig : 𝔾 → 𝔾 → Msg → ZMod q) (m : Msg) (z r : ZMod q) :
    ∃ bad : 𝔾, honest + bad = z • G ∧
      Verify G (honest + bad) (r • G) (Hsig (honest + bad) (r • G) m)
        (r + Hsig (honest + bad) (r • G) m * z) := by
  refine ⟨z • G - honest, ?_, ?_⟩
  · abel
  · have h : honest + (z • G - honest) = z • G := by abel
    simp only [h, Verify, add_smul, mul_smul]

omit [Fact (Nat.Prime q)] in
/-- Zero fixed coefficient removes this term. Rehashing a changed key list is not covered. -/
theorem zero_coefficient_contribution (H : HashContexts q n 𝔾 Msg)
    (L : Fin n → 𝔾) (i : Fin n) (hi : agg_coeff H L i = 0) :
    agg_coeff H L i • L i = 0 := by rw [hi, zero_smul]

omit [Fact (Nat.Prime q)] [AddCommGroup 𝔾] [Module (ZMod q) 𝔾] in
theorem duplicate_keys_equal_coefficients (H : HashContexts q n 𝔾 Msg)
    (L : Fin n → 𝔾) (i j : Fin n) (h : L i = L j) :
    agg_coeff H L i = agg_coeff H L j := by simp only [agg_coeff, h]

omit [Fact (Nat.Prime q)] in
theorem two_participant_key (H : HashContexts q 2 𝔾 Msg) (L : Fin 2 → 𝔾) :
    aggregate_pubkey H L = agg_coeff H L 0 • L 0 + agg_coeff H L 1 • L 1 := by
  simp [aggregate_pubkey, Fin.sum_univ_two]

omit [Fact (Nat.Prime q)] in
theorem duplicate_key_aggregation (H : HashContexts q 2 𝔾 Msg) (X : 𝔾) :
    aggregate_pubkey H (fun _ => X) = (agg_coeff H (fun _ => X) 0 +
      agg_coeff H (fun _ => X) 0) • X := by
  simp [two_participant_key, agg_coeff, add_smul]

omit [Fact (Nat.Prime q)] in
theorem naive_coefficients (H : HashContexts q n 𝔾 Msg) (L : Fin n → 𝔾)
    (h : ∀ i, agg_coeff H L i = 1) : aggregate_pubkey H L = ∑ i, L i := by
  simp [aggregate_pubkey, h]

theorem naive_key_cancellation (X : 𝔾) : X + -X = 0 := add_neg_cancel X

omit [Fact (Nat.Prime q)] in
/-- The equation accepts a zero aggregate key, regardless of the challenge. -/
theorem zero_key_verification (G : 𝔾) (r c : ZMod q) :
    Verify G 0 (r • G) c r := by simp [Verify]

/-- Non-vacuity: the additive finite field with generator one is an instance. -/
def scalarSetup : CyclicSetup q (ZMod q) where
  generator := 1
  generator_bijective := by
    constructor
    · intro a b h
      simpa using h
    · intro x
      exact ⟨x, by simp⟩

omit [Fact (Nat.Prime q)] in
/-- Modular specialization of the same two-nonce ring identity used over the reals. -/
theorem bridge_to_scalar_musig (g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c : ZMod q) :
    (partial_sig (r₀₀ + b * r₀₁) x₀ a₀ c + partial_sig (r₁₀ + b * r₁₁) x₁ a₁ c) • g =
      ((r₀₀ • g + r₁₀ • g) + b • (r₀₁ • g + r₁₁ • g)) +
        c • (a₀ • (x₀ • g) + a₁ • (x₁ • g)) :=
  two_nonce_ring_identity g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c
end Group

/-- Real specialization unfolds exactly the existing scalar module's definitions. -/
theorem bridge_to_existing_real_musig (g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c : ℝ) :
    CryptoMuSig2Aggregation.aggSig
      (CryptoMuSig2Aggregation.partialSig r₀₀ r₀₁ b c a₀ x₀)
      (CryptoMuSig2Aggregation.partialSig r₁₀ r₁₁ b c a₁ x₁) * g =
    CryptoMuSig2Aggregation.aggregateNonce (r₀₀ * g) (r₀₁ * g) (r₁₀ * g) (r₁₁ * g) b +
      c * CryptoMuSig2Aggregation.computeAggKey a₀ a₁ (x₀ * g) (x₁ * g) :=
  two_nonce_ring_identity g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c

/-- Selected group, assembly, attack-witness and bridge guarantees. -/
structure CryptoSchnorrMultiSignaturesMuSigGroupSuite : Prop where
  h_representation : ∀ (q : ℕ) [Fact (Nat.Prime q)] (𝔾 : Type)
    [AddCommGroup 𝔾] [Module (ZMod q) 𝔾] (setup : CyclicSetup q 𝔾) (X : 𝔾),
    ∃! x : ZMod q, x • setup.generator = X
  h_partial : ∀ (q : ℕ) (𝔾 : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]
    (G : 𝔾) (r x a c : ZMod q),
    partial_sig r x a c • G = r • G + (c * a) • (x • G)
  h_assembly : ∀ (q n : ℕ) (𝔾 Msg : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]
    (G : 𝔾) (H : HashContexts q n 𝔾 Msg) (L N : Fin n → 𝔾)
    (s : Fin n → ZMod q) (c : ZMod q),
    (∀ i, s i • G = N i + (c * agg_coeff H L i) • L i) →
    Verify G (aggregate_pubkey H L) (aggregate_nonce N) c (aggregate_sig s)
  h_complete : ∀ (q n : ℕ) [Fact (Nat.Prime q)] [Fact (n ≥ 2)]
    (𝔾 Msg : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾] (setup : CyclicSetup q 𝔾)
    (H : HashContexts q n 𝔾 Msg) (L N : Fin n → 𝔾) (x r s : Fin n → ZMod q) (m : Msg),
    (∀ i, L i = x i • setup.generator) → (∀ i, N i = r i • setup.generator) →
    (∀ i, s i = partial_sig (r i) (x i) (agg_coeff H L i) (challenge H L N m)) →
    Verify setup.generator (aggregate_pubkey H L) (aggregate_nonce N)
      (challenge H L N m) (aggregate_sig s)
  h_rogue : ∀ (q : ℕ) (𝔾 Msg : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]
    (G honest : 𝔾) (Hsig : 𝔾 → 𝔾 → Msg → ZMod q) (m : Msg) (z r : ZMod q),
    ∃ bad : 𝔾, honest + bad = z • G ∧
      Verify G (honest + bad) (r • G) (Hsig (honest + bad) (r • G) m)
        (r + Hsig (honest + bad) (r • G) m * z)
  h_duplicates : ∀ (q : ℕ) (𝔾 Msg : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]
    (H : HashContexts q 2 𝔾 Msg) (X : 𝔾),
    aggregate_pubkey H (fun _ => X) =
      (agg_coeff H (fun _ => X) 0 + agg_coeff H (fun _ => X) 0) • X
  h_zero : ∀ (q : ℕ) (𝔾 : Type) [AddCommGroup 𝔾] [Module (ZMod q) 𝔾]
    (G : 𝔾) (r c : ZMod q), Verify G 0 (r • G) c r
  h_ring_bridge : ∀ (R : Type) [CommRing R] (g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c : R),
    ((r₀₀ + b * r₀₁ + c * a₀ * x₀) + (r₁₀ + b * r₁₁ + c * a₁ * x₁)) * g =
      ((r₀₀ * g + r₁₀ * g) + b * (r₀₁ * g + r₁₁ * g)) +
        c * (a₀ * (x₀ * g) + a₁ * (x₁ * g))

theorem crypto_schnorr_musig_group_master_suite : CryptoSchnorrMultiSignaturesMuSigGroupSuite := {
  h_representation := fun _ _ _ _ _ => unique_scalar_representation
  h_partial := fun _ _ _ _ => partial_verify_exact
  h_assembly := fun _ _ _ _ _ _ => partial_to_aggregate_composition
  h_complete := fun _ _ _ _ _ _ _ _ => musig_group_aggregation_soundness
  h_rogue := fun _ _ _ _ _ => rogue_key_naive_aggregation_vulnerability
  h_duplicates := fun _ _ _ _ _ => duplicate_key_aggregation
  h_zero := fun _ _ _ _ => zero_key_verification
  h_ring_bridge := fun _ _ => two_nonce_ring_identity
}

end CryptoSchnorrMultiSignaturesMuSigGroup
