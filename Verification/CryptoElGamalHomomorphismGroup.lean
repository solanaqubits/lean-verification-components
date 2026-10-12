/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoElGamalEncryption
import Verification.CryptoSchnorrMultiSignaturesMuSigGroup

/-!
# Group ElGamal: weighted homomorphism, rerandomization and malleability

Plaintexts are group elements. Exponential encoding returns a group point on
decryption; uniqueness of its scalar representation is not an efficient decoder.
Randomness is an explicit scalar input; no distributional security is asserted.
-/
namespace CryptoElGamalHomomorphismGroup

open scoped BigOperators
open CryptoSchnorrMultiSignaturesMuSigGroup (CyclicSetup)

abbrev Ciphertext (H : Type*) := H × H

section Module
variable {R H : Type*} [CommRing R] [AddCommGroup H] [Module R H]

def enc (G Y : H) (r : R) (M : H) : Ciphertext H := (r • G, M + r • Y)

def dec (x : R) (c : Ciphertext H) : H := c.2 - x • c.1

/-- Completeness uses the module laws and a matching public/secret key. -/
theorem elgamal_group_decryption_correctness (G Y : H) (x r : R) (M : H)
    (hY : Y = x • G) : dec x (enc G Y r M) = M := by
  subst Y
  simp only [dec, enc, smul_smul, mul_comm r x, add_sub_cancel_right]

theorem elgamal_add_homomorphism (G Y : H) (r₁ r₂ : R) (M₁ M₂ : H) :
    enc G Y r₁ M₁ + enc G Y r₂ M₂ = enc G Y (r₁ + r₂) (M₁ + M₂) := by
  apply Prod.ext
  · simp [enc, add_smul]
  · simp only [enc, Prod.snd_add, add_smul]
    abel

theorem elgamal_smul_homomorphism (G Y : H) (a r : R) (M : H) :
    a • enc G Y r M = enc G Y (a * r) (a • M) := by
  apply Prod.ext <;> simp [enc, smul_add, smul_smul]

/-- The underlying module identity includes arbitrary group plaintexts. -/
theorem module_weighted_sum {ι : Type*} (s : Finset ι) (G Y : H)
    (a r : ι → R) (M : ι → H) :
    (∑ i ∈ s, a i • enc G Y (r i) (M i)) =
      enc G Y (∑ i ∈ s, a i * r i) (∑ i ∈ s, a i • M i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    apply Prod.ext <;> simp [enc]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [ih, elgamal_smul_homomorphism, elgamal_add_homomorphism]

theorem elgamal_rerandomization_algebraic (G Y : H) (r t : R) (M : H) :
    enc G Y r M + enc G Y t 0 = enc G Y (r + t) M := by
  simpa using elgamal_add_homomorphism G Y r t M 0

/-- Decryption itself is additive, including on ciphertexts not produced by enc. -/
theorem decryption_add (x : R) (c d : Ciphertext H) :
    dec x (c + d) = dec x c + dec x d := by
  simp only [dec, Prod.fst_add, Prod.snd_add, smul_add]
  abel

theorem decryption_smul (x a : R) (c : Ciphertext H) :
    dec x (a • c) = a • dec x c := by
  change a • c.2 - x • (a • c.1) = a • (c.2 - x • c.1)
  simp only [smul_sub, smul_smul, mul_comm x a]

theorem elgamal_malleability_shift (G : H) (x Δ : R) (c : Ciphertext H) :
    dec x (c.1, c.2 + Δ • G) = dec x c + Δ • G := by
  simp only [dec]
  abel

theorem weighted_permutation {n : ℕ} (perm : Equiv.Perm (Fin n))
    (a : Fin n → R) (c : Fin n → Ciphertext H) :
    (∑ i, a (perm i) • c (perm i)) = ∑ i, a i • c i :=
  Equiv.sum_comp perm (fun i => a i • c i)

end Module

section Group
variable {q : ℕ} [Fact (Nat.Prime q)]
variable {H : Type} [AddCommGroup H] [Module (ZMod q) H]
variable (S : CyclicSetup q H)

def publicKey (x : ZMod q) : H := x • S.generator

def enc_scalar (Y : H) (r m : ZMod q) : Ciphertext H :=
  enc S.generator Y r (m • S.generator)

theorem elgamal_scalar_decryption_correctness (Y : H) (x r m : ZMod q)
    (hY : Y = publicKey S x) : dec x (enc_scalar S Y r m) = m • S.generator :=
  elgamal_group_decryption_correctness S.generator Y x r (m • S.generator) hY

/-- No computable or efficient discrete-logarithm inverse is supplied. -/
theorem elgamal_scalar_uniqueness (x m₁ m₂ : ZMod q) (c : Ciphertext H)
    (h₁ : dec x c = m₁ • S.generator) (h₂ : dec x c = m₂ • S.generator) :
    m₁ = m₂ := S.generator_bijective.1 (h₁.symm.trans h₂)

theorem elgamal_scalar_representation (x : ZMod q) (c : Ciphertext H) :
    ∃! m : ZMod q, dec x c = m • S.generator := by
  obtain ⟨m, hm⟩ := S.generator_bijective.2 (dec x c)
  exact ⟨m, hm.symm, fun y hy => S.generator_bijective.1 (hy.symm.trans hm.symm)⟩

theorem elgamal_weighted_sum_homomorphism {ι : Type} (s : Finset ι) (Y : H)
    (a r m : ι → ZMod q) :
    (∑ i ∈ s, a i • enc_scalar S Y (r i) (m i)) =
      enc_scalar S Y (∑ i ∈ s, a i * r i) (∑ i ∈ s, a i * m i) := by
  simp only [enc_scalar]
  rw [module_weighted_sum]
  simp only [smul_smul, Finset.sum_smul]

theorem weighted_decryption_correctness {ι : Type} (s : Finset ι) (x : ZMod q)
    (a r m : ι → ZMod q) :
    dec x (∑ i ∈ s, a i • enc_scalar S (publicKey S x) (r i) (m i)) =
      (∑ i ∈ s, a i * m i) • S.generator := by
  rw [elgamal_weighted_sum_homomorphism]
  exact elgamal_scalar_decryption_correctness S _ _ _ _ rfl

theorem elgamal_malleability_nonzero (x Δ : ZMod q) (c : Ciphertext H) (hΔ : Δ ≠ 0) :
    Δ • S.generator ≠ 0 ∧ dec x (c.1, c.2 + Δ • S.generator) ≠ dec x c := by
  have hn : Δ • S.generator ≠ 0 := by
    intro h
    exact hΔ (S.generator_bijective.1 (h.trans (zero_smul (ZMod q) S.generator).symm))
  refine ⟨hn, ?_⟩
  rw [elgamal_malleability_shift]
  intro he
  exact hn (add_left_cancel (he.trans (add_zero (dec x c)).symm))

/-- Valid encrypted messages can be shifted without using the secret key. -/
theorem shifted_encryption (Y : H) (r m Δ : ZMod q) :
    ((enc_scalar S Y r m).1, (enc_scalar S Y r m).2 + Δ • S.generator) =
      enc_scalar S Y r (m + Δ) := by
  apply Prod.ext
  · rfl
  · simp only [enc_scalar, enc, add_smul]
    abel

structure GroupProperties : Prop where
  correct : ∀ (Y : H) (x r : ZMod q) (M : H), Y = publicKey S x → dec x (enc S.generator Y r M) = M
  scalar_correct : ∀ (Y : H) (x r m : ZMod q), Y = publicKey S x →
    dec x (enc_scalar S Y r m) = m • S.generator
  unique : ∀ (x : ZMod q) (c : Ciphertext H), ∃! m : ZMod q, dec x c = m • S.generator
  weighted : ∀ (ι : Type) (s : Finset ι) Y (a r m : ι → ZMod q),
    (∑ i ∈ s, a i • enc_scalar S Y (r i) (m i)) =
      enc_scalar S Y (∑ i ∈ s, a i * r i) (∑ i ∈ s, a i * m i)
  rerandomize : ∀ Y (r t : ZMod q) M,
    enc S.generator Y r M + enc S.generator Y t 0 = enc S.generator Y (r + t) M
  shift : ∀ (x Δ : ZMod q) (c : Ciphertext H),
    dec x (c.1, c.2 + Δ • S.generator) = dec x c + Δ • S.generator
  nontrivial_shift : ∀ (x Δ : ZMod q) (c : Ciphertext H), Δ ≠ 0 →
    Δ • S.generator ≠ 0 ∧ dec x (c.1, c.2 + Δ • S.generator) ≠ dec x c

theorem group_properties : GroupProperties S where
  correct := elgamal_group_decryption_correctness S.generator
  scalar_correct := elgamal_scalar_decryption_correctness S
  unique := elgamal_scalar_representation S
  weighted := fun _ => elgamal_weighted_sum_homomorphism S
  rerandomize := elgamal_rerandomization_algebraic S.generator
  shift := elgamal_malleability_shift S.generator
  nontrivial_shift := elgamal_malleability_nonzero S
end Group

/-- Polynomial bridge, independently instantiated over reals and modular scalars. -/
theorem ring_elgamal_bridge {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι)
    (a r M : ι → R) (g x : R) :
    (∑ i ∈ s, a i * (M i + r i * (x * g))) - x * (∑ i ∈ s, a i * (r i * g)) =
      ∑ i ∈ s, a i * M i := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem bridge_to_existing_real_elgamal {ι : Type} (s : Finset ι)
    (setup : CryptoElGamalEncryption.ElGamalSetup) (a r M : ι → ℝ) (x : ℝ) :
    CryptoElGamalEncryption.decrypt x
      ⟨∑ i ∈ s, a i * (CryptoElGamalEncryption.encrypt setup
          (CryptoElGamalEncryption.publicKey setup x) (r i) (M i)).c1,
       ∑ i ∈ s, a i * (CryptoElGamalEncryption.encrypt setup
          (CryptoElGamalEncryption.publicKey setup x) (r i) (M i)).c2⟩ =
      ∑ i ∈ s, a i * M i := ring_elgamal_bridge s a r M setup.g x

def ConsistencyModel (q : ℕ) [Fact (Nat.Prime q)] : CyclicSetup q (ZMod q) :=
  CryptoSchnorrMultiSignaturesMuSigGroup.scalarSetup

theorem consistency_model_exists (q : ℕ) [Fact (Nat.Prime q)] :
    Nonempty (CyclicSetup q (ZMod q)) := ⟨ConsistencyModel q⟩

theorem bridge_to_modular_elgamal (q : ℕ) [Fact (Nat.Prime q)] {ι : Type}
    (s : Finset ι) (a r M : ι → ZMod q) (x : ZMod q) :
    (∑ i ∈ s, a i * (M i + r i * (x * (ConsistencyModel q).generator))) -
      x * (∑ i ∈ s, a i * (r i * (ConsistencyModel q).generator)) =
      ∑ i ∈ s, a i * M i := ring_elgamal_bridge s a r M _ x

structure CryptoElGamalHomomorphismGroupSuite : Prop where
  groups : ∀ (q : ℕ) [Fact (Nat.Prime q)] (H : Type) [AddCommGroup H]
    [Module (ZMod q) H] (S : CyclicSetup q H), GroupProperties S
  model : ∀ (q : ℕ) [Fact (Nat.Prime q)], Nonempty (CyclicSetup q (ZMod q))
  ring_bridge : ∀ (R : Type) [CommRing R] (ι : Type) (s : Finset ι) (a r M : ι → R) (g x : R),
    (∑ i ∈ s, a i * (M i + r i * (x * g))) - x * (∑ i ∈ s, a i * (r i * g)) =
      ∑ i ∈ s, a i * M i

theorem crypto_elgamal_group_master_suite : CryptoElGamalHomomorphismGroupSuite where
  groups := fun _ _ _ _ _ => group_properties
  model := consistency_model_exists
  ring_bridge := fun _ _ _ => ring_elgamal_bridge

end CryptoElGamalHomomorphismGroup
