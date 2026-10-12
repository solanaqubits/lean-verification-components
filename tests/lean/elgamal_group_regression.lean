import Verification.CryptoElGamalHomomorphismGroup

open CryptoElGamalHomomorphismGroup
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev S := ConsistencyModel 7
private abbrev Y : ZMod 7 := publicKey S 2

example : Nonempty (CryptoSchnorrMultiSignaturesMuSigGroup.CyclicSetup 7 (ZMod 7)) :=
  consistency_model_exists 7

example : dec (2 : ZMod 7) (enc S.generator Y (3 : ZMod 7) (5 : ZMod 7)) = 5 :=
  elgamal_group_decryption_correctness S.generator Y 2 3 5 rfl

example : dec (2 : ZMod 7) (enc_scalar S Y 3 5) = 5 • S.generator :=
  elgamal_scalar_decryption_correctness S Y 2 3 5 rfl

example (c : Ciphertext (ZMod 7)) (m n : ZMod 7)
    (hm : dec (2 : ZMod 7) c = m • S.generator)
    (hn : dec (2 : ZMod 7) c = n • S.generator) : m = n :=
  elgamal_scalar_uniqueness S 2 m n c hm hn

example (a r m : ℕ → ZMod 7) :
    (∑ i ∈ (∅ : Finset ℕ), a i • enc_scalar S Y (r i) (m i)) = enc_scalar S Y 0 0 := by
  simpa using elgamal_weighted_sum_homomorphism S (∅ : Finset ℕ) Y a r m

example (a r m : ℕ → ZMod 7) :
    (∑ i ∈ ({0} : Finset ℕ), a i • enc_scalar S Y (r i) (m i)) =
      enc_scalar S Y (a 0 * r 0) (a 0 * m 0) := by
  simpa using elgamal_weighted_sum_homomorphism S ({0} : Finset ℕ) Y a r m

example (a r m : Fin 2 → ZMod 7) :
    dec (2 : ZMod 7) (∑ i, a i • enc_scalar S Y (r i) (m i)) =
      (∑ i, a i * m i) • S.generator := weighted_decryption_correctness S Finset.univ 2 a r m

example (perm : Equiv.Perm (Fin 2)) (a : Fin 2 → ZMod 7)
    (c : Fin 2 → Ciphertext (ZMod 7)) :
    (∑ i, a (perm i) • c (perm i)) = ∑ i, a i • c i := weighted_permutation perm a c

example (c : Ciphertext (ZMod 7)) : (0 : ZMod 7) • c = 0 := by
  apply Prod.ext <;> simp

example (a r : ZMod 7) (M : ZMod 7) :
    (-a) • enc S.generator Y r M = enc S.generator Y ((-a) * r) ((-a) • M) :=
  elgamal_smul_homomorphism S.generator Y (-a) r M

example (r t M : ZMod 7) :
    enc S.generator Y r M + enc S.generator Y t 0 = enc S.generator Y (r + t) M :=
  elgamal_rerandomization_algebraic S.generator Y r t M

example (c : Ciphertext (ZMod 7)) :
    (1 : ZMod 7) • S.generator ≠ 0 ∧
    dec (2 : ZMod 7) (c.1, c.2 + (1 : ZMod 7) • S.generator) ≠ dec (2 : ZMod 7) c :=
  elgamal_malleability_nonzero S 2 1 c one_ne_zero

-- Reduction modulo 7 is observable; this is not an unbounded integer sum.
example : dec (2 : ZMod 7) (enc_scalar S Y 3 5 + enc_scalar S Y 4 4) = 2 := by decide
example : dec (2 : ZMod 7) ((-1 : ZMod 7) • enc_scalar S Y 3 5) = 2 := by decide
example : (enc_scalar S Y 3 5).2 + 1 = (enc_scalar S Y 3 6).2 := by decide

example (s : Finset ℕ) (a r M : ℕ → ZMod 7) :
    (∑ i ∈ s, a i * (M i + r i * (2 * S.generator))) -
      2 * (∑ i ∈ s, a i * (r i * S.generator)) = ∑ i ∈ s, a i * M i :=
  bridge_to_modular_elgamal 7 s a r M 2

example (s : Finset ℕ) (a r M : ℕ → ℝ) (g x : ℝ) :
    (∑ i ∈ s, a i * (M i + r i * (x * g))) - x * (∑ i ∈ s, a i * (r i * g)) =
      ∑ i ∈ s, a i * M i := ring_elgamal_bridge s a r M g x

example : CryptoElGamalHomomorphismGroupSuite := crypto_elgamal_group_master_suite
#print axioms crypto_elgamal_group_master_suite
