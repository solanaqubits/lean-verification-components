import Verification.CryptoBLSSignatureAggregationGroup

open CryptoBLSSignatureAggregationGroup
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev S := ConsistencyModel 7

example : Nonempty (PairingSetup 7 (ZMod 7) (ZMod 7) (ZMod 7)) :=
  consistency_model_exists 7

example : Verify S 3 (publicKey S 2) (sign (2 : ZMod 7) (3 : ZMod 7)) :=
  individual_bls_verification S 2 3

example : S.pair (∑ _i : Fin 1, sign (2 : ZMod 7) (3 : ZMod 7)) S.source₂.generator =
    S.pair 3 (publicKey S 2) := one_participant S (fun _ => 2) (fun _ => 3)

example : S.pair (sign (2 : ZMod 7) (3 : ZMod 7) + sign (4 : ZMod 7) (5 : ZMod 7)) S.source₂.generator =
    S.pair 3 (publicKey S 2) + S.pair 5 (publicKey S 4) := two_participants S 2 4 3 5

-- Repeated keys and repeated message points are allowed by algebraic completeness.
example : Verify S 3 (∑ _i : Fin 2, publicKey S 2) (∑ _i : Fin 2, sign (2 : ZMod 7) (3 : ZMod 7)) :=
  aggregate_bls_common_message S Finset.univ (fun _ => 2) 3

example : sign (0 : ZMod 7) (3 : ZMod 7) = 0 ∧ publicKey S 0 = 0 :=
  zero_secret_contribution S 3

example (perm : Equiv.Perm (Fin 2)) (sig H pk : Fin 2 → ZMod 7) :
    (∑ i, sig (perm i)) = ∑ i, sig i := (aggregate_permutation S perm sig H pk).1

example : ∃ bad : ZMod 7, bad = publicKey S 5 - 2 ∧ 2 + bad = publicKey S 5 ∧
    Verify S 3 (2 + bad) (sign (5 : ZMod 7) 3) := bls_rogue_key_vulnerability S 2 5 3

example : ¬ Verify S 3 (publicKey S 2) (sign (2 : ZMod 7) (3 : ZMod 7) + 1) ∧
    ¬ Verify S 5 (publicKey S 4) (sign (4 : ZMod 7) (5 : ZMod 7) - 1) ∧
    (sign (2 : ZMod 7) (3 : ZMod 7) + 1) + (sign (4 : ZMod 7) (5 : ZMod 7) - 1) =
      sign (2 : ZMod 7) (3 : ZMod 7) + sign (4 : ZMod 7) (5 : ZMod 7) ∧
    S.pair ((sign (2 : ZMod 7) (3 : ZMod 7) + 1) + (sign (4 : ZMod 7) (5 : ZMod 7) - 1)) S.source₂.generator =
      S.pair 3 (publicKey S 2) + S.pair 5 (publicKey S 4) :=
  bls_error_cancellation_counterexample S 3 5 (publicKey S 2) (publicKey S 4)
    (sign (2 : ZMod 7) (3 : ZMod 7)) (sign (4 : ZMod 7) (5 : ZMod 7)) 1
    (individual_bls_verification S 2 3) (individual_bls_verification S 4 5) one_ne_zero

-- Explicit finite-field arithmetic checks the concrete interpretation independently.
example : (2 * 3 + 1 : ZMod 7) = 0 ∧ (4 * 5 - 1 : ZMod 7) = 5 ∧
    (2 * 3 + 4 * 5 : ZMod 7) = 5 := by decide

example (s : Finset ℕ) (x H : ℕ → ZMod 7) :
    S.pair (∑ i ∈ s, sign (x i) (H i)) 1 =
    ∑ i ∈ s, S.pair (H i) (publicKey S (x i)) := bridge_to_modular_bls 7 s x H

example (s : Finset ℕ) (setup : CryptoBLSSignatureAggregation.BLSSetup) (x H : ℕ → ℝ) :
    CryptoBLSSignatureAggregation.pairing
      (∑ i ∈ s, CryptoBLSSignatureAggregation.sign (x i) (H i)) setup.g2 =
    ∑ i ∈ s, CryptoBLSSignatureAggregation.pairing (H i)
      (CryptoBLSSignatureAggregation.publicKey (x i) setup) := bridge_to_existing_real_bls s setup x H

example : CryptoBLSSignatureAggregationGroupSuite := crypto_bls_group_master_suite
#print axioms crypto_bls_group_master_suite
