import Verification.CryptoSchnorrMultiSignaturesMuSigGroup

open CryptoSchnorrMultiSignaturesMuSigGroup
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (2 ≥ 2) := ⟨by decide⟩

def contexts : HashContexts 7 2 (ZMod 7) Unit :=
  ⟨fun _ X => X + 1, fun X R _ => X + R + 1⟩
def keys : Fin 2 → ZMod 7 := ![2, 3]
def nonces : Fin 2 → ZMod 7 := ![4, 5]

example : Verify (1 : ZMod 7) (aggregate_pubkey contexts keys) (aggregate_nonce nonces)
    (challenge contexts keys nonces ())
    (aggregate_sig (fun i => partial_sig (nonces i) (keys i) (agg_coeff contexts keys i)
      (challenge contexts keys nonces ()))) := by
  exact musig_group_aggregation_soundness scalarSetup contexts keys nonces keys nonces _ ()
    (fun _ => by simp [scalarSetup]) (fun _ => by simp [scalarSetup]) (fun _ => rfl)

example : (aggregate_pubkey contexts keys : ZMod 7) = 4 := by decide

example (n : ℕ) (L N : Fin n → ZMod 7) (s : Fin n → ZMod 7)
    (H : HashContexts 7 n (ZMod 7) Unit) (c : ZMod 7)
    (h : ∀ i, s i • (1 : ZMod 7) = N i + (c * agg_coeff H L i) • L i) :
    Verify 1 (aggregate_pubkey H L) (aggregate_nonce N) c (aggregate_sig s) :=
  partial_to_aggregate_composition 1 H L N s c h

example : aggregate_pubkey contexts (fun _ => (2 : ZMod 7)) = 5 := by decide

example : agg_coeff contexts (fun _ => (6 : ZMod 7)) 0 = 0 := by decide
example : aggregate_pubkey contexts (fun _ => (6 : ZMod 7)) = 0 := by decide

example (X : ZMod 7) : X + -X = 0 := naive_key_cancellation X
example (r c : ZMod 7) : Verify 1 0 (r • (1 : ZMod 7)) c r :=
  zero_key_verification 1 r c

example (honest z r : ZMod 7) (H : ZMod 7 → ZMod 7 → Unit → ZMod 7) :
    ∃ bad, honest + bad = z • (1 : ZMod 7) ∧
      Verify 1 (honest + bad) (r • (1 : ZMod 7)) (H (honest + bad) (r • (1 : ZMod 7)) ())
        (r + H (honest + bad) (r • (1 : ZMod 7)) () * z) :=
  rogue_key_naive_aggregation_vulnerability 1 honest H () z r

example (g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c : ZMod 7) :
    (partial_sig (r₀₀ + b * r₀₁) x₀ a₀ c + partial_sig (r₁₀ + b * r₁₁) x₁ a₁ c) • g =
      ((r₀₀ • g + r₁₀ • g) + b • (r₀₁ • g + r₁₁ • g)) +
        c • (a₀ • (x₀ • g) + a₁ • (x₁ • g)) :=
  bridge_to_scalar_musig g a₀ a₁ x₀ x₁ r₀₀ r₀₁ r₁₀ r₁₁ b c

example : CryptoSchnorrMultiSignaturesMuSigGroupSuite := crypto_schnorr_musig_group_master_suite
