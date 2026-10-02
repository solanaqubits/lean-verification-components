import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace CryptoSchnorrSignature

/-- A nonzero real parameter, not a cryptographic group implementation. -/
structure SchnorrSetup where
  g : ℝ
  hg_ne : g ≠ 0

def publicKey (setup : SchnorrSetup) (x : ℝ) : ℝ := x * setup.g

def commitment (setup : SchnorrSetup) (k : ℝ) : ℝ := k * setup.g

def response (k c x : ℝ) : ℝ := k + c * x

def verify (setup : SchnorrSetup) (pk R c s : ℝ) : Prop :=
  s * setup.g = R + c * pk

theorem schnorr_completeness (setup : SchnorrSetup) (x k c : ℝ) :
    let pk := publicKey setup x
    let R := commitment setup k
    let s := response k c x
    verify setup pk R c s := by
  dsimp [verify, publicKey, commitment, response]
  ring

/-- Two accepted scalar transcripts with distinct challenges yield a compatible witness. -/
theorem schnorr_special_soundness (setup : SchnorrSetup) (pk R c1 c2 s1 s2 : ℝ)
    (h_diff_c : c1 ≠ c2)
    (h_v1 : verify setup pk R c1 s1)
    (h_v2 : verify setup pk R c2 s2) :
    let extracted_x := (s1 - s2) / (c1 - c2)
    publicKey setup extracted_x = pk := by
  dsimp [verify] at h_v1 h_v2
  dsimp [publicKey]
  have hc_sub : c1 - c2 ≠ 0 := sub_ne_zero.mpr h_diff_c
  have h_diff_eq : (s1 - s2) * setup.g = (c1 - c2) * pk := by
    calc (s1 - s2) * setup.g
      _ = s1 * setup.g - s2 * setup.g := by ring
      _ = (R + c1 * pk) - (R + c2 * pk) := by rw [h_v1, h_v2]
      _ = (c1 - c2) * pk := by ring
  calc ((s1 - s2) / (c1 - c2)) * setup.g
    _ = ((s1 - s2) * setup.g) / (c1 - c2) := by ring
    _ = ((c1 - c2) * pk) / (c1 - c2) := by rw [h_diff_eq]
    _ = pk := mul_div_cancel_left₀ pk hc_sub

/-- Agreement with any original scalar witness for the same public key. -/
theorem schnorr_extracted_witness_eq (setup : SchnorrSetup) (x R c1 c2 s1 s2 : ℝ)
    (h_diff_c : c1 ≠ c2)
    (h_v1 : verify setup (publicKey setup x) R c1 s1)
    (h_v2 : verify setup (publicKey setup x) R c2 s2) :
    (s1 - s2) / (c1 - c2) = x := by
  have h := schnorr_special_soundness setup (publicKey setup x) R c1 c2 s1 s2
    h_diff_c h_v1 h_v2
  exact mul_right_cancel₀ setup.hg_ne h

def simulateCommitment (setup : SchnorrSetup) (pk c s : ℝ) : ℝ :=
  s * setup.g - c * pk

/-- Acceptance of the constructed transcript, not distributional zero knowledge. -/
theorem schnorr_hvzk_simulation (setup : SchnorrSetup) (pk c s : ℝ) :
    let R_sim := simulateCommitment setup pk c s
    verify setup pk R_sim c s := by
  dsimp [verify, simulateCommitment]
  ring

/-- Compatibility name for the original verification equation. -/
abbrev verifySchnorr := verify

def extractSecretKey (s1 s2 e1 e2 : ℝ) : ℝ := (s1 - s2) / (e1 - e2)

/-- Exact scalar-key extraction, retaining the more general original soundness API. -/
theorem schnorr_extract_secret_key_eq (setup : SchnorrSetup) (sk R e1 e2 s1 s2 : ℝ)
    (h_diff : e1 ≠ e2)
    (h1 : verifySchnorr setup (publicKey setup sk) R e1 s1)
    (h2 : verifySchnorr setup (publicKey setup sk) R e2 s2) :
    extractSecretKey s1 s2 e1 e2 = sk :=
  schnorr_extracted_witness_eq setup sk R e1 e2 s1 s2 h_diff h1 h2

def aggregatePublicKeys (pk1 pk2 : ℝ) : ℝ := pk1 + pk2

def aggregateCommitments (R1 R2 : ℝ) : ℝ := R1 + R2

def aggregateResponses (s1 s2 : ℝ) : ℝ := s1 + s2

/-- Addition of two accepted transcripts with a common challenge; not a MuSig protocol. -/
theorem schnorr_multisig_add (setup : SchnorrSetup) (pk1 pk2 R1 R2 e s1 s2 : ℝ)
    (h1 : verifySchnorr setup pk1 R1 e s1)
    (h2 : verifySchnorr setup pk2 R2 e s2) :
    verifySchnorr setup (aggregatePublicKeys pk1 pk2) (aggregateCommitments R1 R2)
      e (aggregateResponses s1 s2) := by
  dsimp [verifySchnorr, verify, aggregatePublicKeys, aggregateCommitments, aggregateResponses] at *
  calc (s1 + s2) * setup.g
    _ = s1 * setup.g + s2 * setup.g := by ring
    _ = (R1 + e * pk1) + (R2 + e * pk2) := by rw [h1, h2]
    _ = (R1 + R2) + e * (pk1 + pk2) := by ring

/-- Forward implication from two individually accepted equations to their unweighted sum. -/
theorem schnorr_batch_verify_2 (setup : SchnorrSetup) (pk1 pk2 R1 R2 e1 e2 s1 s2 : ℝ)
    (h1 : verifySchnorr setup pk1 R1 e1 s1)
    (h2 : verifySchnorr setup pk2 R2 e2 s2) :
    (s1 + s2) * setup.g = (R1 + R2) + (e1 * pk1 + e2 * pk2) := by
  dsimp [verifySchnorr, verify] at h1 h2
  calc (s1 + s2) * setup.g
    _ = s1 * setup.g + s2 * setup.g := by ring
    _ = (R1 + e1 * pk1) + (R2 + e2 * pk2) := by rw [h1, h2]
    _ = (R1 + R2) + (e1 * pk1 + e2 * pk2) := by ring

/-- Opposite errors cancel in an unweighted sum although both individual checks fail. -/
theorem schnorr_batch_cancellation_example (setup : SchnorrSetup) :
    (1 + (-1) : ℝ) * setup.g = (0 + 0) + (0 * 0 + 0 * 0) ∧
    ¬ verifySchnorr setup 0 0 0 1 ∧ ¬ verifySchnorr setup 0 0 0 (-1) := by
  simp [verifySchnorr, verify, setup.hg_ne]

structure CryptoSchnorrSignatureFormalSuite : Prop where
  h_completeness : ∀ (setup : SchnorrSetup) (sk r e : ℝ),
    verifySchnorr setup (publicKey setup sk) (commitment setup r) e (response r e sk)
  h_special_sound : ∀ (setup : SchnorrSetup) (sk R e1 e2 s1 s2 : ℝ), e1 ≠ e2 →
    verifySchnorr setup (publicKey setup sk) R e1 s1 →
    verifySchnorr setup (publicKey setup sk) R e2 s2 → extractSecretKey s1 s2 e1 e2 = sk
  h_hvzk_sim : ∀ (setup : SchnorrSetup) (pk e s : ℝ),
    verifySchnorr setup pk (simulateCommitment setup pk e s) e s
  h_multisig_agg : ∀ (setup : SchnorrSetup) (pk1 pk2 R1 R2 e s1 s2 : ℝ),
    verifySchnorr setup pk1 R1 e s1 → verifySchnorr setup pk2 R2 e s2 →
    verifySchnorr setup (aggregatePublicKeys pk1 pk2) (aggregateCommitments R1 R2)
      e (aggregateResponses s1 s2)
  h_batch_2 : ∀ (setup : SchnorrSetup) (pk1 pk2 R1 R2 e1 e2 s1 s2 : ℝ),
    verifySchnorr setup pk1 R1 e1 s1 → verifySchnorr setup pk2 R2 e2 s2 →
    (s1 + s2) * setup.g = (R1 + R2) + (e1 * pk1 + e2 * pk2)
  h_batch_cancellation : ∀ setup : SchnorrSetup,
    (1 + (-1) : ℝ) * setup.g = (0 + 0) + (0 * 0 + 0 * 0) ∧
    ¬ verifySchnorr setup 0 0 0 1 ∧ ¬ verifySchnorr setup 0 0 0 (-1)

theorem crypto_schnorr_signature_master_suite : CryptoSchnorrSignatureFormalSuite := {
  h_completeness := schnorr_completeness
  h_special_sound := schnorr_extract_secret_key_eq
  h_hvzk_sim := schnorr_hvzk_simulation
  h_multisig_agg := schnorr_multisig_add
  h_batch_2 := schnorr_batch_verify_2
  h_batch_cancellation := schnorr_batch_cancellation_example
}

structure CryptoSchnorrFormalSuite : Prop where
  h_extended : CryptoSchnorrSignatureFormalSuite
  h_complete : ∀ (setup : SchnorrSetup) (x k c : ℝ),
    verify setup (publicKey setup x) (commitment setup k) c (response k c x)
  h_soundness : ∀ (setup : SchnorrSetup) (pk R c1 c2 s1 s2 : ℝ), c1 ≠ c2 →
    verify setup pk R c1 s1 → verify setup pk R c2 s2 →
    publicKey setup ((s1 - s2) / (c1 - c2)) = pk
  h_simulation : ∀ (setup : SchnorrSetup) (pk c s : ℝ),
    verify setup pk (simulateCommitment setup pk c s) c s

theorem crypto_schnorr_master_verification_suite : CryptoSchnorrFormalSuite := {
  h_extended := crypto_schnorr_signature_master_suite
  h_complete := schnorr_completeness
  h_soundness := schnorr_special_soundness
  h_simulation := schnorr_hvzk_simulation
}

end CryptoSchnorrSignature
