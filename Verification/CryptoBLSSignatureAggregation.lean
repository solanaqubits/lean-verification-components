import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace CryptoBLSSignatureAggregation

/-- Parameters of a scalar multiplication model, not an elliptic-curve group. -/
structure BLSSetup where
  g2 : ℝ
  hg2_ne_zero : g2 ≠ 0

def publicKey (x : ℝ) (setup : BLSSetup) : ℝ := x * setup.g2

def sign (x Hm : ℝ) : ℝ := x * Hm

/-- Concrete real multiplication, not a cryptographic pairing. -/
def pairing (P Q : ℝ) : ℝ := P * Q

def verifySingle (setup : BLSSetup) (Hm pk sig : ℝ) : Prop :=
  pairing sig setup.g2 = pairing Hm pk

/-- Completeness of the supplied scalar verification equation. -/
theorem bls_single_completeness (setup : BLSSetup) (x Hm : ℝ) :
    verifySingle setup Hm (publicKey x setup) (sign x Hm) := by
  dsimp [verifySingle, pairing, publicKey, sign]
  ring

def aggregateSignatures (sig1 sig2 : ℝ) : ℝ := sig1 + sig2

def aggregatePublicKeys (pk1 pk2 : ℝ) : ℝ := pk1 + pk2

def verifyAggregate (setup : BLSSetup) (Hm pkAgg sigAgg : ℝ) : Prop :=
  pairing sigAgg setup.g2 = pairing Hm pkAgg

/-- Two honestly generated scalar signatures on the same supplied message value. -/
theorem bls_aggregation_completeness (setup : BLSSetup) (x1 x2 Hm : ℝ) :
    let sig1 := sign x1 Hm
    let sig2 := sign x2 Hm
    let pk1 := publicKey x1 setup
    let pk2 := publicKey x2 setup
    let sigAgg := aggregateSignatures sig1 sig2
    let pkAgg := aggregatePublicKeys pk1 pk2
    verifyAggregate setup Hm pkAgg sigAgg := by
  dsimp [verifyAggregate, pairing, aggregateSignatures, aggregatePublicKeys, sign, publicKey]
  ring

theorem pairing_add_left (P1 P2 Q : ℝ) :
    pairing (P1 + P2) Q = pairing P1 Q + pairing P2 Q := by
  dsimp [pairing]
  ring

theorem pairing_scalar_homogeneity (c P Q : ℝ) :
    pairing (c * P) Q = c * pairing P Q ∧ pairing P (c * Q) = c * pairing P Q := by
  dsimp [pairing]
  constructor <;> ring

/- A separate interface preserves the original setup and argument orders. -/
namespace TwoGenerator

/-- Two nonzero real scales, not generators of cryptographic groups. -/
structure BLSSetup where
  g1 : ℝ
  g2 : ℝ
  hg1_ne : g1 ≠ 0
  hg2_ne : g2 ≠ 0

def publicKey (setup : BLSSetup) (sk : ℝ) : ℝ := sk * setup.g2

def sign (setup : BLSSetup) (sk h : ℝ) : ℝ := sk * h * setup.g1

def verifySingle (setup : BLSSetup) (pk h sig : ℝ) : Prop :=
  pairing sig setup.g2 = pairing (h * setup.g1) pk

end TwoGenerator

/-- Completeness for honestly constructed scalar signatures with two scales. -/
theorem bls_single_correctness (setup : TwoGenerator.BLSSetup) (sk h : ℝ) :
    TwoGenerator.verifySingle setup (TwoGenerator.publicKey setup sk) h
      (TwoGenerator.sign setup sk h) := by
  dsimp [TwoGenerator.verifySingle, TwoGenerator.publicKey, TwoGenerator.sign, pairing]
  ring

/-- Same-message aggregation of two honest signatures; no operation count is modeled. -/
theorem bls_multisig_same_message_correctness
    (setup : TwoGenerator.BLSSetup) (sk1 sk2 h : ℝ) :
    let sig1 := TwoGenerator.sign setup sk1 h
    let sig2 := TwoGenerator.sign setup sk2 h
    let sigAgg := aggregateSignatures sig1 sig2
    let pkAgg := aggregatePublicKeys
      (TwoGenerator.publicKey setup sk1) (TwoGenerator.publicKey setup sk2)
    TwoGenerator.verifySingle setup pkAgg h sigAgg := by
  dsimp [TwoGenerator.verifySingle, TwoGenerator.publicKey, TwoGenerator.sign,
    pairing, aggregateSignatures, aggregatePublicKeys]
  ring

/-- Two arbitrary scalar message values; they need not be distinct. -/
theorem bls_aggregate_distinct_messages_correctness
    (setup : TwoGenerator.BLSSetup) (sk1 sk2 h1 h2 : ℝ) :
    let sig1 := TwoGenerator.sign setup sk1 h1
    let sig2 := TwoGenerator.sign setup sk2 h2
    let sigAgg := aggregateSignatures sig1 sig2
    let pk1 := TwoGenerator.publicKey setup sk1
    let pk2 := TwoGenerator.publicKey setup sk2
    pairing sigAgg setup.g2 =
      pairing (h1 * setup.g1) pk1 + pairing (h2 * setup.g1) pk2 := by
  dsimp [TwoGenerator.publicKey, TwoGenerator.sign, pairing, aggregateSignatures]
  ring

/-- Additivity in the supplied scalar h, not in raw messages or a hash function. -/
theorem bls_sig_additive_messages (setup : TwoGenerator.BLSSetup) (sk h1 h2 : ℝ) :
    TwoGenerator.sign setup sk (h1 + h2) =
      TwoGenerator.sign setup sk h1 + TwoGenerator.sign setup sk h2 := by
  dsimp [TwoGenerator.sign]
  ring

theorem bls_sig_homomorphic_scale (setup : TwoGenerator.BLSSetup) (k sk h : ℝ) :
    TwoGenerator.sign setup (k * sk) h = k * TwoGenerator.sign setup sk h := by
  dsimp [TwoGenerator.sign]
  ring

structure TwoGeneratorFormalSuite : Prop where
  h_single_correct : ∀ (setup : TwoGenerator.BLSSetup) (sk h : ℝ),
    TwoGenerator.verifySingle setup (TwoGenerator.publicKey setup sk) h
      (TwoGenerator.sign setup sk h)
  h_same_msg_agg : ∀ (setup : TwoGenerator.BLSSetup) (sk1 sk2 h : ℝ),
    TwoGenerator.verifySingle setup
      (aggregatePublicKeys (TwoGenerator.publicKey setup sk1) (TwoGenerator.publicKey setup sk2))
      h (aggregateSignatures (TwoGenerator.sign setup sk1 h) (TwoGenerator.sign setup sk2 h))
  h_diff_msg_agg : ∀ (setup : TwoGenerator.BLSSetup) (sk1 sk2 h1 h2 : ℝ),
    pairing (aggregateSignatures (TwoGenerator.sign setup sk1 h1)
      (TwoGenerator.sign setup sk2 h2)) setup.g2 =
    pairing (h1 * setup.g1) (TwoGenerator.publicKey setup sk1) +
      pairing (h2 * setup.g1) (TwoGenerator.publicKey setup sk2)
  h_add_msg : ∀ (setup : TwoGenerator.BLSSetup) (sk h1 h2 : ℝ),
    TwoGenerator.sign setup sk (h1 + h2) =
      TwoGenerator.sign setup sk h1 + TwoGenerator.sign setup sk h2
  h_scale_key : ∀ (setup : TwoGenerator.BLSSetup) (k sk h : ℝ),
    TwoGenerator.sign setup (k * sk) h = k * TwoGenerator.sign setup sk h

theorem two_generator_master_suite : TwoGeneratorFormalSuite := {
  h_single_correct := bls_single_correctness
  h_same_msg_agg := bls_multisig_same_message_correctness
  h_diff_msg_agg := bls_aggregate_distinct_messages_correctness
  h_add_msg := bls_sig_additive_messages
  h_scale_key := bls_sig_homomorphic_scale
}

structure CryptoBLSSignatureFormalSuite : Prop where
  h_two_generator : TwoGeneratorFormalSuite
  h_single_complete : ∀ (setup : BLSSetup) (x Hm : ℝ),
    verifySingle setup Hm (publicKey x setup) (sign x Hm)
  h_agg_complete : ∀ (setup : BLSSetup) (x1 x2 Hm : ℝ),
    let sigAgg := aggregateSignatures (sign x1 Hm) (sign x2 Hm)
    let pkAgg := aggregatePublicKeys (publicKey x1 setup) (publicKey x2 setup)
    verifyAggregate setup Hm pkAgg sigAgg
  h_pair_add_left : ∀ (P1 P2 Q : ℝ),
    pairing (P1 + P2) Q = pairing P1 Q + pairing P2 Q
  h_pair_homogeneity : ∀ (c P Q : ℝ),
    pairing (c * P) Q = c * pairing P Q ∧ pairing P (c * Q) = c * pairing P Q

theorem crypto_bls_signature_master_verification_suite : CryptoBLSSignatureFormalSuite := {
  h_two_generator := two_generator_master_suite
  h_single_complete := bls_single_completeness
  h_agg_complete := bls_aggregation_completeness
  h_pair_add_left := pairing_add_left
  h_pair_homogeneity := pairing_scalar_homogeneity
}

/-- The extended registry retains the original scalar API and adds two-scale results. -/
theorem crypto_bls_signature_master_suite : CryptoBLSSignatureFormalSuite :=
  crypto_bls_signature_master_verification_suite

end CryptoBLSSignatureAggregation
