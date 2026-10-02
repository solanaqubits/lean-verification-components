---
id: CryptoSchnorrSignature
language: en
section: cryptography
source: Verification/CryptoSchnorrSignature.lean
source_sha256: 37e53e36d02d5e36f7168c29aaaded0afcdcef03249fdb672707184650309842
novelty: not-assessed
status: reviewed
---

# CryptoSchnorrSignature

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoSchnorrSignature.lean)

## Verified result

The original real-scalar completeness, compatible-witness extraction and simulated-transcript acceptance theorems are preserved. verifySchnorr aliases verify, and extractSecretKey names (s1-s2)/(e1-e2). With two accepted transcripts sharing the same commitment and public key and unequal challenges, schnorr_extract_secret_key_eq returns the original scalar key when pk=publicKey setup sk.

Two accepted transcripts with a common challenge combine into an accepted transcript for summed keys, commitments and responses. With separate challenges, two accepted equations imply the stated unweighted batch equation. This is a forward implication only. schnorr_batch_cancellation_example proves that responses 1 and -1 at pk=R=e=0 satisfy the sum while both individual checks fail for any nonzero g.

## Assumptions and limitations

The model uses real scalars, and pk/g directly exposes the secret key. The simulator theorem establishes acceptance of a chosen transcript, not equality of honest and simulated distributions or HVZK. No random sampling, signature-message model, adversary or security game is defined.

Naive additive aggregation is not a MuSig/MuSig2 protocol proof. The unweighted batch equality is not equivalent to individual validity and does not provide a sound batch verifier for adversarial inputs. Randomized batch coefficients and their security bounds are not modeled. Fiat–Shamir hashing e=H(R,PK,m), ROM, EUF-CMA/Forking Lemma, rogue-key protection and weighted key aggregation, finite groups, secp256k1/BIP-340, Ed25519 and sr25519 implementations are not formalized. Scientific novelty has not been assessed.

Old definitions, theorem signatures and the existing schnorr_signature registry field retain their types. CryptoSchnorrFormalSuite gains h_extended, which manual constructors must supply; it contains CryptoSchnorrSignatureFormalSuite. The new master theorem is crypto_schnorr_signature_master_suite. No extra import or duplicate registry field is added.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoSchnorrSignature.crypto_schnorr_signature_master_suite`.
