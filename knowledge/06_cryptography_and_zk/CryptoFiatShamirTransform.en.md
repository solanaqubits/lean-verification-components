---
id: CryptoFiatShamirTransform
language: en
section: cryptography
source: Verification/CryptoFiatShamirTransform.lean
source_sha256: f610ff29b97ce0192f99d8a931c1cdb861a7aeb2bc1b8dc30ddc1d8488a5d2ac
novelty: not-assessed
status: reviewed
---

# CryptoFiatShamirTransform

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoFiatShamirTransform.lean)

## Verified result

Honest responses satisfy the scalar verification equation. Two accepted transcripts with the same commitment R and distinct challenges yield an extracted scalar whose product with G equals the public key. An additional theorem uses G ≠ 0 and the key relation to prove that this scalar equals privKey. Substituting any deterministic oracle output as the challenge preserves honest completeness.

## Assumptions and limitations

SchnorrKeys stores real scalars, G ≠ 0 and pubKey = privKey*G. Extraction assumes both verification equations and c1 ≠ c2; it does not construct the two transcripts. FiatShamirOracle is an arbitrary function of R and a real-valued message, not a random oracle, hash implementation, encoding or domain-separation scheme. Even a constant function is permitted by the completeness theorem.

Over real scalars the private value is already algebraically determined as pubKey/G. No discrete-log hardness, finite cyclic group, zero-knowledge simulator, randomness distribution, rewinding or forking lemma, ROM security or probabilistic unforgeability is formalized. The theorem name special_soundness refers to this conditional algebraic extraction, not a proof of security for a deployed signature scheme.

## Value and novelty

Reusable completeness and extraction equations with explicit nondegeneracy conditions. Mathematical novelty and first-formalization claims have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `CryptoFiatShamirTransform.crypto_fiat_shamir_master_verification_suite`.

- [`schnorr_special_soundness`](../../Verification/CryptoFiatShamirTransform.lean#L32)
- [`schnorr_extracts_private_key`](../../Verification/CryptoFiatShamirTransform.lean#L48)
