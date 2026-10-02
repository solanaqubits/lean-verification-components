---
id: CryptoElGamalEncryption
language: en
section: cryptography
source: Verification/CryptoElGamalEncryption.lean
source_sha256: 417ee25530fa7b57b72656c2728d9bb0093d3d34bf57356c194f2c715686c555
novelty: not-assessed
status: reviewed
---

# CryptoElGamalEncryption

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoElGamalEncryption.lean)

## Verified result

The scalar ciphertext (r*g, m+r*pk) decrypts to m when pk=x*g. Decryption is additive and homogeneous for arbitrary ciphertexts. Adding encryptions under the same pk equals encryption of m1+m2 with parameter r1+r2. Adding an encryption of zero preserves the original plaintext.

## Assumptions and limitations

The setup requires g ≠ 0. All values are real scalars; public pk/g directly reveals x. These equalities do not establish confidentiality or IND-CPA security. No random sampling, independence or distributional rerandomization is defined. At r2=0 the added encryption of zero is zero, so the theorem does not claim the ciphertext always changes.

Messages are real scalars added directly to c2, not encoded group elements g^m. DDH, finite cyclic groups, discrete-log decoding and Baby-step Giant-step, Twisted Edwards/Ristretto curves, and correspondence to Solana confidential-transfer implementations are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoElGamalEncryption.crypto_elgamal_master_verification_suite`.
