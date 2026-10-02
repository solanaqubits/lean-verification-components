---
id: CryptoShamirSecretSharing
language: en
section: cryptography
source: Verification/CryptoShamirSecretSharing.lean
source_sha256: 59fde5cd871b66206025b821790f8dfc5610bfc2620f4f3e2bcb265e6dfeea4f
novelty: not-assessed
status: reviewed
---

# CryptoShamirSecretSharing

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoShamirSecretSharing.lean)

## Verified result

The original reconstruction, evaluation-at-zero, weight-sum and unique-compatible-slope results remain. PolyLinear aliases Shamir2Polynomial; s/a access secret/slope. The new second Lagrange weight x1/(x1-x2) is proved equal to the retained weight -x1/(x2-x1). Requested reconstruction and single-share compatibility entry points reuse existing theorems. A new theorem proves addition of evaluations equals evaluation of coefficientwise sums.

## Assumptions and limitations

The polynomial has degree at most one, since the slope may be zero. Reconstruction requires distinct coordinates but not nonzero coordinates. Single-share compatibility and uniqueness require a nonzero coordinate. No distribution on slopes or secrets is defined, so compatibility with every candidate secret does not prove information-theoretic privacy or indistinguishability.

Original definitions and theorem names are preserved. PolyLinear retains record fields secret/slope; s/a are accessors. The original suite now includes h_additive_suite and requires it in manual constructors. CryptoFullSuite.shamir_secret_sharing accesses that new suite through the existing shamir field; no import is added. General thresholds, finite fields, VSS, malicious-share detection and implementation correctness are outside this model. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoShamirSecretSharing.crypto_shamir_secret_sharing_master_verification_suite`.
