---
id: CryptoShamirSecretSharing
language: en
section: cryptography
source: Verification/CryptoShamirSecretSharing.lean
source_sha256: c7e84e0287fdae4a71e32077cd214999d35c8749d922a7afa1dda8407561e7ee
novelty: not-assessed
status: reviewed
---

# CryptoShamirSecretSharing

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoShamirSecretSharing.lean)

## Verified result

For P(x) = secret + slope*x, evaluation at zero returns the secret. At distinct coordinates x1 and x2, the Lagrange weights sum to one and their weighted combination of two evaluations recovers the secret exactly. For any single share (x,y) with x ≠ 0 and any candidate secret s, the slope (y-s)/x produces that share. An additional uniqueness theorem proves there is exactly one compatible slope for each fixed candidate secret.

## Assumptions and limitations

Reconstruction needs distinct coordinates, not distinct share values, and permits one coordinate to be zero. Single-share compatibility requires a nonzero coordinate: a share at zero directly exposes the secret. The share function itself accepts every real coordinate. There is no collection of n participants, sampling algorithm, or random slope distribution.

These results establish algebraic compatibility, not equality of probability distributions or information-theoretic perfect secrecy. Neither arbitrary k > 2 thresholds, finite fields, malicious-share detection, Feldman/Pedersen VSS, numerical precision nor a deployed secret-sharing implementation is formalized. The historical theorem name `shamir_single_share_perfect_secrecy` denotes only its displayed algebraic statement.

## Value and novelty

Reusable reconstruction equations and explicit nondegeneracy conditions; a check of why one nonzero-coordinate share leaves the secret algebraically undetermined. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `CryptoShamirSecretSharing.crypto_shamir_master_verification_suite`.
