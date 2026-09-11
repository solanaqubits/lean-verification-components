---
id: CryptoKZGCommitment
language: en
section: cryptography
source: Verification/CryptoKZGCommitment.lean
source_sha256: bb35e4c7485316cf7ad221f2688742b42ef49ea9f6efd23ad1490126e28e3cda
novelty: not-assessed
---

# CryptoKZGCommitment

[Section](README.md) · [Lean source](../../Verification/CryptoKZGCommitment.lean)

## Verified result

Division identities for P(x)−P(z) in degrees 2 and 3, linearity of evaluation, and cancellation in a scalar verification equation.

## Assumptions and scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`poly2_division_identity`](../../Verification/CryptoKZGCommitment.lean#L12)
- [`poly3_division_identity`](../../Verification/CryptoKZGCommitment.lean#L21)
- [`kzg_commitment_linearity`](../../Verification/CryptoKZGCommitment.lean#L29)
- [`crypto_kzg_master_verification_suite`](../../Verification/CryptoKZGCommitment.lean#L88)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
