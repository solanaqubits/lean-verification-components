---
id: CryptoPedersenCommitment
language: en
section: cryptography
source: Verification/CryptoPedersenCommitment.lean
source_sha256: 90581daec61cb069b71d0cd260605e56c412e39857bccc32daf24da63b0289c7
novelty: not-assessed
---

# CryptoPedersenCommitment

[Section](../cryptography/README.md) · [Lean source](../../Verification/CryptoPedersenCommitment.lean)

## Verified result

For C(m,r)=mG+rH over real scalars, additivity, scalar linearity, an explicit change of opening, and a ratio identity extracted from a collision. H ≠ 0 is required; the collision result also assumes distinct messages.

## Assumptions and scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

An alternative opening is not equality of commitment distributions. The real ratio G/H is directly available: discrete-log hardness and computational binding are not proved. The theorem names retain the submitted API but do not enlarge the formal claims.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`pedersen_homomorphic_add`](../../Verification/CryptoPedersenCommitment.lean#L19)
- [`pedersen_homomorphic_smul`](../../Verification/CryptoPedersenCommitment.lean#L24)
- [`pedersen_perfect_hiding_equiv`](../../Verification/CryptoPedersenCommitment.lean#L31)
- [`pedersen_binding_discrete_log`](../../Verification/CryptoPedersenCommitment.lean#L40)
- [`crypto_pedersen_master_verification_suite`](../../Verification/CryptoPedersenCommitment.lean#L68)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
