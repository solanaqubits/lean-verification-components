---
id: CryptoZKFRILowDegree
language: en
section: cryptography
source: Verification/CryptoZKFRILowDegree.lean
source_sha256: 49f0b4cce0b82372ccb4683b59debe0afcbb82aa17d07100a5c152f12f63d94b
novelty: not-assessed
---

# CryptoZKFRILowDegree

[Section](README.md) · [Lean source](../../Verification/CryptoZKFRILowDegree.lean)

## Verified result

Length of pairwise coefficient folding, arithmetic of d/2^k, and a folding identity for cubic polynomials.

## Assumptions and scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`friFoldStep_length`](../../Verification/CryptoZKFRILowDegree.lean#L18)
- [`friDegreeStep_strict_lt`](../../Verification/CryptoZKFRILowDegree.lean#L34)
- [`friRoundsDeg_eq`](../../Verification/CryptoZKFRILowDegree.lean#L38)
- [`crypto_zk_fri_master_verification_suite`](../../Verification/CryptoZKFRILowDegree.lean#L76)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
