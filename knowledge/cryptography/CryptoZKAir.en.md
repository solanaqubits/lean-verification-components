---
id: CryptoZKAir
language: en
section: cryptography
source: Verification/CryptoZKAir.lean
source_sha256: f7d977aed20a9d88c01a8f7822147e718c53059a82deb62e05f9bd3e73d061cb
novelty: not-assessed
---

# CryptoZKAir

[Section](README.md) · [Lean source](../../Verification/CryptoZKAir.lean)

## Verified result

Generation and checking of finite deterministic traces, checker correctness, and trace uniqueness.

## Assumptions and scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`generateTrace_length`](../../Verification/CryptoZKAir.lean#L18)
- [`generateTrace_head`](../../Verification/CryptoZKAir.lean#L24)
- [`generateTrace_valid`](../../Verification/CryptoZKAir.lean#L28)
- [`crypto_zk_air_master_verification_suite`](../../Verification/CryptoZKAir.lean#L97)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
