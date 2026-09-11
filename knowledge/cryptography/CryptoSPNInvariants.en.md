---
id: CryptoSPNInvariants
language: en
section: cryptography
source: Verification/CryptoSPNInvariants.lean
source_sha256: d75285a57bc578afa597216f95c072c5e07638f59d3fc1fd00ad5fa58e41a751
novelty: not-assessed
---

# CryptoSPNInvariants

[Section](README.md) · [Lean source](../../Verification/CryptoSPNInvariants.lean)

## Verified result

Invertibility of rational diffusion, a weight-sum lower bound of five, and round bijectivity under invertible substitution.

## Assumptions and scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`zero_x0`](../../Verification/CryptoSPNInvariants.lean#L29)
- [`smul_x0`](../../Verification/CryptoSPNInvariants.lean#L31)
- [`zero_x1`](../../Verification/CryptoSPNInvariants.lean#L33)
- [`crypto_spn_master_verification_suite`](../../Verification/CryptoSPNInvariants.lean#L230)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
