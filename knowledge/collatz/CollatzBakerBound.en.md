---
id: CollatzBakerBound
language: en
section: collatz
source: Verification/CollatzBakerBound.lean
source_sha256: 1a076473a6bc6dc6976b1384963bb06c8287855f9efd685300e64b1900b4040c
novelty: not-assessed
---

# CollatzBakerBound

[Section](README.md) · [Lean source](../../Verification/CollatzBakerBound.lean)

## Verified result

Numerator and divisibility checks for finite three-transition cases. No general Baker bound is proved.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`cycle3_denom_nonpos`](../../Verification/CollatzBakerBound.lean#L18)
- [`cycle3_denom_pos_iff_ge_five`](../../Verification/CollatzBakerBound.lean#L21)
- [`cycle3_numerators_S5`](../../Verification/CollatzBakerBound.lean#L36)
- [`collatz_baker_master_verification_suite`](../../Verification/CollatzBakerBound.lean#L76)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
