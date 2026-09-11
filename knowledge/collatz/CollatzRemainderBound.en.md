---
id: CollatzRemainderBound
language: en
section: collatz
source: Verification/CollatzRemainderBound.lean
source_sha256: 3433485e6119b1aabe928f2069d9e11bc55a609ee0395c273a04b8961bbf746c
novelty: not-assessed
---

# CollatzRemainderBound

[Section](README.md) · [Lean source](../../Verification/CollatzRemainderBound.lean)

## Verified result

The weighted rational correction 40/81 and bounds after division by the input.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`expected_remainder_eq`](../../Verification/CollatzRemainderBound.lean#L36)
- [`remainder_uniform_lt_one`](../../Verification/CollatzRemainderBound.lean#L40)
- [`expected_perturbation_bound_at_five`](../../Verification/CollatzRemainderBound.lean#L46)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
