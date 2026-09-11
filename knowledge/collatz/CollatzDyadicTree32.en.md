---
id: CollatzDyadicTree32
language: en
section: collatz
source: Verification/CollatzDyadicTree32.lean
source_sha256: ec31f00e86e0860b5f9d3a5c60a36504a7c16fb9d0a430ecae3440bd23e5e11a
novelty: not-assessed
---

# CollatzDyadicTree32

[Section](README.md) · [Lean source](../../Verification/CollatzDyadicTree32.lean)

## Verified result

A six-branch partition; arithmetic mean of coefficients 639/512 > 1; 31 reaches 5 after 101 steps.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`odd_dyadic_complete_partition_32`](../../Verification/CollatzDyadicTree32.lean#L10)
- [`branch_unique`](../../Verification/CollatzDyadicTree32.lean#L26)
- [`collatz_mod32_thirtyone_stage3`](../../Verification/CollatzDyadicTree32.lean#L33)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
