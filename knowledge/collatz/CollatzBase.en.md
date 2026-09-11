---
id: CollatzBase
language: en
section: collatz
source: Verification/CollatzBase.lean
source_sha256: 08e7db17198380050792cc5d03c0c594fb8a7c355a93b13f488e3a21b8bc75e5
novelty: not-assessed
---

# CollatzBase

[Section](README.md) · [Lean source](../../Verification/CollatzBase.lean)

## Verified result

Reachability of one for the finite base {1,2,3,4,5}.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatz_one`](../../Verification/CollatzBase.lean#L23)
- [`collatz_two`](../../Verification/CollatzBase.lean#L24)
- [`collatz_three`](../../Verification/CollatzBase.lean#L25)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
