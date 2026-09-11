---
id: CollatzAttractor
language: en
section: collatz
source: Verification/CollatzAttractor.lean
source_sha256: b82afe03dd56bcfc7a3cf983bace28e3dc475a20f8aea5e12acd74cf69bdf531
novelty: not-assessed
---

# CollatzAttractor

[Section](README.md) · [Lean source](../../Verification/CollatzAttractor.lean)

## Verified result

Conditional reachability of one once an orbit enters the finite base.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatzIter_add`](../../Verification/CollatzAttractor.lean#L14)
- [`collatz_reaches_one_if_enters_compact`](../../Verification/CollatzAttractor.lean#L30)
- [`collatz_one_step_reduction`](../../Verification/CollatzAttractor.lean#L42)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
