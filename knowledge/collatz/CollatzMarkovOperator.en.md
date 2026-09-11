---
id: CollatzMarkovOperator
language: en
section: collatz
source: Verification/CollatzMarkovOperator.lean
source_sha256: 8c52f2236424e0ab2c4afbe534378cfa943532b9b0141ddf6ac8e60ed18c1bc4
novelty: not-assessed
---

# CollatzMarkovOperator

[Section](README.md) · [Lean source](../../Verification/CollatzMarkovOperator.lean)

## Verified result

Equality between a weighted expression and a scalar bound, plus a conditional dichotomy. No Markov transition kernel is constructed.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`tree32_markov_drift_eq`](../../Verification/CollatzMarkovOperator.lean#L27)
- [`tree32_markov_drift_strictly_negative`](../../Verification/CollatzMarkovOperator.lean#L36)
- [`collatz_positive_global_dichotomy`](../../Verification/CollatzMarkovOperator.lean#L44)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
