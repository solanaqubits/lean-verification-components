---
id: CollatzAverageDrift
language: en
section: collatz
source: Verification/CollatzAverageDrift.lean
source_sha256: 7ff0c976a0bf1647e084adf99a5bf16586eab1abd910c4129aff90ff807b5581
novelty: not-assessed
---

# CollatzAverageDrift

[Section](README.md) · [Lean source](../../Verification/CollatzAverageDrift.lean)

## Verified result

The residue-5 branch formula and normalization of prescribed rational weights.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatzIter_four_mod8_five`](../../Verification/CollatzAverageDrift.lean#L11)
- [`collatzIter_four_strict_decrease`](../../Verification/CollatzAverageDrift.lean#L24)
- [`dyadic_measure8_normalized`](../../Verification/CollatzAverageDrift.lean#L50)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
