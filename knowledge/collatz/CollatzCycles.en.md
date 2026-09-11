---
id: CollatzCycles
language: en
section: collatz
source: Verification/CollatzCycles.lean
source_sha256: 40b5b62441cbe517c280e54bf9c775e38142da70f613fb02ff72e20b838db8ae
novelty: not-assessed
---

# CollatzCycles

[Section](README.md) · [Lean source](../../Verification/CollatzCycles.lean)

## Verified result

Exclusion of positive one- and two-step returns; classification of three-step returns.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`no_fixed_points_pos`](../../Verification/CollatzCycles.lean#L22)
- [`no_period_one`](../../Verification/CollatzCycles.lean#L31)
- [`no_period_two`](../../Verification/CollatzCycles.lean#L43)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
