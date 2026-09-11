---
id: CollatzEffectiveDrift
language: en
section: collatz
source: Verification/CollatzEffectiveDrift.lean
source_sha256: a216f94665f0071ae84d779fb34a5d4c58abfd0be34bbfb8d4413666fc0343ef
novelty: not-assessed
---

# CollatzEffectiveDrift

[Section](README.md) · [Lean source](../../Verification/CollatzEffectiveDrift.lean)

## Verified result

A negative scalar bound for n ≥ 13 and reachability of one for inputs 1 through 12.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`drift_ratio_pos`](../../Verification/CollatzEffectiveDrift.lean#L14)
- [`log_drift_gap_algebraic_lower_bound`](../../Verification/CollatzEffectiveDrift.lean#L19)
- [`rational_drift_threshold_thirteen_strict`](../../Verification/CollatzEffectiveDrift.lean#L30)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
