---
id: Collatz2AdicErgodic
language: en
section: collatz
source: Verification/Collatz2AdicErgodic.lean
source_sha256: 161ec435605d2160da630020f9fe3d088b87cff77fffa186a6707e2553e7605f
novelty: not-assessed
---

# Collatz2AdicErgodic

[Section](README.md) · [Lean source](../../Verification/Collatz2AdicErgodic.lean)

## Verified result

Positive cylinder weights and equal preimage cardinalities at ranks 1 and 2 only. No general Haar-measure invariance or ergodicity theorem is proved.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`cylinder_measure_pos`](../../Verification/Collatz2AdicErgodic.lean#L15)
- [`cylinder_measure_halving`](../../Verification/Collatz2AdicErgodic.lean#L19)
- [`syracuse_even_branch`](../../Verification/Collatz2AdicErgodic.lean#L27)
- [`collatz_2adic_ergodic_master_verification_suite`](../../Verification/Collatz2AdicErgodic.lean#L118)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
