---
id: CollatzBranchFifteen
language: en
section: collatz
source: Verification/CollatzBranchFifteen.lean
source_sha256: 3ca75b4a9c70ea166ce61f45d824ebbb02cd62364619102ec24c948ec09b23bf
novelty: not-assessed
---

# CollatzBranchFifteen

[Section](README.md) · [Lean source](../../Verification/CollatzBranchFifteen.lean)

## Verified result

Refining the residue-15 branch modulo 32 and finite iteration formulas.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`collatz_mod16_fifteen_stage1`](../../Verification/CollatzBranchFifteen.lean#L10)
- [`collatz_mod16_fifteen_stage2`](../../Verification/CollatzBranchFifteen.lean#L15)
- [`collatzIter_six_mod16_fifteen`](../../Verification/CollatzBranchFifteen.lean#L24)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
