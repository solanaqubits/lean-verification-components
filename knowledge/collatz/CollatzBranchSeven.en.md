---
id: CollatzBranchSeven
language: en
section: collatz
source: Verification/CollatzBranchSeven.lean
source_sha256: b4ae976a1299f333994d44c53ff8d1cf4da53b7d41b9e1c515d155d27620bcb0
novelty: not-assessed
---

# CollatzBranchSeven

[Section](README.md) · [Lean source](../../Verification/CollatzBranchSeven.lean)

## Verified result

Splitting the residue-7 branch modulo 16, iteration formulas, and the finite orbit of seven.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`mod8_seven_split_mod16`](../../Verification/CollatzBranchSeven.lean#L11)
- [`collatz_mod16_seven_stage1`](../../Verification/CollatzBranchSeven.lean#L16)
- [`collatz_mod16_seven_stage2`](../../Verification/CollatzBranchSeven.lean#L21)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
