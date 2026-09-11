---
id: CollatzLogPotential
language: en
section: collatz
source: Verification/CollatzLogPotential.lean
source_sha256: adac89fa57d264601cb50b576190a6b8ef6f49c1d5d1234db654dd038bdb6b2e
novelty: not-assessed
---

# CollatzLogPotential

[Section](README.md) · [Lean source](../../Verification/CollatzLogPotential.lean)

## Verified result

Negativity of the specified scalar expression (15/8) log 3 − (49/16) log 2.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`rpow3_pos`](../../Verification/CollatzLogPotential.lean#L14)
- [`rpow2_pos`](../../Verification/CollatzLogPotential.lean#L17)
- [`log_pow30_three_lt_log_pow49_two`](../../Verification/CollatzLogPotential.lean#L20)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
