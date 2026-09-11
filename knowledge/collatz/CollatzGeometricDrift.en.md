---
id: CollatzGeometricDrift
language: en
section: collatz
source: Verification/CollatzGeometricDrift.lean
source_sha256: 72b07e777b93d480e1e0f3a2064ec2ef153bafed748e7a85ecc83f84d0ea1742
novelty: not-assessed
---

# CollatzGeometricDrift

[Section](README.md) · [Lean source](../../Verification/CollatzGeometricDrift.lean)

## Verified result

The exact coefficient product 3^30/2^49 is between zero and one. This is a power of the geometric mean, not an orbit-wise contraction theorem.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`expected_pow3_eq`](../../Verification/CollatzGeometricDrift.lean#L40)
- [`expected_pow2_eq`](../../Verification/CollatzGeometricDrift.lean#L52)
- [`collatz_tree32_integer_drift_strict_contraction`](../../Verification/CollatzGeometricDrift.lean#L56)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
