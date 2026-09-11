---
id: HopfObstruction
language: en
section: hopf
source: Verification/HopfObstruction.lean
source_sha256: 259a4aab05c7491aabe3551e719a7fb85ed972c1b7b27f0f73f4fbadf9d41cd3
novelty: not-assessed
---

# HopfObstruction

[Section](README.md) · [Lean source](../../Verification/HopfObstruction.lean)

## Verified result

Positivity and unboundedness of the scalar function 1/ε − 1 as positive ε approaches zero.

## Assumptions and scope

The algebraic and scalar statements do not resolve the Hopf problem or establish a global geometric integrability obstruction.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`singular_energy_pos`](../../Verification/HopfObstruction.lean#L18)
- [`singular_energy_lower_half`](../../Verification/HopfObstruction.lean#L27)
- [`hopf_singular_obstruction_divergence`](../../Verification/HopfObstruction.lean#L40)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
