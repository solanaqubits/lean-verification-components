---
id: Generated
language: en
section: collatz
source: Verification/Generated.lean
source_sha256: c2d2efb42cf5c16d1cb4014c84f1fda96adf0b2c86f627c08259422ae5df9cfc
novelty: not-assessed
---

# Generated

[Section](README.md) · [Lean source](../../Verification/Generated.lean)

## Verified result

A separate real scalar estimate with explicit witnesses s=1/3, gamma=0.94566, and N₀=5. No link to a global orbit is established.

## Assumptions and scope

Finite trajectories, congruences, and scalar estimates do not prove the Collatz conjecture. Weighted coefficient identities do not establish the behavior of every deterministic orbit.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`foster_lyapunov_contraction_bound`](../../Verification/Generated.lean#L42)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
