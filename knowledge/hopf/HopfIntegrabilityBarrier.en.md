---
id: HopfIntegrabilityBarrier
language: en
section: hopf
source: Verification/HopfIntegrabilityBarrier.lean
source_sha256: f55f4188f59c916b64a83341ad5b07e528f3bcaa4ee5ce9b90f3257c575b92a6
novelty: not-assessed
---

# HopfIntegrabilityBarrier

[Section](README.md) · [Lean source](../../Verification/HopfIntegrabilityBarrier.lean)

## Verified result

A nonzero value rules out identical vanishing of an algebraic expression; bounds for a prescribed scaled scalar energy.

## Assumptions and scope

The algebraic and scalar statements do not resolve the Hopf problem or establish a global geometric integrability obstruction.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`obstruction_of_not_integrable`](../../Verification/HopfIntegrabilityBarrier.lean#L23)
- [`scaled_energy_pos`](../../Verification/HopfIntegrabilityBarrier.lean#L34)
- [`scaled_energy_divergence`](../../Verification/HopfIntegrabilityBarrier.lean#L39)
- [`hopf_master_verification_suite`](../../Verification/HopfIntegrabilityBarrier.lean#L65)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
