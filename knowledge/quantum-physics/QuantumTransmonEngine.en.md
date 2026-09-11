---
id: QuantumTransmonEngine
language: en
section: quantum-physics
source: Verification/QuantumTransmonEngine.lean
source_sha256: 580cd2e93fff464e4039ea4229da4477c9785873b05437a7509ef4fc11c5484c
novelty: not-assessed
---

# QuantumTransmonEngine

[Section](README.md) · [Lean source](../../Verification/QuantumTransmonEngine.lean)

## Verified result

A lower bound for a prescribed two-level gap and exact deviations from ng=1/2.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`eigenGapSq_pos`](../../Verification/QuantumTransmonEngine.lean#L27)
- [`eigenGapSq_ge_EJ_sq`](../../Verification/QuantumTransmonEngine.lean#L32)
- [`eigenGap_ge_EJ`](../../Verification/QuantumTransmonEngine.lean#L37)
- [`quantum_transmon_master_verification_suite`](../../Verification/QuantumTransmonEngine.lean#L94)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
