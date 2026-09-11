---
id: QuantumHeatEngine
language: en
section: quantum-physics
source: Verification/QuantumHeatEngine.lean
source_sha256: a3f2ee409b36e14dbb5d9c5a8a0ce8f9d742b16681241ee719f02bd0010c65a1
novelty: not-assessed
---

# QuantumHeatEngine

[Section](README.md) · [Lean source](../../Verification/QuantumHeatEngine.lean)

## Verified result

Prescribed scalar heat and work in an Otto cycle, efficiency in (0,1), and a conditional comparison with Carnot efficiency.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`wh_pos`](../../Verification/QuantumHeatEngine.lean#L33)
- [`Th_pos`](../../Verification/QuantumHeatEngine.lean#L34)
- [`netWork_eq`](../../Verification/QuantumHeatEngine.lean#L36)
- [`quantum_heat_engine_master_verification_suite`](../../Verification/QuantumHeatEngine.lean#L87)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
