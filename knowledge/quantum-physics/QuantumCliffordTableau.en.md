---
id: QuantumCliffordTableau
language: en
section: quantum-physics
source: Verification/QuantumCliffordTableau.lean
source_sha256: 14408dd719ac975a6463ca8b6b43057ab90a479d798c2990b2f7a2abc0dd8213
novelty: not-assessed
---

# QuantumCliffordTableau

[Section](README.md) · [Lean source](../../Verification/QuantumCliffordTableau.lean)

## Verified result

H, S, and CNOT preserve a Boolean symplectic form; basis actions and involutions in the phase-free representation.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`H_preserves_symplectic`](../../Verification/QuantumCliffordTableau.lean#L32)
- [`S_preserves_symplectic`](../../Verification/QuantumCliffordTableau.lean#L38)
- [`H_involutive`](../../Verification/QuantumCliffordTableau.lean#L45)
- [`quantum_clifford_master_verification_suite`](../../Verification/QuantumCliffordTableau.lean#L101)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
