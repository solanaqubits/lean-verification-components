---
id: QuantumStabilizerCodes
language: en
section: quantum-physics
source: Verification/QuantumStabilizerCodes.lean
source_sha256: a3905aa63844777f15d56f3bee601811bb8073acb29432ad3c9602def829c485
novelty: not-assessed
---

# QuantumStabilizerCodes

[Section](README.md) · [Lean source](../../Verification/QuantumStabilizerCodes.lean)

## Verified result

Phase-free Boolean Pauli representation, symmetry of its product, and four distinct syndromes for a three-qubit bit-flip code.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`symplecticProd1_comm`](../../Verification/QuantumStabilizerCodes.lean#L25)
- [`symplecticProd1_identity`](../../Verification/QuantumStabilizerCodes.lean#L31)
- [`pauliMul_identity`](../../Verification/QuantumStabilizerCodes.lean#L36)
- [`quantum_stabilizer_master_verification_suite`](../../Verification/QuantumStabilizerCodes.lean#L126)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
