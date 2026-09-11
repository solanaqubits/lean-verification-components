---
id: QuantumToricCode
language: en
section: quantum-physics
source: Verification/QuantumToricCode.lean
source_sha256: 63895946a6f1f906b0457d073fdcb0d2d04934eea928d160fb4570fec964d8f3
novelty: not-assessed
---

# QuantumToricCode

[Section](README.md) · [Lean source](../../Verification/QuantumToricCode.lean)

## Verified result

Parity of a prescribed overlap, energy formulas, and addition of a defect pair by definition. No lattice is constructed.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`star_plaq_comm_of_even_overlap`](../../Verification/QuantumToricCode.lean#L16)
- [`star_plaq_comm_zero_overlap`](../../Verification/QuantumToricCode.lean#L22)
- [`star_plaq_comm_two_overlap`](../../Verification/QuantumToricCode.lean#L23)
- [`quantum_toric_master_verification_suite`](../../Verification/QuantumToricCode.lean#L95)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
