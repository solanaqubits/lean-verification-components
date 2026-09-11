---
id: QuantumMajoranaChain
language: en
section: quantum-physics
source: Verification/QuantumMajoranaChain.lean
source_sha256: 4f0807d66c0e02faabf9287c3e0373da39ce39ed2e404c50099c18213fcb1db2
novelty: not-assessed
---

# QuantumMajoranaChain

[Section](README.md) · [Lean source](../../Verification/QuantumMajoranaChain.lean)

## Verified result

Explicit complex 2×2 matrices: Majorana algebra, CAR, a number projection, and involutive parity. No spatial chain is constructed.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`gamma1_self_adjoint`](../../Verification/QuantumMajoranaChain.lean#L43)
- [`gamma2_self_adjoint`](../../Verification/QuantumMajoranaChain.lean#L47)
- [`gamma1_sq_identity`](../../Verification/QuantumMajoranaChain.lean#L51)
- [`quantum_majorana_master_verification_suite`](../../Verification/QuantumMajoranaChain.lean#L131)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
