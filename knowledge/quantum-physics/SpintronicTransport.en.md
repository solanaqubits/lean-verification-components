---
id: SpintronicTransport
language: en
section: quantum-physics
source: Verification/SpintronicTransport.lean
source_sha256: 1f432346f2b4108ab04191b852425aca6bf11e62c72d348bbfa9a7bb0729498b
novelty: not-assessed
---

# SpintronicTransport

[Section](README.md) · [Lean source](../../Verification/SpintronicTransport.lean)

## Verified result

A prescribed antisymmetric response matrix, zero scalar work, and an inverse matrix for a nonzero coefficient.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`klitzing_pos`](../../Verification/SpintronicTransport.lean#L21)
- [`chern_tensor_antisymmetric`](../../Verification/SpintronicTransport.lean#L48)
- [`chern_tensor_longitudinal_zero`](../../Verification/SpintronicTransport.lean#L51)
- [`spintronic_transport_master_verification_suite`](../../Verification/SpintronicTransport.lean#L114)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
