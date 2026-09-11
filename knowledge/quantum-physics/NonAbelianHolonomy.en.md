---
id: NonAbelianHolonomy
language: en
section: quantum-physics
source: Verification/NonAbelianHolonomy.lean
source_sha256: 49fe81c70c0d4b8f744e9573d25c77fbb8e4458b89feb2233d1a200ae5c5533d
novelty: not-assessed
---

# NonAbelianHolonomy

[Section](README.md) · [Lean source](../../Verification/NonAbelianHolonomy.lean)

## Verified result

Real skew-symmetric 3×3 matrices: closure under commutators, so(3) relations, and Jacobi. Parallel transport along loops is not defined.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`Lx_skew`](../../Verification/NonAbelianHolonomy.lean#L72)
- [`Ly_skew`](../../Verification/NonAbelianHolonomy.lean#L76)
- [`Lz_skew`](../../Verification/NonAbelianHolonomy.lean#L80)
- [`non_abelian_holonomy_master_verification_suite`](../../Verification/NonAbelianHolonomy.lean#L131)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
