---
id: NonHermitianPhotonicEP
language: en
section: quantum-physics
source: Verification/NonHermitianPhotonicEP.lean
source_sha256: d64896e0667a0d0e4e379dd858ec5f50d23a11ec2b8dfaef4cce311f976c2be8
novelty: not-assessed
---

# NonHermitianPhotonicEP

[Section](README.md) · [Lean source](../../Verification/NonHermitianPhotonicEP.lean)

## Verified result

The sign of κ²−γ², its vanishing at κ=γ, and real splitting 2√Δ. No operator or complex spectrum is constructed.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`discrim_zero_iff_ep`](../../Verification/NonHermitianPhotonicEP.lean#L29)
- [`ep_eigenvalues_coalesce`](../../Verification/NonHermitianPhotonicEP.lean#L39)
- [`unbroken_phase_discrim_pos`](../../Verification/NonHermitianPhotonicEP.lean#L44)
- [`non_hermitian_photonic_master_verification_suite`](../../Verification/NonHermitianPhotonicEP.lean#L89)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
