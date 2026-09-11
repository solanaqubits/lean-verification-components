---
id: SpinPhotonicWaveguide
language: en
section: quantum-physics
source: Verification/SpinPhotonicWaveguide.lean
source_sha256: 02120d1e8b75aad24ef611c406b00176f7cfb80dac21e4f9342ee58f4b60aa36
novelty: not-assessed
---

# SpinPhotonicWaveguide

[Section](README.md) · [Lean source](../../Verification/SpinPhotonicWaveguide.lean)

## Verified result

Nonnegative four-coordinate energy, preservation under specified mixing, and phase and geometric-profile formulas.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`energy_nonneg`](../../Verification/SpinPhotonicWaveguide.lean#L24)
- [`energy_zero_iff`](../../Verification/SpinPhotonicWaveguide.lean#L28)
- [`energy_conservation`](../../Verification/SpinPhotonicWaveguide.lean#L46)
- [`spin_photonic_master_verification_suite`](../../Verification/SpinPhotonicWaveguide.lean#L92)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
