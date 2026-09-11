---
id: SymplecticHamiltonianDynamics
language: en
section: quantum-physics
source: Verification/SymplecticHamiltonianDynamics.lean
source_sha256: 10c0d2cc2d98721ecd777b69d9eb1b7588074633744ed98188c8dda493e0c963
novelty: not-assessed
---

# SymplecticHamiltonianDynamics

[Section](README.md) · [Lean source](../../Verification/SymplecticHamiltonianDynamics.lean)

## Verified result

The prescribed symplectic Euler step has determinant one and preserves a modified quadratic energy, nonnegative when h²k < 4m.

## Assumptions and scope

The results concern the explicit matrices, transformations, and scalar energy models. Their correspondence to a physical device or a full many-body system is not established by compilation.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`symplectic_jacobian_det_one`](../../Verification/SymplecticHamiltonianDynamics.lean#L39)
- [`symplectic_form_preserved`](../../Verification/SymplecticHamiltonianDynamics.lean#L43)
- [`shadow_energy_conserved`](../../Verification/SymplecticHamiltonianDynamics.lean#L52)
- [`symplectic_dynamics_master_verification_suite`](../../Verification/SymplecticHamiltonianDynamics.lean#L91)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
