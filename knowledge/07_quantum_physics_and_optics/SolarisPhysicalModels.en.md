---
id: SolarisPhysicalModels
language: en
section: quantum-physics
source: Verification/SolarisPhysicalModels.lean
source_sha256: f0a27eee365eac4e303fc154ea5850457872b4e7a9b7834f97387b78a9b3c5b9
novelty: not-assessed
status: reviewed
---

# SolarisPhysicalModels

[Section](../quantum-physics/README.md) · [Lean](../../Verification/SolarisPhysicalModels.lean)

## Results and audit lessons

Real cosine orthogonality on [0,2*pi] is proved under m1≠m2 and m1≠-m2. The indices 1 and -1 give the counterexample integral pi. Distinct indices alone are insufficient. Orthogonality preservation by a supplied complex linear isometry and squared-norm preservation by a supplied unitary transformation are proved separately; the operators are not constructed from a waveguide or YIG model.

The original existential claims loss_bound<0.05, energy_loss≤alpha*g and actual_stress≤50 MPa allowed arbitrary witnesses unrelated to a device. The issue was a weak specification: these existences do not establish physical losses, unitarity or strength. Lean checking alone does not eliminate interpretation errors.

adiabatic_oam_phase_stability explicitly assumes calibration |phase_error(n,r)|≤0.012 at the stated thresholds and derives <0.05. magnon_photon_loss_bound links the input energy_loss to alpha*g, deriving a stricter budget from small alpha and positive g. thermalStressProxy is defined as |delta_alpha*delta_temp*joint_modulus|. The given inputs evaluate to 9812000 Pa; the actual_stress bound requires equality to that proxy.

## Model boundaries

Loss laws, the relation between the scalar proxy and the von Mises stress tensor, adiabatic dynamics and actual resonator unitarity are not derived. There is no unconditional absence-of-noise or packaging certification result. Calibration and model adequacy remain explicit premises, not custom axioms. The root Verification module exports this file, and the project audit checks it separately from the three-component PhotonicsInterposerFullSuite. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `SolarisOptics.oam_mode_orthogonality_preserved`.
