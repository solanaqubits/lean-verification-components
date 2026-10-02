---
id: OpticalLossAttenuation
language: en
section: quantum-physics
source: Verification/OpticalLossAttenuation.lean
source_sha256: 2fc08e8a123535bf8b3f6fff06f6ed0055608c83ca3ebf7c5893204b0c5c1902
novelty: not-assessed
status: reviewed
---

# OpticalLossAttenuation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/OpticalLossAttenuation.lean)

## Verified result

The definition is I(z)=i0*exp(-alpha*z). The module proves I(0)=i0, the cascade identity I(z1+z2)=I(z1)*exp(-alpha*z2), and strict decrease when z1<z2, i0>0 and alpha>0. For i0≥0, alpha≥0 and z≥0, it also proves 0≤I(z)≤i0, including zero-input and zero-attenuation cases.

## Model boundaries

Cascading uses the same constant alpha on both segments. Identities do not require positivity; the physical domain and strict monotonicity have separate hypotheses. Consistent units for alpha and z belong to the external interpretation.

The exponential law is a definition, not a derivation from wave equations or Si3N4 measurements. Topological protection, bend losses, calibration of alpha, two-photon absorption, scattering and fluctuating pumping are not proved. The fractional loss 1-I(z)/i0 and logarithmic dB units are not modeled. No FDTD/SimLab results were supplied or used as Lean verification evidence. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `SolarisOptics.optical_loss_master_suite`.
