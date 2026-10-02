---
id: SolarisMithraCore
language: en
section: quantum-physics
source: Verification/SolarisMithraCore.lean
source_sha256: 9227144d385e982e38dfe585681a75e16b17bdfaf3c45a9deb5c928ab0978b14
novelty: not-assessed
status: reviewed
---

# SolarisMithraCore

[Section](../quantum-physics/README.md) · [Lean](../../Verification/SolarisMithraCore.lean)

## Verified result

For the prescribed formulas I_out = i0*cos²(delta_theta/2) and I_dump = i0*sin²(delta_theta/2), the module proves I_out + I_dump = i0 and exact routing to the dump port at delta_theta = pi. MZIAnalyticalSuite collects both results.

## Model boundaries

The identities hold for every real i0; interpreting it as intensity requires 0 ≤ i0. This is ideal scalar power redistribution, without a derivation from Maxwell equations, a scattering matrix, arm imbalance or device losses. The legacy name adaptive_collapse_complete does not denote quantum collapse or adaptive control. Registration alongside an attenuation law does not prove device composition. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `SolarisMithraCore.mzi_master_verification_suite`.
