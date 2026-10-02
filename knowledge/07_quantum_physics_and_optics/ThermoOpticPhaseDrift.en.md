---
id: ThermoOpticPhaseDrift
language: en
section: quantum-physics
source: Verification/ThermoOpticPhaseDrift.lean
source_sha256: f71198898e0a95337ba634905be7802041af7f0d71d8beb685d62980cfe803bf
novelty: not-assessed
status: reviewed
---

# ThermoOpticPhaseDrift

[Section](../quantum-physics/README.md) · [Lean](../../Verification/ThermoOpticPhaseDrift.lean)

## Verified result

For the constant coefficient A=k0*dndT*length, phase_drift(p,dT)=A*dT. The module proves additivity, zero drift at dT=0, and |phase_drift|≤|A|*tol from |dT|≤tol. An additional budget |A|*tol≤budget gives |phase_drift|≤budget.

If A≠0, the budget is equivalent to the temperature threshold |dT|≤budget/|A|. If A=0, drift vanishes at every temperature; the threshold theorem does not divide by zero. Parameters may have either sign. The premise |dT|≤tol already implies tol≥0; a physical budget is nonnegative.

## Model boundaries

This deterministic constant-coefficient linear model does not establish optical or statistical coherence. Lean does not relate k0 to 2*pi/lambda or derive dndT by differentiating refractive index, and units are not encoded. Phase periodicity modulo 2*pi, nonlinear temperature effects, thermal expansion, heat capacity, transients, noise, stabilizer feedback and physical interposers are not modeled. FDTD/SimLab remains an external step without supplied results. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `SolarisThermoOptics.thermo_optic_master_suite`.
