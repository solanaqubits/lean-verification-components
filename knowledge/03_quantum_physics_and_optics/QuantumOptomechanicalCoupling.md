---
id: QuantumOptomechanicalCoupling
language: en
section: quantum-physics
source: Verification/QuantumOptomechanicalCoupling.lean
source_sha256: b77ce2d085411707b3de3a2546809d41ea21f13f1ff20b8c40b3f281eb087e54
novelty: not-assessed
status: reviewed
---

# QuantumOptomechanicalCoupling

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumOptomechanicalCoupling.lean)

## Scalar model and normalization

`OptomechanicalParams` supplies positive `omega_c`, `omega_m`, `g0`, `gamma_m`,
and `kappa`. Occupations and displacement are real scalars, not operators.
`x` is displacement in units of `x_zpf`; energy expressions denote H/hbar (frequency units).
`free_energy = omega_c*n_c + omega_m*n_m` omits zero-point offsets, and
`interaction_energy = -g0*n_c*x`. Interpreting products as products of expectation
values requires a separate factorization assumption; correlations are not modeled.

`radiation_force = g0*n_c` is the generalized force conjugate to normalized `x`.
An SI force would require the factor `hbar/x_zpf`. Neither `x_zpf` nor the
relations to effective mass, cavity length, or physical displacement are derived.
The frequency `omega_c-g0*x` is affine, and can be negative for unrestricted `x`;
physical small-displacement validity is external.

## Checked results

- `free_energy_nonneg`: nonnegative free-mode energy for nonnegative occupations.
- `optomechanical_force_nonneg`: nonnegative force for `n_c ≥ 0`.
  `optomechanical_force_pos` proves strict positivity for `n_c > 0`;
  `radiation_force_strict_pos` remains an alias.
  `radiation_force_strict_mono` proves strict growth with photon occupation.
- `interaction_energy_hasDerivAt` and `radiation_force_eq_neg_deriv`: the force
  equals the negative derivative of the prescribed scalar interaction energy.
- `frequency_shift_linear`: the offset from `omega_c` is additive in displacement.
  `frequency_shift_difference` proves differences equal `-g0*(x2-x1)`.
  `frequency_shift_strictly_decreasing` uses `x1 < x2` and `g0 > 0`.
- `total_energy_dispersion`: free plus interaction energy has the shifted optical
  frequency as its coefficient of photon occupation.
- `optical_damping = 4*g^2/kappa`: nonnegative for any `g`, positive for `g ≠ 0`.
  Here `g` is an independently supplied enhanced coupling, not `g0`;
  `g = g0*sqrt(n_c)` is not derived or assumed.
- `dynamical_backaction_cooling`: any `gamma_opt > 0` strictly increases total
  damping over `gamma_m`. Despite its name, this theorem proves no temperature reduction.
- `dynamical_backaction_damping`: for `g ≠ 0`, adding that positive rate strictly
  increases `gamma_m`. At `g = 0`, the rate is unchanged. `red_branch_stable`
  proves positive total rate even at zero enhanced coupling.
- `stability_criterion_iff`: `gamma_eff > 0` exactly when `gamma_opt > -gamma_m`.
  For the prescribed negative branch, `blue_branch_stability_iff` gives
  `4*g^2 < gamma_m*kappa`.
- `stable_envelope_decreases`: the stipulated scalar envelope
  `initial*exp(-gamma_eff*t)` strictly decreases when `initial > 0`, the total
  rate is positive, and time increases. `threshold_envelope_constant` proves
  it is constant at zero total rate. This is not a mechanical oscillator ODE.

The suite is `OptomechanicalCouplingFormalSuite`, instantiated by
`quantum_optomechanical_coupling_master_suite`, with registry field
`QuantumPhysicsFullSuite.optomechanical_coupling`.

## Physical scope

The expression `4*g^2/kappa` is a prescribed approximation, not a derived optical
response. Its usual red-sideband, weak-coupling interpretation uses resolved
sidebands (`kappa << omega_m`), not `kappa >> omega_m`; see
[Aspelmeyer, Kippenberg and Marquardt, Eq. 63](https://arxiv.org/pdf/1303.0733).
No detuning parameter or derivation of a sign change from detuning is present.

Positive total damping and decay of the stipulated envelope do not prove lower
phonon occupation or temperature. Bath noise, heating and equilibrium occupation
are absent. Full coupled-system stability, optical-spring effects, an operator
Hamiltonian, commutators, Langevin noise, the standard quantum limit, and a
resolved-sideband approximation theorem are not formalized. There is no hardware
or simulator validation, and no scientific priority claim.

## Verification

The module passed `verifier_skill.py verify` and `audit`; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. See the
[project validation record](../VERIFICATION.en.md) for full-project checks.
