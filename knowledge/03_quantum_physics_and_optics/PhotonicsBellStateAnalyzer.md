---
id: PhotonicsBellStateAnalyzer
language: en
section: quantum-physics
source: Verification/PhotonicsBellStateAnalyzer.lean
source_sha256: 1399413a00dc3a96a2c8237f2d18842c788af0518ea7f134921f06732a422ac5
novelty: not-assessed
status: reviewed
---

# A concrete linear-optical Bell-state analyzer

[Section](../quantum-physics/README.md) · [Lean](../../Verification/PhotonicsBellStateAnalyzer.lean)

## Optical model and derivation

The four modes are a_H, a_V, b_H, b_V at the input and c_H, c_V, d_H, d_V at
the output. Each polarization is mixed between spatial ports using the imported
PhotonicsBeamSplitterPhaseShift.splitter(1/2), with reflection amplitude i/sqrt(2).
The two-photon basis enumerates all ten unordered pairs including repeated modes.
The occupation enumeration is proved bijective onto ordered pairs i <= j.
Double occupation has creation monomial x_i^2/sqrt(2); distinct modes have x_i*x_j.
Polynomial substitution proves the symmetric-lift coefficients for any four-mode
complex matrix. This finite normalized bosonic model does not construct the full
infinite Fock space or prove canonical commutation relations.

Both the one-photon network U₁ and the derived two-photon lift U₂ satisfy U†U = I.
The isometry J embeds HH, HV, VH, VV into pairs (0,2), (0,3), (1,2), (1,3).
An ideal PBS routes (spatial port, polarization) bijectively to four detector
channels. Detection resolves photon number, without loss or dark counts.
All ten Fock outcomes remain in the sample space.

## Amplitudes, probabilities and measurement

The four inputs are the normalized canonical polarization Bell states. Scattering
gives Psi-minus = (c_H† d_V† - c_V† d_H†)|0>/sqrt(2), and
Psi-plus = i(c_H† c_V† + d_H† d_V†)|0>/sqrt(2).
For Phi-plus/minus the amplitudes in the normalized double-occupation basis are
i/2 at c_H and d_H and +/-i/2 at c_V and d_V. These identities are proved from
U₂ and J; neither the outputs nor the expanded scattering matrix define the network.

Psi-minus has two opposite-polarization, different-port outcomes of probability 1/2.
Psi-plus has two opposite-polarization, same-port outcomes of probability 1/2:
after the PBS these hit two different detectors within one spatial port.
Each Phi state has four double-occupation outcomes of probability 1/4.
Their complete distributions on all ten outcomes are equal, although their pure
output vectors are different. The two same-polarization split-port outcomes have
zero probability for the entire encoded Bell basis and are classified inconclusive.
The classifier is total; no event is dropped or renormalized by postselection.

Detector projectors are compressed by transfer = U₂ J. Their three effects are
proved equal to the projectors onto Psi-minus, Psi-plus, and the sum of the two
Phi projectors. Their sum is I₄. Hermiticity and nonnegative quadratic forms are
proved, as is the Born identity for every complex computational input vector.
The norm convention is the sum of squared complex amplitudes, not the Pi sup norm.

Psi-plus/minus are identified without error with probability one. The success
probability for any normalized nonnegative prior is p(Psi-minus)+p(Psi-plus).
It is exactly 1/2 for the uniform four-state ensemble and 1 for a Psi-only prior.
No deterministic classifier separates the Phi pair from these detector outcomes.
Any stochastic classical postprocessing preserves their identical distributions;
for equal priors, randomized binary guessing has success exactly 1/2. Unequal
priors may favor guessing the more probable state and are not covered by that value.

## Scope and regressions

Kernel regressions cover normalization, Psi output orthogonality, absence of false
identifications, the unused detector outcomes, uniform and Psi-only ensembles.
The external live test checks the Born identity for arbitrary coherent vectors,
positive effects, physical channel classification and classical indistinguishability.

The model assumes ideal passive optics and matching temporal/spectral wave packets
apart from the explicitly encoded polarization. PBS routing and Born photodetection
are model assumptions, not electromagnetic or detector hardware derivations.
This proves one fixed analyzer. The universal Calsamiglia-Luetkenhaus bound over
arbitrary static passive networks with vacuum auxiliaries is not formalized.
Ancilla photons, adaptive measurements, active or nonlinear optics, partial spectral
indistinguishability, photon loss, dark counts and nondestructive heralding are absent.
Python correctness, JSON/SHA-256 correctness and SimLab correspondence remain open.
Scientific priority is not assessed.

Reference: [Calsamiglia and Luetkenhaus, Maximum efficiency of a linear-optical
Bell-state analyzer (2001)](https://arxiv.org/abs/quant-ph/0007058).
The paper's universal upper bound is background, not a theorem claimed by this module.

## Validation

Base snapshot: 9502d727465b13c7895370b4a6dc3f5000616e38.
Required checks: module verify/audit, strict full build, verify-all, live tests,
registry audit, pinned independent audit and knowledge validation.
All required project and export checks passed; measured results follow.

## Source theorem links

- [symmetric_lift_substitution](../../Verification/PhotonicsBellStateAnalyzer.lean#L67)
- [network_unitary](../../Verification/PhotonicsBellStateAnalyzer.lean#L91)
- [two_photon_unitary](../../Verification/PhotonicsBellStateAnalyzer.lean#L120)
- [bell_output_exact](../../Verification/PhotonicsBellStateAnalyzer.lean#L162)
- [probabilities_exact](../../Verification/PhotonicsBellStateAnalyzer.lean#L183)
- [effects_exact](../../Verification/PhotonicsBellStateAnalyzer.lean#L262)
- [povm_completeness](../../Verification/PhotonicsBellStateAnalyzer.lean#L273)
- [effect_positive](../../Verification/PhotonicsBellStateAnalyzer.lean#L301)
- [phi_postprocessing_equal](../../Verification/PhotonicsBellStateAnalyzer.lean#L318)
- [success_probability_exact](../../Verification/PhotonicsBellStateAnalyzer.lean#L361)
- [success_probability_uniform](../../Verification/PhotonicsBellStateAnalyzer.lean#L370)
- [detector_born_rule](../../Verification/PhotonicsBellStateAnalyzer.lean#L386)
- [photonics_bell_state_analyzer_master_suite](../../Verification/PhotonicsBellStateAnalyzer.lean#L444)

## Private snapshot validation: concrete Bell-state analyzer

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 134 |
| Lean sources | 176 under Verification/; 177 including root |
| Strict clean private build | 3625 jobs; no warnings |
| Both full axiom audits | 16721 declarations; no violations |
| Private live tests | 82; no failures or skips; 280.487s |
| Export live tests | 79; no failures or skips; 292.381s |
| Strict clean export build | 3625 jobs; no warnings |

Module verify and audit each covered 736 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. No second independent proof kernel is claimed.
Counts include generated declarations. Both project builds started with empty
.lake/build directories and isolated pinned dependency caches. All 177 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private module integration did not publish a public release.

## Public release validation

The [v0.5.32 report](../../docs/release-v0.5.32.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 134 |
| Lean files under Verification/ | 174 top-level + 2 auxiliary = 176 |
| Root-inclusive sources identical to the private snapshot | 177 |
| Clean strict build | 3625 jobs; no warnings |
| Complete verifier audit | 16721 declarations; no violations |
| Pinned independent full audit | 16721 declarations; no violations |
| Public live tests | 79; no failures or skips; 277.483s |
