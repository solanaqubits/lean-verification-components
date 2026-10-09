---
id: PhotonicsBeamSplitterPhaseShift
language: en
section: quantum-physics
source: Verification/PhotonicsBeamSplitterPhaseShift.lean
source_sha256: d2f7348a4df08003c27390f9a1dcd9c877682d9c5b76cec128d4f7de6e1fb9d9
novelty: not-assessed
status: reviewed
---

# Complex beam splitter and Mach–Zehnder phase response

[Section](../quantum-physics/README.md) · [Lean](../../Verification/PhotonicsBeamSplitterPhaseShift.lean)

## Model and operator convention

For real 0≤T≤1, set t=√T and r=√(1−T). The complex two-mode splitter is
B=[[t, i r],[i r,t]]. The arm phase is D(φ)=diag(exp(iφ),1); the complete
interferometer is U=B† D B. The second splitter is explicitly the inverse of
the first. Other port/phase conventions need a separate change of basis.
The reflection factor i equals exp(iπ/2) in this symmetric lossless model.
This is not a universal law of reflection; a zero component has no defined
relative phase at the endpoints.

Both B†B=BB†=I and U†U=UU†=I are proved. For arbitrary complex input vectors,
the sum of squared complex moduli and its square root are preserved.
This is the Hermitian Euclidean norm, not the supremum norm of a function space.

## Derived output and probabilities

The input is the actual column (1,0), output=U·input, and each probability is
defined as Complex.normSq of the corresponding output component. The proofs derive
c0=T exp(iφ)+(1−T) and c1=i√T√(1−T)(1−exp(iφ)); probability laws are not assumptions.

P0=1−4T(1−T)sin²(φ/2), P1=4T(1−T)sin²(φ/2).
Both probabilities lie in [0,1], sum to one and have period 2π. At T=0 or T=1,
P0=1 and P1=0 for every phase. At T=1/2 the probabilities become cos²(φ/2)
and sin²(φ/2). Multiplication by I0≥0 gives exactly the existing
SolarisMithraCore constructive/destructive intensities, with total power I0.

## Extrema, visibility and propagation

For I0>0, port-0 intensity is bounded below by I0(2T−1)² and above by I0.
These values are attained at φ=π and φ=0 respectively. The certified extrema
construct a valid MithraicPhaseCollapse.InterferencePattern with visibility
V=(1−(2T−1)²)/(1+(2T−1)²)=4T(1−T)/(1+(2T−1)²), equal to one at T=1/2.
A constant phase offset leaves both extrema unchanged; their locations become
−offset and π−offset. A static operating-point shift is not loss of contrast
or decoherence. Dependence on path difference follows by substitution under
the explicit external premise φ=κΔL+φ0. No propagation equation is derived;
if κ=0, scanning ΔL does not scan the full phase curve.

## Theorems and regressions

Main declarations: splitter_unitary, mzi_unitary, mzi_output_amplitudes,
mzi_probabilities_exact, mzi_prob_properties, mzi_endpoint_probabilities,
mzi_balanced_bridge_to_solaris, mzi_intensity_extrema,
mzi_visibility_pattern_bridge, mzi_static_phase_extrema and mzi_phase_geometric_affine.
The master theorem is photonics_beam_splitter_phase_shift_master_suite.

Kernel regressions cover arbitrary complex inputs, endpoint splitters, the dark
balanced port, T=1/4 probabilities (1/4,3/4) at π and visibility 3/5, unchanged
extrema after an arbitrary phase offset, zero input power, the Solaris bridge
and the zero-slope geometric case. Existing subject modules remain unchanged.

## Clean Water

The results follow from the specified lossless matrix model, not from Maxwell's
equations. Waveguide dispersion, polarization, absorption, stochastic phase noise,
decoherence, detectors, full optical Fock-space dynamics and hardware synthesis
are outside this module. The old real beam-splitter model remains a separate
convention; this module does not assert a new Fock-space lift or a derived device model.
Python, JSON/SHA-256 and SimLab-to-Lean correspondence remain open obligations.
Scientific priority is not assessed. See [commands and source hashes](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `2dba8201d6046e7017c2353c95941dd5d51237f8`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 126 |
| Lean files under Verification/ | 166 top-level + 2 support = 168 |
| Root-inclusive byte-identical export | 169 sources |
| Clean strict private build | 3617 jobs; no warnings |
| Both full axiom audits | 14415 declarations; no violations |
| Private live tests | 74; no failures or skips; 263.155s |
| Export live tests | 71; no failures or skips; 275.022s |
| Export clean strict build | 3617 jobs; no warnings |

Module verify and audit each covered 255 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor source is pinned to 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not asserted.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. Integration is idempotent.
Prior subject proof sources, original HEAD and 406 tracked files outside simulations/
are preserved. This task makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.24 report](../../docs/release-v0.5.24.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 126 |
| Lean files under Verification/ | 166 top-level + 2 auxiliary = 168 |
| Root-inclusive sources identical to the private snapshot | 169 |
| Clean strict build | 3617 jobs; no warnings |
| Complete verifier audit | 14415 declarations; no violations |
| Pinned independent full audit | 14415 declarations; no violations |
| Public live tests | 71; no failures or skips; 263.419s |
