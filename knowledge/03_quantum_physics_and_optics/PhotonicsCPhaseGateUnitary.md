---
id: PhotonicsCPhaseGateUnitary
language: en
section: quantum-physics
source: Verification/PhotonicsCPhaseGateUnitary.lean
source_sha256: 272d7c0db99de811ec9a4cc3612d26948b936b1dc60ec78f86fe7a4ab0095884
novelty: not-assessed
status: reviewed
---

# Postselected photonic controlled-Z gate

[Section](../quantum-physics/README.md) · [Lean](../../Verification/PhotonicsCPhaseGateUnitary.lean)

## Model and proof contract

Modes are a₀,a₁,b₀,b₁,v_a,v_b. The two-boson occupation basis enumerates
all 21 unordered pairs (i,j), i≤j. Double occupations use the normalized
creation monomial x_i²/√2; distinct occupations use x_i x_j. The theorem
symmetric_lift_substitution proves the coefficient formula for an arbitrary
complex six-mode matrix. This is a finite homogeneous-polynomial model,
not an infinite Fock-space construction or a proof of canonical commutation relations.

The three disjoint lossless splitters act on (a₀,v_a), (a₁,b₁), (b₀,v_b).
Each uses the imported B(T)=[[√T,i√(1−T)],[i√(1−T),√T]], with 0≤T≤1.
The six-mode matrix and its normalized 21-dimensional two-boson lift are unitary.
The encoding J puts one photon in each logical rail pair and no photons in the
auxiliary modes. J†J=I; JJ† is an orthogonal acceptance projector.

The success operator is DEFINED by compression K(T)=J† U_two_photon_six(T) J.
Its diagonal diag(T,T,T,2T−1) is PROVED from scattering, not assumed.
At T=1/3, K=CZ/3 and K†K=I/9. The squared-norm success probability is 1/9
for every normalized input; the normalized branch is CZψ. For every matrix ρ,
KρK†=(1/9)CZρCZ†, in particular for density matrices. Born-rule interpretation
and ideal coincidence selection are modeling assumptions.

CZ is unitary, Hermitian and involutive. Conjugation maps X⊗I to X⊗Z and
I⊗X to Z⊗X, and fixes both local Z operators. CZ|++⟩ is the graph state
(1,1,1,−1)/2, not literally a computational-basis Bell vector. A local Hadamard
maps it to Φ⁺. Its global density is pure, both reduced densities equal I₂/2,
and reduced purity is 1/2. A product-state purity theorem and an independent
zero-determinant criterion connect these computations to pure-state separability;
the graph state is proved not to factor into local vectors.

## Regressions and boundaries

All four basis inputs have success probability 1/9 and signs (+,+,+,−).
At T=1/2, K=diag(1/2,1/2,1/2,0); the |11⟩ component bunches in central
computational modes and is rejected by coincidence selection. This is not
leakage into the auxiliary vacuum modes for that particular input.
At T=1, K=I. The balanced splitter is not a CZ realization in this network.

The full scattering is unitary; K is a conditional contraction. An exactly
known probability 1/9 does not mean deterministic success. Output coincidence
postselection is not a nondestructive herald. No scalable KLM architecture,
Kerr interaction, photon loss, imperfect detectors, partial distinguishability,
wave-packet spectra, timing dependence or physical hardware implementation is proved.
Python, JSON/SHA-256 and SimLab → Lean correspondence remain open obligations.
Scientific priority is not assessed.

Reference: [Ralph, Langford, Bell and White, PRA 65, 062324 (2002)](https://arxiv.org/abs/quant-ph/0112088).
The formal network uses the project's complex phase convention and isolates
the controlled-sign part; exact identity with the paper's CNOT diagram is not claimed.

## Validation

Base snapshot: 035b98853ca060ea70ea70815a56ae55d0d7e1d4.
The required checks are module verify/audit, strict full build, verify-all,
live unittest, registry audit, pinned independent full audit, and knowledge validation.
All required checks passed; measured results follow below.

## Private snapshot validation: postselected photonic CZ gate

[Contract](PhotonicsCPhaseGateUnitary.md) · [Hashes and commands](../../tools/validation_snapshot.json)

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 130 |
| Lean files under Verification/ | 170 top-level + 2 support = 172 |
| Root-inclusive byte-identical export | 173 sources |
| Clean strict private build | 3621 jobs; no warnings |
| Both full axiom audits | 15177 declarations; no violations |
| Private live tests | 78; no failures or skips; 262.074s |
| Export live tests | 75; no failures or skips; 275.318s |
| Export clean strict build | 3621 jobs; no warnings |

Module verify and audit each covered 510 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor source is pinned to 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; auditor source toolchain records v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not asserted.
Both project build directories started empty, with isolated copies of pinned dependency caches.
Counts include generated declarations. Integration is idempotent. The source HEAD and 406 tracked
files outside simulations/ are preserved. No task writes to simulations/; this earlier check did not publish a public release.


## Source theorem links

- [symmetric_lift_substitution](../../Verification/PhotonicsCPhaseGateUnitary.lean#L63)
- [network_unitary](../../Verification/PhotonicsCPhaseGateUnitary.lean#L81)
- [two_photon_six_unitary](../../Verification/PhotonicsCPhaseGateUnitary.lean#L449)
- [postselected_kraus_exact](../../Verification/PhotonicsCPhaseGateUnitary.lean#L502)
- [ralph_cphase_exact](../../Verification/PhotonicsCPhaseGateUnitary.lean#L518)
- [cphase_success_prob_invariant](../../Verification/PhotonicsCPhaseGateUnitary.lean#L546)
- [density_matrix_evolution](../../Verification/PhotonicsCPhaseGateUnitary.lean#L551)
- [cz_pauli_conjugation](../../Verification/PhotonicsCPhaseGateUnitary.lean#L578)
- [cz_graph_state_entanglement](../../Verification/PhotonicsCPhaseGateUnitary.lean#L681)
- [product_reduced_purity](../../Verification/PhotonicsCPhaseGateUnitary.lean#L625)
- [graph_bell_local_equivalence](../../Verification/PhotonicsCPhaseGateUnitary.lean#L664)
- [photonics_cphase_gate_master_suite](../../Verification/PhotonicsCPhaseGateUnitary.lean#L766)

## Public release validation

The [v0.5.28 report](../../docs/release-v0.5.28.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 130 |
| Lean files under Verification/ | 170 top-level + 2 auxiliary = 172 |
| Root-inclusive sources identical to the private snapshot | 173 |
| Clean strict build | 3621 jobs; no warnings |
| Complete verifier audit | 15177 declarations; no violations |
| Pinned independent full audit | 15177 declarations; no violations |
| Public live tests | 75; no failures or skips; 269.270s |
