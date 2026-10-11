---
id: PhotonicsQuantumTeleportation
language: en
section: quantum-physics
source: Verification/PhotonicsQuantumTeleportation.lean
source_sha256: ef9f9d795bdcdbd2b74d8b1a401092b9a03dd20583df39e1c5df79451cb42d38
novelty: not-assessed
status: reviewed
---

# Conditional linear-optical quantum teleportation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/PhotonicsQuantumTeleportation.lean)

## Physical construction

The input is an arbitrary polarization qubit A and a supplied ideal Bell resource
Phi-plus on B,C. Alice holds A,B; Bob holds C. The model uses the invariant sector
with two photons in Alice's four modes and one photon in Bob's two modes:
Sector = Fin 10 × Fin 2, of cardinality 20. It does not construct the entire
56-dimensional three-photon sector. The Fin 20 state interface is a reindexing.
The resource embedding has entries sqrt(2)/2 times the existing analyzer's dual-rail
embedding J, and its isometry is proved. Local evolution is U₂ ⊗ I₂, using the
actual optical two-photon network of module 134. Its unitarity is proved.

For each of the ten orthogonal Fock detector outcomes, the corresponding block
of (U₂ ⊗ I₂) resourceEmbedding defines a 2×2 Kraus operator on Bob's qubit.
The explicit coefficient table is a proved expansion of these blocks, not the
definition of the instrument. Kraus completeness is derived: sum M_k† M_k = I₂.
Branch grouping uses the imported total detector classifier, and branch positivity
is proved for positive semidefinite inputs.

## Channels, probabilities and recovery

For every complex 2×2 matrix rho, the grouped branch maps are
E_minus(rho) = (1/4) XZ rho (XZ)†,
E_plus(rho) = (1/4) X rho X†, and
E_inconclusive(rho) = (1/2)(P0 rho P0 + P1 rho P1).
The two successful branches each contain two detector outcomes. The inconclusive
class has four double-occupation outcomes and two identically zero Kraus operators;
there are not six nonzero double-occupation outcomes.

For trace-one inputs, the branch traces are 1/4, 1/4, 1/2, hence success is exactly
1/2 independently of the input, including mixed states. The density predicate
requires positive semidefiniteness and trace one. Corrections ZX and X are proved
unitary; they yield rho/4 on each successful branch. Their sum is rho/2, and division
by its success probability recovers rho exactly. Squared Uhlmann fidelity is defined
using the continuous-functional-calculus positive square root:
|Tr sqrt(sqrt(rho) sigma sqrt(rho))|². Its value after recovery is proved to be one
for every density operator. This is not a purity surrogate: the maximally mixed
regression has fidelity one and Tr(rho²) = 1/2.

The full nonselective channel is Tr(rho) I₂/2. Its equality to the partial trace of
the evolved joint state, and to the partial trace before Alice's optics, is proved.
Thus for normalized input Bob sees I₂ without Alice's classical outcome.
No-signalling concerns the uncorrected, unconditioned channel; postselection and
feed-forward explicitly require the detector record to reach Bob.

## Bridge and regressions

Contraction of the physical Bell resource with each of the four canonical Bell
vectors yields one half of the branch amplitude prescribed by
QuantumTeleportationProtocol. The two physically resolved contractions are linked
to their individual detector Kraus operators, including their relative signs and
reflection phases. The correction matrices also match the existing protocol.
This does not turn the unresolved Phi pair into an accessible four-outcome Bell
measurement, and does not claim deterministic optical teleportation.

Regressions cover |0>, |1>, |+>, |+i>, the maximally mixed input, trace preservation
and the two dark outcomes. The requested counterexample on |+> would be false:
using Z instead of ZX leaves residual X (up to global phase), which preserves |+>.
The module proves that exception and gives genuine failures: |0> becomes |1>, and
|+i> becomes |-i>, both with squared fidelity zero. For conventional Pauli Y,
ZX = iY; the proofs use explicit X,Z matrices and do not rely on a Y phase label.

## Clean Water boundaries

This is conditional teleportation with success probability 1/2 for the specific
passive analyzer and an ideal supplied entangled resource. Detector projection,
Born probabilities, matching spectral/temporal modes and ideal classical
feed-forward are assumptions of the finite quantum model. Resource generation,
wave-packet distinguishability, losses, dark counts, detector imperfections,
classical-channel delays, universal optical discrimination bounds and deterministic
teleportation architectures are not modeled. This model derives the finite
instrument, not electromagnetic hardware behavior or a universal optimality bound.
Python, JSON/SHA-256 and SimLab correctness obligations remain open.
Scientific novelty is not assessed.

References: [Bennett et al., Teleporting an unknown quantum state (1993)](https://people.disim.univaq.it/~serva/teaching/Bennet.1993.pdf);
[squared fidelity convention](https://quantumai.google/reference/python/cirq/fidelity).

## Validation

Base snapshot: 59aa296435696dbe388d0e19a110f81c13e8b578.
All required project and export checks passed; measured results follow.

## Source theorem links

- [resource_embedding_isometry](../../Verification/PhotonicsQuantumTeleportation.lean#L35)
- [kraus_exact](../../Verification/PhotonicsQuantumTeleportation.lean#L82)
- [kraus_completeness](../../Verification/PhotonicsQuantumTeleportation.lean#L91)
- [branch_exact](../../Verification/PhotonicsQuantumTeleportation.lean#L107)
- [pauli_corrections_exact](../../Verification/PhotonicsQuantumTeleportation.lean#L138)
- [no_signalling_partial_trace](../../Verification/PhotonicsQuantumTeleportation.lean#L211)
- [teleportation_fidelity_one](../../Verification/PhotonicsQuantumTeleportation.lean#L237)
- [bridge_to_quantum_teleportation_protocol](../../Verification/PhotonicsQuantumTeleportation.lean#L270)
- [counterexample_wrong_relative_phase](../../Verification/PhotonicsQuantumTeleportation.lean#L380)
- [reg_maximally_mixed](../../Verification/PhotonicsQuantumTeleportation.lean#L410)
- [photonics_quantum_teleportation_master_suite](../../Verification/PhotonicsQuantumTeleportation.lean#L463)

## Private snapshot validation: conditional optical teleportation

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 135 |
| Lean sources | 177 under Verification/; 178 including root |
| Strict clean private build | 3725 jobs; no warnings |
| Both full axiom audits | 16901 declarations; no violations |
| Private live tests | 83; no failures or skips; 268.81s |
| Export live tests | 80; no failures or skips; 287.295s |
| Strict clean export build | 3725 jobs; no warnings |

Module verify and audit each covered 1119 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 178 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

Squared Uhlmann fidelity uses the positive CFC matrix square root. For mixed I/2,
fidelity is one while purity is one half. The requested |+> wrong-correction
counterexample is false; the module proves that exception and fidelity-zero
counterexamples on |0> and |+i>.

## Public release validation

The [v0.5.33 report](../../docs/release-v0.5.33.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 135 |
| Lean files under Verification/ | 175 top-level + 2 auxiliary = 177 |
| Root-inclusive sources identical to the private snapshot | 178 |
| Clean strict build | 3725 jobs; no warnings |
| Complete verifier audit | 16901 declarations; no violations |
| Pinned independent full audit | 16901 declarations; no violations |
| Public live tests | 80; no failures or skips; 276.334s |
