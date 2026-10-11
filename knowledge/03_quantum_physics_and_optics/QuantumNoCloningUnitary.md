---
id: QuantumNoCloningUnitary
language: en
section: quantum-physics
source: Verification/QuantumNoCloningUnitary.lean
source_sha256: 33882149457e36e20082df17f58deac2424bfd9d1f43fb0f4d431209c90a3e52
novelty: not-assessed
status: reviewed
---

# Unitary no-cloning from quantum state evolution

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumNoCloningUnitary.lean)

## Mathematical contract

Pure vectors are complex d by 1 matrices. Normalized means psi† psi=I_1;
rho(psi)=psi psi† is positive semidefinite and has trace one. A common square
unitary U acts on the pair of d-dimensional systems, with one fixed normalized
blank b. Tensor-vector columns have index Fin 1 x Fin 1; no implicit identification
of differently typed matrices is used. Most algebraic lemmas work for arbitrary d;
the universal impossibility explicitly requires d>=2.

For exact vector cloning, preservation of inner products and tensor factorization
give c=c^2 for the complex overlap c=(psi† phi)(0,0), hence c=0 or c=1.
For density cloning, invariance of the trace of a product under unitary conjugation
gives t=t^2, where t=Tr(rho(psi) rho(phi))=normSq(c). The trace is proved real.
For normalized inputs, 0<=t<=1 follows using the squared Hilbert-Schmidt distance.
The zero-overlap case is equivalent to psi† phi=0. The unit-overlap case is
equivalent to equality of the two pure density matrices.

A unit-modulus phase, including exp(i theta), leaves rho unchanged and gives t=1.
Literal vector cloning of both psi and -psi is impossible; those vectors represent
the same density matrix. This difference is part of the formal contract.

Two distinct coordinate directions supply |0> and |+> with t=1/2 in every d>=2.
No common U with a fixed normalized blank can clone both densities, hence none
can clone all pure states. The vector impossibility follows as a corollary.
The bridge to the older scalar module derives its quadratic hypothesis from
unitary evolution; it is not supplied externally. The BB84 bridge uses the actual
four ket definitions from QuantumBB84ProtocolQBER, not a separate lookup table.

## Positive examples and regressions

An explicit CNOT matrix is unitary, trace preserving, and clones the computational
basis with blank |0>. Applied to |+>|0>, it gives (|00>+|11>)/sqrt(2), which is proved
unequal to every product v tensor w, not merely unequal to |+>|+>.
A unitary copying any one prescribed normalized state with a prescribed normalized
blank exists by the isometry-extension theorem from QuantumPOVMNaimarkDilation.
That existence result uses noncomputable mathematics, not a gate synthesis algorithm.

Regressions check arbitrary dimension, CNOT, overlap 1/2, orthogonal overlap zero,
phase overlap one, the BB84 obstruction and the distinction between vectors and densities.

## Clean Water boundaries

This is exact deterministic unitary cloning of pure states with a common fixed blank
and two output systems. It does not establish a general theorem for arbitrary CPTP
maps with discarded environments. Mixed-state no-broadcasting, probabilistic or
approximate cloning, covariant cloners and physical QKD security are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is not
assessed. Only propext, Classical.choice and Quot.sound are permitted.

## Validation

Base snapshot: 5cfecd3773d40cc2ceca22686e0976416b3df834.
All project and export checks passed; measured results follow.

## Source theorem links

- [trace_overlap](../../Verification/QuantumNoCloningUnitary.lean#L46)
- [vector_cloning_overlap_square](../../Verification/QuantumNoCloningUnitary.lean#L72)
- [density_cloning_overlap_square](../../Verification/QuantumNoCloningUnitary.lean#L102)
- [overlap_bounds](../../Verification/QuantumNoCloningUnitary.lean#L121)
- [overlap_zero_iff](../../Verification/QuantumNoCloningUnitary.lean#L130)
- [overlap_one_iff](../../Verification/QuantumNoCloningUnitary.lean#L140)
- [density_cloning_ortho_or_identical](../../Verification/QuantumNoCloningUnitary.lean#L161)
- [single_state_cloner](../../Verification/QuantumNoCloningUnitary.lean#L197)
- [phase_invariance_exp](../../Verification/QuantumNoCloningUnitary.lean#L241)
- [pair_zero_plus_unclonable](../../Verification/QuantumNoCloningUnitary.lean#L248)
- [no_universal_unitary_cloning](../../Verification/QuantumNoCloningUnitary.lean#L256)
- [bridge_to_quantum_no_cloning_theorem](../../Verification/QuantumNoCloningUnitary.lean#L273)
- [cnot_unitary](../../Verification/QuantumNoCloningUnitary.lean#L286)
- [cnot_clones_computational_basis](../../Verification/QuantumNoCloningUnitary.lean#L293)
- [bell_not_product](../../Verification/QuantumNoCloningUnitary.lean#L310)
- [cnot_entangles_superposition](../../Verification/QuantumNoCloningUnitary.lean#L323)
- [bridge_to_bb84_unclonability](../../Verification/QuantumNoCloningUnitary.lean#L337)
- [opposite_vectors_not_both_cloned](../../Verification/QuantumNoCloningUnitary.lean#L355)
- [vector_cloning_cases](../../Verification/QuantumNoCloningUnitary.lean#L367)
- [quantum_no_cloning_unitary_master_suite](../../Verification/QuantumNoCloningUnitary.lean#L408)

## Private snapshot validation: Exact unitary no-cloning

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 141 |
| Lean sources | 183 under Verification/; 184 including root |
| Strict clean private build | 3731 jobs; no warnings |
| Both full axiom audits | 18166 declarations; no violations |
| Private live tests | 89; no failures or skips; 291.643s |
| Export live tests | 86; no failures or skips; 298.549s |
| Strict clean export build | 3731 jobs; no warnings |

Module verify and audit each covered 1550 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 184
exported Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

Unitary evolution implies c=c^2 for exact vector cloning and t=t^2 for pure-density
cloning. Normalized inputs are orthogonal or have identical densities. Global phase
is handled explicitly. CNOT copies the computational basis but entangles |+>|0>.
Universal cloning in d>=2 and joint BB84 cloning are impossible in this model.
General CPTP cloning, mixed no-broadcasting and physical QKD security are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.39 report](../../docs/release-v0.5.39.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 141 |
| Lean files under Verification/ | 181 top-level + 2 auxiliary = 183 |
| Root-inclusive sources identical to the private snapshot | 184 |
| Clean strict build | 3731 jobs; no warnings |
| Complete verifier audit | 18166 declarations; no violations |
| Pinned independent full audit | 18166 declarations; no violations |
| Public live tests | 86; no failures or skips; 289.434s |
