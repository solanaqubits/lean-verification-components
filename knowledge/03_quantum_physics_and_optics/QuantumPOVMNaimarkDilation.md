---
id: QuantumPOVMNaimarkDilation
language: en
section: quantum-physics
source: Verification/QuantumPOVMNaimarkDilation.lean
source_sha256: c7d811ec4745854286ab54aacb463bcefc6909d1d3a43b7d2128766f1f335301
novelty: not-assessed
status: reviewed
---

# Finite POVMs and Naimark dilation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumPOVMNaimarkDilation.lean)

## Mathematical contract

A FinitePOVM consists of k positive semidefinite complex d by d effects E_m
whose sum is I. The roots F_m are defined by Mathlib CFC.sqrt, with positivity,
Hermiticity and F_m F_m = E_m proved. No factorization or dilation witness is
assumed. These are noncomputable mathematical definitions, not a numerical
square-root algorithm or an executable synthesis procedure.

The rectangular matrix V has entries V((i,m),j)=F_m(i,j). The extended space
has dimension d*k. Orthogonal projectors Pi_m=I_d tensor |m><m| sum to I.
The module proves V†V=I and V†Pi_m V=E_m. Cyclic trace identities give equality
of Born traces for every complex matrix M, without a trace-one assumption.
For density matrices the lifted state is positive with trace one; probabilities
are real, nonnegative and normalized. Born's rule supplies the physical model;
its mathematical consequences, not the physical postulate itself, are proved.

For k>=1, J embeds into the fixed ancilla |0>. A general lemma extends an isometry
on the range of J to the whole finite Euclidean space using Mathlib's
LinearIsometry.extend. Its matrix U satisfies U†U=UU†=I and UJ=V.
Consequently V M V†=U(M tensor |0><0|)U† for every M. Existence of U is proved,
not postulated. Its gate decomposition and optical realization are not provided.
The algebraic lemmas also allow zero-dimensional index types where meaningful;
the intended physical application has d>=1 and k>=1.

## Instruments and bridges

Partial trace is explicitly the sum of diagonal ancilla blocks. Applying it to
Pi_m V M V† Pi_m yields F_m M F_m, the unnormalized branch of the canonical
Lueders instrument. A normalized conditional state would require a nonzero
outcome probability; no division by zero is hidden in this statement.

POVM effects do not specify the state update uniquely. The singleton Kraus
families {I} and {X} both have effect I but send |0><0| to distinct density
matrices. The Bell-analyzer bridge instantiates the three existing detector
effects as a FinitePOVM. The depolarizing bridge uses E_j=K_j†K_j and proves
agreement with each actual Kraus-branch trace for physical p in [0,1]. It does
not identify the canonical Lueders instrument with the depolarizing channel.

Regressions cover singleton measurements (with the necessary reindexing
Fin d x Fin 1 to Fin d), zero effects, projective square roots and binary effects
t I, (1-t) I. For 0<t<1 and d>=1 the first binary effect is proved nonprojective;
its probability on a density matrix is t, the other probability is 1-t.

## Clean Water boundaries

This is a general finite-dimensional Naimark theorem for finite POVMs.
Infinite-dimensional spaces, spectral measures, minimality of the dilation,
physical circuit synthesis and hardware implementation are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is
not assessed. Only propext, Classical.choice and Quot.sound are permitted.

Reference: [Watrous, Lecture 5, Naimark's theorem](https://cs.uwaterloo.ca/~watrous/TQI-notes/TQI-notes.05.pdf).

## Validation

Base snapshot: 09e41d2eca4d4b88ac8c779d8b7d60622b51aaa3.
All project and export checks passed; measured results follow.

## Source theorem links

- [sqrt_positive](../../Verification/QuantumPOVMNaimarkDilation.lean#L26)
- [sqrt_hermitian](../../Verification/QuantumPOVMNaimarkDilation.lean#L29)
- [sqrt_square](../../Verification/QuantumPOVMNaimarkDilation.lean#L32)
- [projector_mul](../../Verification/QuantumPOVMNaimarkDilation.lean#L54)
- [projectors_complete](../../Verification/QuantumPOVMNaimarkDilation.lean#L60)
- [isometry_v](../../Verification/QuantumPOVMNaimarkDilation.lean#L69)
- [naimark_dilation_exact](../../Verification/QuantumPOVMNaimarkDilation.lean#L79)
- [born_rule_preservation](../../Verification/QuantumPOVMNaimarkDilation.lean#L90)
- [density_matrix_dilation](../../Verification/QuantumPOVMNaimarkDilation.lean#L99)
- [unitary_between_isometries](../../Verification/QuantumPOVMNaimarkDilation.lean#L135)
- [unitary_dilation_extension](../../Verification/QuantumPOVMNaimarkDilation.lean#L175)
- [lueders_instrument_reduction](../../Verification/QuantumPOVMNaimarkDilation.lean#L186)
- [probability_distribution](../../Verification/QuantumPOVMNaimarkDilation.lean#L216)
- [bridge_to_bell_state_analyzer](../../Verification/QuantumPOVMNaimarkDilation.lean#L245)
- [bridge_to_depolarizing_channel](../../Verification/QuantumPOVMNaimarkDilation.lean#L256)
- [projective_sqrt](../../Verification/QuantumPOVMNaimarkDilation.lean#L263)
- [singleton_isometry](../../Verification/QuantumPOVMNaimarkDilation.lean#L276)
- [binary_nonprojective](../../Verification/QuantumPOVMNaimarkDilation.lean#L294)
- [counterexample_povm_not_instrument](../../Verification/QuantumPOVMNaimarkDilation.lean#L312)
- [quantum_povm_naimark_dilation_master_suite](../../Verification/QuantumPOVMNaimarkDilation.lean#L360)

## Private snapshot validation: Finite Naimark dilation

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 140 |
| Lean sources | 182 under Verification/; 183 including root |
| Strict clean private build | 3730 jobs; no warnings |
| Both full axiom audits | 18067 declarations; no violations |
| Private live tests | 88; no failures or skips; 286.149s |
| Export live tests | 85; no failures or skips; 296.979s |
| Strict clean export build | 3730 jobs; no warnings |

Module verify and audit each covered 1437 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 183
exported Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

The general finite POVM dilation uses CFC square roots, an explicit isometry and
orthogonal outcome projectors. Unitary extension with a fixed pure ancilla is
proved, as are Born probabilities, density preservation and Lueders reduction.
POVM statistics do not uniquely determine a quantum instrument. Infinite-dimensional
spectral measures, minimal dilation and physical circuit synthesis are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.38 report](../../docs/release-v0.5.38.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 140 |
| Lean files under Verification/ | 180 top-level + 2 auxiliary = 182 |
| Root-inclusive sources identical to the private snapshot | 183 |
| Clean strict build | 3730 jobs; no warnings |
| Complete verifier audit | 18067 declarations; no violations |
| Pinned independent full audit | 18067 declarations; no violations |
| Public live tests | 85; no failures or skips; 279.862s |
