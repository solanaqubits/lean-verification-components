---
id: QuantumPOVMInformationallyComplete
language: en
section: quantum-physics
source: Verification/QuantumPOVMInformationallyComplete.lean
source_sha256: 163beda79b3faf9c71a2b96d4991f0dd12713aa77925a84a0f7172ea1ed1bbd4
novelty: not-assessed
status: reviewed
---

# Informationally complete POVMs and exact tomography

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumPOVMInformationallyComplete.lean)

## Model

`POVM` reuses `QuantumPOVMNaimarkDilation.FinitePOVM`: positive semidefinite effects
whose sum is the identity. `HermMat d` is the real vector space of self-adjoint
complex matrices with the Hilbert--Schmidt inner product Re(trace(A B)). Its norm
is induced by this inner product, separately from the matrix operator norm.
`herm_finrank` proves real dimension d² by decomposing complex matrices into
self-adjoint and skew-adjoint parts, identified by multiplication by i.

`is_ic_povm` means the real span of the Hermitian effects is the whole space.
`measurement` is the real-linear map X ↦ (Re(trace(X E_m)))_m. No injectivity,
reconstruction identity or invertibility is built into the definition of a POVM.

## Theorems

- `ic_povm_iff_injective`: spanning is equivalent to measurement injectivity.
- `frame_operator_pos_def`: for nonzero X, ⟨X,S_E X⟩ > 0 under IC. The quadratic
  form is the sum of squares of measurement coordinates.
- `frame_operator_invertible`: finite dimensionality turns this injective linear
  operator into a bijection.
- `dual_frame`: D_m = S_E⁻¹ E_m using the proved linear equivalence.
- `dual_frame_reconstruction_identity`: X = ∑ Re(trace(X E_m)) D_m for all Hermitian X.
- `quantum_state_tomography`: density operators have nonnegative real probabilities
  summing to one and satisfy the dual reconstruction. `hermitian_trace_real` proves
  that taking the real part loses no information for Hermitian inputs and effects.
- `ic_povm_outcome_bound`: every IC-POVM has k ≥ d² outcomes.
- `relabel_ic`, `relabel_frame`, `relabel_dual`: permutations preserve IC and the
  frame operator and permute the canonical dual consistently.

## Explicit models and counterexamples

`qubitTetrahedron` has four effects (I + v_m · σ)/4, with tetrahedral Bloch vectors
(1,1,1), (1,-1,-1), (-1,1,-1), (-1,-1,1), each divided by sqrt(3).
Positivity and completeness are proved directly. `tetra_projector` proves that
2E_m is an idempotent of trace one; `tetra_symmetric_overlap` gives trace(E_i E_j)
= 1/4 on the diagonal and 1/12 otherwise. `qubit_tetrahedron_ic_povm` proves IC
using the explicit frame formula S(X) = (X + trace(X) I)/6.
This is a concrete qubit SIC, not an all-dimension SIC existence assumption.

`scalar_ic` covers d = 1. `onb_measurement_not_ic` rules out every d-outcome POVM
when d ≥ 2, including `basisPOVM`. The distinct density operators `phasePlus`
and `phaseMinus` have identical basis-measurement probabilities; the tetrahedral
measurement distinguishes them. Regression examples reconstruct a pure qubit
and I/2 and verify relabeling by a nontrivial swap.

## Clean Water

The reconstruction is algebraic and uses exact theoretical probabilities. The
canonical inverse is defined noncomputably as a linear equivalence; no efficient
numerical inversion algorithm is claimed. Dual operators need not be positive.
SIC existence in arbitrary dimensions (Zauner's conjecture), finite samples,
shot noise, confidence intervals, numerical conditioning and maximum-likelihood
estimation are not modeled. Python, JSON/SHA-256 and SimLab correspondence
obligations remain open. Mathematical novelty is not assessed.

Strict module verification, full project checks, live regressions and axiom audits
are recorded in the validation snapshot after completion. Only propext,
Classical.choice and Quot.sound are permitted.

Reference: [Scott (2006), Tight informationally complete quantum measurements](https://arxiv.org/abs/quant-ph/0604049).
