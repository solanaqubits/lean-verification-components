---
id: QuantumChannelTraceDistanceContract
language: en
section: quantum-physics
source: Verification/QuantumChannelTraceDistanceContract.lean
source_sha256: b7b7c95efad3bacbd81ca60ba20921b80cbe7a7533712e04128130cb11434d05
novelty: not-assessed
status: reviewed
---

# Trace distance, distinguishability, and measurement contraction

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumChannelTraceDistanceContract.lean)

## Contract and interfaces

For finite complex density matrices (positive semidefinite, trace one),
trace_distance rho sigma = (1/2)*trace_norm(rho-sigma). The norm is the existing
module 171 definition Re Tr(sqrt(A†A)), proved there equal to the sum of absolute
Hermitian eigenvalues. It is not the ambient matrix norm. No commutation is assumed.
Metric theorems explicitly require density matrices; the definition alone does not
assert a metric on arbitrary matrices. Dimension zero is excluded by existence of
a trace-one density matrix, not an additional nonempty assumption.

FinitePOVM comes from QuantumPOVMNaimarkDilation, and mixed outcome probabilities
are prob_dist from QuantumPOVMInformationEntropy. The project has no
QuantumInformationPOVM module. ClassicalChannel and postprocess_povm reuse module
166; the domain aggregate is QuantumPhysicsFullSuite.

## Proved statements

trace_distance_nonneg, trace_distance_symm, trace_distance_eq_zero_iff,
trace_distance_triangle and trace_distance_le_one prove the metric laws and
0 <= D <= 1 on states. Separation uses the sum of nonnegative absolute eigenvalues:
zero sum forces every eigenvalue to vanish, and the spectral theorem gives zero
matrix. No norm axiom is introduced.

distance_effect is the spectral projector on strictly positive eigenvalues of
rho-sigma, built with module 171's spectral_effect and positive_selector.
distance_effect_projective proves idempotence; Effect supplies positivity and a
positive complement. distance_effect_attains proves Re Tr(E(rho-sigma))=D.
trace_distance_variational_sup is an IsGreatest statement for absolute effect
expectations, with an explicit member attaining the maximum. Symmetry and triangle
follow from these effect bounds. Zero eigenvectors are excluded by this selector;
optimal-measurement uniqueness is not claimed.

trace_distance_helstrom_link proves the equal-prior identity
optimal_success fair rho sigma = (1+D)/2 using the actual module 171 optimum.
The trace distance is defined from the norm, not from this desired identity.

TV p q = (1/2)*sum_j |p_j-q_j|. Its nonnegativity, symmetry, separation, triangle
and unit bound for distributions are proved. tv_contractive_under_classical_channel
proves TV(Mp,Mq)<=TV(p,q) from nonnegative entries and unit column sums; the algebraic
inequality also holds for unnormalized real input vectors.

fair_guessing_tv relates equal-prior Bayes guessing to (1+TV)/2. Together with
module 171's guessing_prob_le_helstrom, it proves tv_le_trace_distance_under_povm.
effect_povm_tv identifies binary-effect TV with the absolute effect expectation.
optimal_povm packages the spectral effect and its complement as a real FinitePOVM;
tv_attains_trace_distance proves equality. measurement_tv_isGreatest proves that
the same binary measurement attains the maximum over all finite outcome counts.

tv_postprocess_le combines measurement and classical contraction. Permutations
preserve TV, and erasure to any fixed distribution yields zero, both for classical
vectors and actual postprocessed POVMs.

## Exact regressions

Equal states have distance zero. Orthogonal |0> and |1> have distance one.
Noncommuting |0> and |+> have distance 1/sqrt(2); Z-basis measurement gives exactly
TV=1/2, strictly smaller. The uninformative binary POVM (0,I) yields zero and loses
all distinguishability for the orthogonal pair. Tests also cover symmetric order,
triangle through the mixed state, optimal attainment, empty classical outcome
vectors, identity, permutations, erasure and composed stochastic channels.

## Clean Water

This module proves analytic finite-dimensional metric and measurement statements.
Real spectral definitions are noncomputable Lean definitions; regression examples
are exact kernel checks, not floating-point diagonalization certificates.
General quantum-channel contraction D(Phi(rho),Phi(sigma))<=D(rho,sigma) is not
modeled here and needs a separate channel contract (for physical channels, CPTP).
Classical postprocessing alone does not establish that theorem. Purity preservation,
general quantum relative-entropy DPI, certified numerical eigensolvers, finite-sample
estimation and physical realization of measurements are outside scope.

Full Bulletproofs range extraction requires degree-bounded multipoint interpolation
in y,z; powers of a single field scalar are not assumed independent over that field.
Rewinding, computational binding, HVZK, Fiat–Shamir/ROM, Tendermint accountable safety,
Python, JSON/SHA-256 and SimLab correspondence obligations remain open. Novelty has
not been assessed.

## Verification and references

Module verify and audit, strict project build, full verifier audit, live regressions,
registry audit, pinned independent axiom audit and catalog check are recorded in
[the validation record](../VERIFICATION.en.md). Only propext, Classical.choice and
Quot.sound are permitted.

Mathematical background: [Watrous, The Theory of Quantum Information, chapter 3](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf).
