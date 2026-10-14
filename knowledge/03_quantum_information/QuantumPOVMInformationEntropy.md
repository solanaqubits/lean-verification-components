---
id: QuantumPOVMInformationEntropy
language: en
section: quantum-physics
source: Verification/QuantumPOVMInformationEntropy.lean
source_sha256: 5f8f1bb94dc841434e0277af1afe51ec5d94e50be195abbce3e4ace89063fbf6
novelty: not-assessed
status: reviewed
---

# Finite POVM entropic uncertainty in bits

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumPOVMInformationEntropy.lean)

## Exact model

The module reuses `QuantumPOVMNaimarkDilation.FinitePOVM`: positive semidefinite
complex matrices whose sum is the identity. For nonzero dimension d, two finite
POVMs E,F and any density matrix rho, `prob_dist` is Re(trace(rho E_j)).
The distribution is nonnegative and normalized. Informational completeness,
rank-one effects, and noncommutativity are not hypotheses.

`xlogx` is zero on the nonpositive half-line and x ln x otherwise. On nonnegative
probabilities it equals x ln x, including zero. `shannon_entropy_bits` is
`-(sum xlogx(p_j))/ln(2)`. Nonnegativity, continuity on the nonnegative cone,
two-point concavity and finite-mixture concavity are proved. Measurement entropy
is also concave in the density matrix via the affine probability map.

`matrix_op_norm` is the norm of `Matrix.toEuclideanCLM` on the complex Euclidean
space. The matrix calculations explicitly use `Matrix.Norms.L2Operator`, not an
entrywise or row-sum norm. `c_overlap` is the maximum of
`norm(sqrt(E_j) * sqrt(F_k))`, using a finite supremum of nonnegative norms.
For d>0, `povm_overlap_bounds` proves 0<c<=1; empty outcome families cannot be
valid POVMs in this dimension.

## Analytic proof, not an assumed inequality

`maassen_uffink_pure_state` proves the general bound for every normalized vector.
The joint complex amplitudes are w_jk = <psi, E_j F_k psi>. Their row and column
sums are the measurement probabilities p_j,q_k, and
`norm(w_jk) <= c sqrt(p_j) sqrt(q_k)` follows from Cauchy--Schwarz and the operator
norm. Zero probabilities cause no division by zero; their amplitudes vanish.

The finite analytic family is
`f(z) = sum_jk w_jk exp(z*((ln p_j + ln q_k)/2 - ln c))`.
At Re(z)=1 its norm is bounded by sum_jk p_j q_k=1. At Re(z)=0, phase-weighted
sums of effects are contractions: they are compressions V* D V through the
existing Naimark isometry, with a diagonal phase contraction D. The finite
exponential sum is differentiable and bounded on the closed strip. Mathlib's
Hadamard three-lines theorem gives norm(f(t))<=1 for 0<=t<=1. Since f(0)=1,
the real right derivative at zero is nonpositive. Computing this derivative
gives the entropy inequality. The phase bound is proved from POVMs, not left as
a hypothesis of the main theorem.

`maassen_uffink_mixed_state` proves, for every positive semidefinite rho of trace 1,

    H_2(P_E^rho) + H_2(P_F^rho) >= -2 ln(c(E,F))/ln(2).

The spectral eigenvalues are a probability distribution; the spectral theorem
expresses rho as their mixture of normalized eigenvector projectors. Measurement
probabilities are the same mixture of pure-state distributions. Finite Jensen
concavity transfers the pure-state bound to all density matrices.

`bound_strictly_positive` requires 0<c<1. `bound_monotone_in_c` proves the bound
is nonincreasing with c>0. This does not assert universal entropy monotonicity
under arbitrary measurement changes. `squared_overlap_convention` records that
-log_2(c^2) = -2 log_2(c). Coles et al. use the squared-overlap convention in
Section III.D, equations (49)-(50).

## Exact examples and symmetry

- Pauli Z/X: c=1/sqrt(2), analytic lower bound exactly one bit, for every density.
- The Z eigenstate |0><0|: entropies 0 and 1, attaining the lower bound.
- I/2: both entropies 1, with sum 2.
- Identical projective Z measurements: c=1 and zero bound, attained on |0>.
  Equality E=F does not imply c=1 for arbitrary nonprojective POVMs.
- In dimension three, the standard basis and the basis consisting of |0> and
  (|1> +/- |2>)/sqrt(2) have noncommuting effects. They share |0>, have c=1 and
  both outcome entropies zero on its density. Noncommutativity alone is insufficient.
- Relabeling either outcome family preserves overlap; relabeling a distribution
  preserves entropy. Prepending a zero effect preserves overlap and entropy.

`QuantumPOVMInformationEntropySuite` packages the general analytic theorems,
coefficient bounds, exact examples, zero effects and label invariance. The live
regression compiles 30 kernel examples, including universally quantified bounds.
There is no numerical evaluator or floating-point oracle for logarithms.

## Clean Water

This is exact finite-dimensional real/complex mathematics. Square roots,
logarithms and spectral choices are noncomputable definitions. No efficient
numerical entropy implementation or certificate for transcendental evaluations
is asserted. Finite shot samples, statistical uncertainty, quantum memory or
side information, and cryptographic protocol security are outside this module.
Existing Bulletproofs witness-extraction, HVZK and Fiat-Shamir/ROM obligations
remain open, as do Python, JSON/SHA-256 and SimLab correspondence obligations.
Mathematical novelty is not assessed. Only propext, Classical.choice and
Quot.sound are permitted; measured verification is recorded in the validation snapshot.

Source reference snapshot: 22f869e47aa9b9d9703bee7520b3798e693f6b15.

Reference: [Coles, Berta, Tomamichel and Wehner (2017), Entropic uncertainty relations and their applications, Section III.D](https://arxiv.org/pdf/1511.04857).
