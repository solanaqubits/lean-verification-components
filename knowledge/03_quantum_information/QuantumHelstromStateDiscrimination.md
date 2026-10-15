---
id: QuantumHelstromStateDiscrimination
language: en
section: quantum-physics
source: Verification/QuantumHelstromStateDiscrimination.lean
source_sha256: 7d1b7feebb39534612c12a8dc169cbad07d391a1005bffb5af4bfd92f4172784
novelty: not-assessed
status: reviewed
---

# Holevo–Helstrom state discrimination

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumHelstromStateDiscrimination.lean)

## Mathematical contract

Density matrices use the existing IsDensityMatrix predicate (positive semidefinite,
trace one). Priors stores nonnegative real weights summing to one. Effect stores a
positive semidefinite matrix E and a positive semidefinite complement I-E. No
commutation of states or effects is assumed. The general theorems do not need a
separate nonempty-dimension hypothesis: density matrices already exclude dimension
zero. FinitePOVM is imported from QuantumPOVMNaimarkDilation; the reference project
has no QuantumInformationPOVM module. The existing mixed probability is prob_dist.

difference_hermitian and difference_trace establish Hermiticity and real trace
p0-p1 for Delta=p0*rho-p1*sigma. success_standard_form identifies p1+Re Tr(E Delta)
with p0 Re Tr(E rho)+p1 Re Tr((I-E) sigma).

## Spectral optimization

spectral_map uses Mathlib's unitary eigenbasis of a Hermitian matrix. Positive and
negative parts use max(lambda,0) and max(-lambda,0); absolute_part uses abs(lambda).
parts_sub and parts_add prove Delta=Delta_plus-Delta_minus and
abs(Delta)=Delta_plus+Delta_minus. Positivity is proved by unitary conjugation.

trace_norm A is explicitly Re Tr(CFC.sqrt(A.conjTranspose*A)). absolute_part_sqrt
proves its agreement with the spectral absolute value for Hermitian A, and
trace_norm_spectral proves the sum of absolute eigenvalues. This is the Schatten
one norm formula, not the ambient Matrix norm or an entrywise absolute sum.

trace_product_nonneg proves nonnegative real trace for the product of two PSD
matrices without assuming they commute. This yields spectral_upper_bound and
helstrom_upper_bound. helstrom_trace_norm_identity gives
p1+Tr(Delta_plus)=(1+trace_norm Delta)/2.

helstrom_effect selects strictly positive eigenvalues and excludes zero ones.
It is a valid effect and an orthogonal projector. helstrom_bound_achievable proves
exact equality, and helstrom_isGreatest proves an attained maximum over all valid
effects. zero_flexible_selector permits independent inclusion of zero eigenvectors;
zero_eigenvalue_choice_irrelevant proves the same optimum for every such choice.
This covers a family of zero-eigenspace choices, without claiming uniqueness or
classifying every possible optimal effect. identical_fair_nonunique exhibits two
distinct optimal effects. effect_povm packages E,I-E as an actual FinitePOVM.

## Classical decision rules and processing

decision_success sums D_j*a_j+(1-D_j)*b_j. guessing sums max(a_j,b_j).
bayes_decision_rule_optimal proves the upper bound for every randomized rule
0<=D_j<=1, and bayes_rule_attains proves attainment by choosing hypothesis zero
when a_j>=b_j (including ties).

guessing_prob specializes to a_j=p0*prob_dist E rho j and b_j=p1*prob_dist E sigma j.
decision_effect and decision_effect_success link every such rule to a valid
binary quantum effect. guessing_prob_le_helstrom bounds all measured guessing
probabilities by the global Helstrom optimum.

guessing_data_processing follows from nonnegative channel entries and column
normalization; it holds even for arbitrary real input scores. Its probabilistic
interpretation uses density matrices and valid priors. guessing_prob_postprocessing_le
uses module 166's actual postprocess_povm and probability identity. Outcome
permutations preserve guessing; erasure to a fixed distribution leaves exactly
max(p0,p1). The fixed reversed-rule example improves from zero to one under bit
inversion; this does not contradict contraction of the optimal decision value.

## Exact regression cases

Identical states have optimum max(p0,p1). Orthogonal qubit basis states have
optimum one for all priors. A zero prior also gives optimum one. The pair
|0><0| and |+><+| is proved noncommuting; for equal priors the trace norm is
1/sqrt(2) and the optimum is (1+1/sqrt(2))/2. This exact calculation uses a proved
positive matrix square root, not numerical diagonalization. Regression declarations
also cover ties, randomized decisions, projectors, zero modes, composed channels,
permutations, erasure and the suboptimal-rule counterexample.

## Clean Water

This is finite-dimensional spectral optimization and classical postprocessing of
fixed measurements. Real spectra and square roots are noncomputable definitions
here; kernel-checked theorems are not certified floating-point algorithms.
Numerical eigensolvers, finite-sample estimation, physical measurement realization,
and general quantum data processing under CPTP maps remain outside scope.

Full Bulletproofs range extraction still needs a degree-bounded multipoint
interpolation contract in y,z; powers of one field scalar are not assumed linearly
independent over that field. Rewinding, computational binding, HVZK and Fiat–Shamir/ROM,
Tendermint accountability with its observation/justification contract, Python,
JSON/SHA-256 and SimLab correspondence remain open. Only propext, Classical.choice
and Quot.sound are allowed. Novelty has not been assessed.

Baseline: c665583189f495470fff135cc5406beaa70af249.
Measured validation: tools/validation_snapshot.json.
Reference: [Watrous, The Theory of Quantum Information, Theorem 3.4](https://cs.uwaterloo.ca/~watrous/TQI/TQI.3.pdf).
