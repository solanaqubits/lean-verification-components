---
id: QuantumChannelClassicalDataProcessing
language: en
section: quantum-physics
source: Verification/QuantumChannelClassicalDataProcessing.lean
source_sha256: 306bbb3609f47d03fb4526b1a3a526eed96278a89d42b93a1774bf7e1d687706
novelty: not-assessed
status: reviewed
---

# Classical postprocessing of POVMs and KL data processing

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumChannelClassicalDataProcessing.lean)

## Exact model

ClassicalChannel m n has a nonnegative real matrix M(k,j) with each input column
summing to one. BistochasticChannel m additionally requires every row to sum to one.
The channel acts on a column distribution by (Mp)(k)=sum_j M(k,j)*p(j).
FinitePOVM is reused from QuantumPOVMNaimarkDilation; there is no separate
QuantumInformationPOVM source in the reference project. Its effects are positive
semidefinite complex matrices summing to the identity. The existing probability
map is prob_dist E rho = Re(trace(rho * E_j)).

postprocess_povm constructs effects sum_j (M(k,j):Complex) • E_j, with proofs of
positive semidefiniteness and completeness. Hermiticity follows from positivity.
The probability map commutes with the classical channel for every input matrix;
for density matrices the probabilities are nonnegative and normalized. Identity,
relabeling by equivalences, channel composition and associativity are proved.
Zero effects are allowed and a weighted sum of zero contributions remains zero.
No nonzero-dimension assumption is required for these algebraic identities;
probabilistic claims explicitly require density matrices or normalized distributions.

## Finite relative entropy and the support boundary

AbsContinuous p q means p(j)>0 implies q(j)>0. All input distributions in the
KL nonnegativity and data processing theorems have nonnegative entries and total
mass one. Absolute continuity is preserved by every channel.

kl_term a b is zero for a<=0 and otherwise a*log(a/b). kl_divergence sums this
formula in nats; kl_divergence_bits divides by log(2). The total formula does NOT
give a finite-divergence interpretation to a>0,b=0. Meaningful input KL theorems
require absolute continuity. checked_kl returns some only for two valid distributions
with the support condition and returns none for a singular input. It is a
noncomputable mathematical guard over exact reals, not a floating-point decision procedure.
Algebraic permutation/self identities concern the total formula; erasure can repair
an input support mismatch, so its output KL is zero even for singular input pairs.
No DPI claim with a finite singular input KL is made.

## Analytic proof

The finite log-sum theorem holds for arbitrary nonnegative a,b with a<<b, without
normalization. If sum b=0, absolute continuity forces every a entry to zero.
Otherwise Jensen's inequality for the Mathlib theorem Real.convexOn_mul_log is
applied to weights b(j)/sum b and arguments a(j)/b(j). Zero b entries are treated
explicitly and force zero a entries. Multiplication by the positive total yields
log-sum. Nonnegativity of KL follows from unit totals. Applying log-sum to each
output row and using column normalization proves KL data processing. The POVM
corollary uses the already proved equality of probability maps; it is not assumed.

For bistochastic matrices, finite Jensen for Real.negMulLog is applied row by row;
column normalization recovers the input entropy sum. Strict concavity additionally
proves that every nonuniform binary distribution strictly gains entropy through
a binary symmetric channel when 0<epsilon<1/2. The proof is analytic, not a sampled
numerical comparison. Natural logarithms are exact and Shannon entropy is in bits.

## Regression coverage

Kernel regressions cover identity and permutation invariance, channel composition,
normalization, support preservation, KL in nats/bits, zero entries and empty finite
sums, singular-input refusal, full erasure and exact binary noise at 0, 1/4 and 1/2.
For a fair bit, entropy is exactly one; deterministic merging into a single outcome
has entropy zero. Hence entropy growth is not asserted for arbitrary stochastic
coarse-graining. POVM regressions use Pauli Z, mixed-state theorem parameters,
positive effects, completeness, relabeling and an explicit zero output effect.
All regression assertions are Lean kernel proofs. No executable logarithm benchmark
or numerical certificate is claimed.

## Clean Water

This module proves classical KL contraction for distributions of finite quantum
measurements. It does not prove general Umegaki quantum relative-entropy DPI for
CPTP maps, an extended-real infinity API, quantum memory bounds, finite-sample
estimation or numerical logarithm certification. Exact real operations are noncomputable.

Tendermint accountable safety still needs a complete observation/justification
contract for Amnesia: missing Polka in a partial observer log is not evidence that
a validator never received it. Signature attribution and slashing evidence extraction
remain open. Bulletproofs knowledge extraction, computational binding, HVZK,
Fiat-Shamir/ROM and external Python, JSON/SHA-256 and SimLab correspondence remain open.
Scientific novelty is not assessed.

## Verification and references

The module is checked with verifier_skill verify and audit, strict Lake build,
full live regressions, registry and pinned independent axiom audits. Allowed axioms
are only propext, Classical.choice and Quot.sound. See the current
[validation record](../VERIFICATION.en.md) for measured full-project results.

- [Polyanskiy and Wu, MIT 6.441 lecture notes](https://www.ocw.mit.edu/courses/6-441-information-theory-spring-2016/pages/lecture-notes/): classical information measures and data processing.
- Mathlib Analysis.SpecialFunctions.Log.NegMulLog and Analysis.Convex.Jensen supply
  proved analytic convexity/concavity and finite Jensen; no new axioms are introduced.

## Proof entry points

- [`postprocess_povm`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L209)
- [`postprocess_prob`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L226)
- [`postprocess_compose`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L238)
- [`compose_associative`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L247)
- [`abs_continuous_preserved`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L74)
- [`log_sum_inequality`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L110)
- [`kl_divergence_nonneg`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L159)
- [`kl_data_processing_inequality`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L165)
- [`kl_data_processing_bits`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L184)
- [`povm_kl_data_processing`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L256)
- [`bistochastic_entropy_nondecreasing`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L191)
- [`binary_symmetric_entropy_strict`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L356)
- [`coarse_graining_entropy_decrease_counterexample`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L395)
- [`checked_kl_singular`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L440)
- [`verification_suite`](../../Verification/QuantumChannelClassicalDataProcessing.lean#L477)
