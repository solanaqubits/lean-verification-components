---
id: CryptoShamirSecretSharingGroup
language: en
section: cryptography
source: Verification/CryptoShamirSecretSharingGroup.lean
source_sha256: 5337a3b024ca85c15a9b6f4d75f9c4762cb4bbf133a40abb25389f534e6a197c
novelty: not-assessed
status: reviewed
---

# Finite-field Shamir sharing: threshold recovery and joint PMF secrecy

The scalar model uses a prime q and K = ZMod q, with 1 ≤ t ≤ n < q.
Setup supplies injective nonzero participant coordinates ξ : Fin n → K and a
cyclic additive group B with a K-module structure and a generator G for which
x ↦ x • G is bijective. ConsistencyModel chooses coordinates 1,...,n, B = K and
G = 1. This witnesses the assumptions; it is not a claim of cryptographic hardness.
The algebraic core is proved for arbitrary fields, with explicit finite-field
instantiations in GroupProperties and the master suite.

ShamirPoly K t s consists of polynomials p with p.natDegree < t and p.eval 0 = s.
The leading coefficient may be zero. Positive t includes the zero polynomial.
For I.card = t, the coefficient at participant i is
λ_i = ∏ j ∈ I.erase i, (-ξ j) * (ξ i - ξ j)⁻¹.
Distinct coordinates imply nonzero denominators. Mathlib's Lagrange interpolation
then proves ∑ i ∈ I, λ_i * p.eval (ξ i) = s.

## Probability model

observationLaw samples uniformly from the finite type ShamirPoly K t s and maps
the result to the whole vector of shares indexed by the coalition A. Finiteness
is proved by injection into the vector of the first t coefficients; nonemptiness
is witnessed by C s. This is a uniform law on all bounded-degree polynomials with
fixed constant coefficient, equivalently uniform independent free coefficients.
It does not restrict the leading coefficient to be nonzero.

For A.card < t, coalitionPoly is the product of normalized factors
(X - ξ i) / (-ξ i). It has degree A.card, value one at zero and value zero at
every coalition coordinate. The explicit equivalence
p ↦ p + (s' - s) • coalitionPoly has inverse with s and s' exchanged.
It preserves every observed share. Transport of the uniform PMF across this
bijection proves equality of the joint observation distributions for every pair
s,s'. No independence assumption about the secret's prior distribution is needed
to state equality of these conditional sampling laws. The result concerns a
fixed passive coalition, not adaptive corruption or active share substitution.

## Group lift and linearity

Group shares are p.eval (ξ i) • G. Weighted interpolation recovers s • G.
Generator injectivity supplies mathematical uniqueness of the scalar represented
by that point, without an algorithm for computing a discrete logarithm.
Finite weighted sums of valid polynomials stay below threshold t and have the
weighted sum of secrets as their constant term. Evaluation and group shares
respect the same linear combination, including zero and negative weights.
All finite-field arithmetic is modulo q; no unbounded integer-sum claim is made.

The real 2-of-n bridge uses the actual CryptoShamirSecretSharing definitions.
The common two-point field identity specializes independently to real numbers
and ZMod q; no homomorphism from the reals to a finite field is asserted.
The older theorem named shamir_single_share_perfect_secrecy establishes algebraic
compatibility with candidate secrets, as its comment states. This module adds
equality of probability distributions.

## Regressions and Clean Water

The kernel regression file tests a 3-of-4 setup over ZMod 7, recovery from
selected triples, a two-member coalition's joint PMF law, the shift equivalence,
thresholds 1, 2 and n, empty coalitions, relabelling, group recovery and weighted
sums. The coordinate-zero counterexample proves a single such share reveals s.

Proved: finite-field threshold reconstruction, joint PMF perfect secrecy below
threshold, group-point recovery, weighted homomorphism and the real-model bridge.
VSS/Feldman, malicious or forged shares, DKG, proactive refresh, threshold
signatures, discrete-log decoding, concrete curves and serialization are outside
the model. Python, JSON/SHA-256 and SimLab obligations remain open.
Novelty is not assessed.

Reference: [Shamir, How to Share a Secret (1979)](https://people.cs.pitt.edu/~litman/courses/cs2001/lectures/lecture-02-p612-shamir.pdf).
Source baseline: 3f3dc24abfe6d9b6a44069e88f3abd5f49aaa8ed. All checks passed; source hashes and measured results follow.

## Source theorem links

- [lagrange_denom_nonzero](../../Verification/CryptoShamirSecretSharingGroup.lean#L24)
- [field_lagrange_bridge](../../Verification/CryptoShamirSecretSharingGroup.lean#L28)
- [shamir_threshold_reconstruction](../../Verification/CryptoShamirSecretSharingGroup.lean#L37)
- [coalitionPoly_eval_zero](../../Verification/CryptoShamirSecretSharingGroup.lean#L47)
- [coalitionPoly_eval_member](../../Verification/CryptoShamirSecretSharingGroup.lean#L51)
- [coalitionPoly_degree](../../Verification/CryptoShamirSecretSharingGroup.lean#L56)
- [coalition_annihilator_poly](../../Verification/CryptoShamirSecretSharingGroup.lean#L62)
- [shift_preserves_observations](../../Verification/CryptoShamirSecretSharingGroup.lean#L93)
- [map_uniform_equiv](../../Verification/CryptoShamirSecretSharingGroup.lean#L123)
- [shamir_pmf_perfect_secrecy](../../Verification/CryptoShamirSecretSharingGroup.lean#L132)
- [weighted_share_eval](../../Verification/CryptoShamirSecretSharingGroup.lean#L144)
- [shamir_homomorphism_weighted_sum](../../Verification/CryptoShamirSecretSharingGroup.lean#L148)
- [shamir_group_reconstruction](../../Verification/CryptoShamirSecretSharingGroup.lean#L162)
- [weighted_group_shares](../../Verification/CryptoShamirSecretSharingGroup.lean#L169)
- [shamir_zero_coord_leakage](../../Verification/CryptoShamirSecretSharingGroup.lean#L175)
- [threshold_one](../../Verification/CryptoShamirSecretSharingGroup.lean#L179)
- [two_share_field](../../Verification/CryptoShamirSecretSharingGroup.lean#L187)
- [threshold_two_coefficients](../../Verification/CryptoShamirSecretSharingGroup.lean#L192)
- [threshold_all](../../Verification/CryptoShamirSecretSharingGroup.lean#L200)
- [reconstruction_permutation](../../Verification/CryptoShamirSecretSharingGroup.lean#L206)
- [bridge_to_scalar_shamir](../../Verification/CryptoShamirSecretSharingGroup.lean#L218)
- [group_properties](../../Verification/CryptoShamirSecretSharingGroup.lean#L273)
- [crypto_shamir_group_master_suite](../../Verification/CryptoShamirSecretSharingGroup.lean#L295)

## Private snapshot validation: finite-field Shamir sharing

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 149 |
| Lean sources including root | 192 |
| Strict clean private build | 3740 jobs; no warnings |
| Both full axiom audits | 19077 declarations; no violations |
| Private live tests | 97; no failures or skips; 304.332s |
| Export live tests | 94; no failures or skips; 310.551s |
| Strict clean export build | 3740 jobs; no warnings |

Module verify and audit each covered 1138 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were absent
before the final builds. Each tree uses its own copy of the pinned dependency cache.
All 192 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

Proved: threshold interpolation, joint uniform-PMF secrecy for fixed coalitions below
threshold, explicit secret-shift equivalence, group-point reconstruction and weighted
linearity. VSS, active share forgery, DKG, proactive refresh, adaptive corruptions,
threshold signatures, DLOG decoding, curves and serialization remain outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.47 report](../../docs/release-v0.5.47.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 149 |
| Lean files under Verification/ | 189 top-level + 2 auxiliary = 191 |
| Root-inclusive sources identical to the private snapshot | 192 |
| Clean strict build | 3740 jobs; no warnings |
| Complete verifier audit | 19077 declarations; no violations |
| Pinned independent full audit | 19077 declarations; no violations |
| Public live tests | 94; no failures or skips; 297.242s |
