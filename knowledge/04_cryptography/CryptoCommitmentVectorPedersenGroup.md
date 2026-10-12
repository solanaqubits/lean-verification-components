---
id: CryptoCommitmentVectorPedersenGroup
language: en
section: cryptography
source: Verification/CryptoCommitmentVectorPedersenGroup.lean
source_sha256: 7498ec257e38efd1a80d34444449a63e039a6c2b16e4f18cfbc216fb0530b832
novelty: not-assessed
status: reviewed
---

# Vector Pedersen commitments: perfect hiding and collision relations

The model uses a prime q, an additive commutative group A with a ZMod q module
structure, and a blinding generator H such that r ↦ r • H is bijective. An indexed
family G : Fin k → A supplies one nonzero generator for each message coordinate.
These are not a linearly independent basis: the group is cyclic. Repeated bases
are allowed and have explicit collision regressions.

The commitment is C(m,r) = ∑ i, m i • G i + r • H. It respects vector addition,
scalar multiplication and arbitrary finite weighted sums, with all scalar
arithmetic in ZMod q. The k=0 case is pure blinding. The k=1 bridge uses the actual
commit function from CryptoPedersenHomomorphicSum.

## Probability and assumptions

For each fixed m, r ↦ C(m,r) is bijective. Mapping a uniform PMF on ZMod q through
this function gives the uniform PMF on A. The proof reuses map_uniform_equiv.
Finiteness can be constructed from the blinding-generator bijection; a separate
finite enumeration does not add a cryptographic hypothesis. The output law is
identical for any two fixed message vectors. Blinding is sampled uniformly in
this statement; no claim is made for arbitrary message-dependent randomness.

Setup collects the generator conditions. ConsistencyModel uses A = ZMod q and
H = G i = 1 for every prime q and every k. This witnesses the algebraic assumptions,
not cryptographic hardness or an absolute consistency theorem.

## Collision semantics

Equality of two commitments is equivalent to
∑ i, (m i - m' i) • G i + (r-r') • H = 0.
If m ≠ m', at least one message coefficient is nonzero. This is extraction of a
nontrivial relation, not unconditional computation of a particular discrete log.

Fix j with d_j = m j - m' j ≠ 0. If the other bases are known as G i = α i • H for
i ≠ j, the collision proves
G j = -(d_j⁻¹ * (∑ i ≠ j, (m i - m' i) * α i + r-r')) • H.
The formula does not require α j as an input relation. Generator injectivity
ensures the extracted scalar represents the unique logarithm.

A known nonzero relation ∑ d i • G i + t • H = 0 constructs the alternate opening
(m+d,r+t), proves it differs from (m,r), and proves the commitments equal.
Equal bases additionally preserve the commitment under a swap of their coordinates.
A concrete regression uses different vectors with the same blinding.

## Regressions and Clean Water boundaries

Kernel regressions cover k=0, k=1 and k=2, finite weighted sums, zero and negative
weights, uniform PMF hiding, relation extraction, a conditional log extraction
example, repeated-base collisions and translated alternate openings.

Proved: linearity, distributional perfect hiding, exact collision relations,
nontrivial coefficients, conditional log extraction and the scalar Pedersen bridge.
Computational binding against polynomial-time adversaries, CRS or parameter
sampling, coordinate opening proofs, ZKP, Bulletproofs inner-product protocols,
concrete curves and serialization are not modeled. Merely assigning a base to
each coordinate does not establish computational binding.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

The vector commitment is the algebraic primitive used in
[Bulletproofs](https://eprint.iacr.org/2017/1066.pdf); that proof system is outside this module.
All project and export checks passed; measured results follow.

## Source theorem links

- [commit_vec_add_homomorphism](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L38)
- [commit_vec_smul_homomorphism](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L44)
- [commit_vec_weighted_sum_homomorphism](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L49)
- [commit_vec_hiding_equiv](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L60)
- [commit_vec_perfect_hiding](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L77)
- [message_independent_law](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L83)
- [commit_vec_collision_iff](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L89)
- [commit_vec_collision_linear_relation](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L99)
- [commit_vec_collision_nontrivial_coeff](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L105)
- [commit_vec_dlog_extraction_conditional](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L113)
- [commit_vec_permutation](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L134)
- [commit_vec_identical_generators_collision](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L141)
- [commit_vec_known_relation_alternate_open](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L155)
- [bridge_to_scalar_pedersen](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L168)
- [empty_vector](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L174)
- [group_properties](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L210)
- [crypto_vector_pedersen_master_suite](../../Verification/CryptoCommitmentVectorPedersenGroup.lean#L231)

## Private snapshot validation: Vector Pedersen commitments

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 148 |
| Lean sources including root | 191 |
| Strict clean private build | 3738 jobs; no warnings |
| Both full axiom audits | 18990 declarations; no violations |
| Private live tests | 96; no failures or skips; 291.065s |
| Export live tests | 93; no failures or skips; 311.101s |
| Strict clean export build | 3738 jobs; no warnings |

Module verify and audit each covered 1150 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were absent
before the final builds. Each tree uses its own copy of the pinned dependency cache.
All 191 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

Proved: vector linearity and finite weighted homomorphism, uniform-PMF perfect hiding,
exact collision relations, nontrivial coefficients, conditional logarithm extraction,
alternate openings, equal-base swap collisions and the scalar Pedersen bridge.
Indexed generators are not a linearly independent basis. Computational binding,
CRS or parameter generation, coordinate opening proofs, ZKP and Bulletproofs
protocols remain outside scope. Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.46 report](../../docs/release-v0.5.46.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 148 |
| Lean files under Verification/ | 188 top-level + 2 auxiliary = 190 |
| Root-inclusive sources identical to the private snapshot | 191 |
| Clean strict build | 3738 jobs; no warnings |
| Complete verifier audit | 18990 declarations; no violations |
| Pinned independent full audit | 18990 declarations; no violations |
| Public live tests | 93; no failures or skips; 290.036s |
