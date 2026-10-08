---
id: CryptoPedersenHomomorphicSum
language: en
section: cryptography
source: Verification/CryptoPedersenHomomorphicSum.lean
source_sha256: 6a1928b37e34dd2fd93380c9e64c875a3ecc762a9c69bd1d3d803da6987bcaba
novelty: not-assessed
status: reviewed
---

# Pedersen homomorphic sums over a finite group

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoPedersenHomomorphicSum.lean)

## Model and hypotheses

For prime q, F = ZMod q is the scalar field. Setup contains an abstract finite
additive abelian group G with a Module F G instance, card G = q, and nonzero
points g,h. Nonzero points generate G: the scalar action F → G is proved
bijective using injectivity and equal cardinalities. Neither generator may be zero.
The commitment is C(m,r) = m • g + r • h. The prior real-scalar module is unchanged;
no equivalence between its continuous model and this finite distribution model is asserted.

setup_satisfiable constructs a concrete setup with G = F and g = h = 1.
This proves consistency of the hypotheses, not DLOG hardness: the relation is
explicitly known in this witness. Secure representations and generator selection
are outside the model. The abstract-group theorem does not reveal a supplied log.

## Checked contract

| Declaration | Exact result |
|---|---|
| commit_linear_combination | For any finite index set and field coefficients, sum cᵢ • C(mᵢ,rᵢ) = C(sum cᵢmᵢ,sum cᵢrᵢ). Repeated values at distinct indices are allowed. |
| commit_empty_combination | The empty sum is C(0,0) = 0. |
| commit_perfect_hiding | For every fixed message, the pushforward of the uniform PMF on F is exactly the uniform PMF on G. |
| commitment_point_probability | Every point has probability 1/q, independently of the message. |
| commit_aggregate_hiding | If k belongs to the index set and cₖ ≠ 0, a fresh independent uniform mask at k makes the aggregate uniform. |
| aggregate_zero_law | All-zero coefficients give the point mass at 0 for any mask distribution. This is message-independent but not uniform. |
| dlog_extraction_from_collision | Equal commitments with m ≠ m′ imply r ≠ r′ and h = ((m−m′)/(r′−r)) • g. |
| aggregate_binding_scalar_only | Apply that extraction only when the weighted message sums differ. |
| vector_not_determined | Distinct messages [1,0] and [0,1] have equal aggregates under weights [1,1] and zero masks. |
| known_relation_opening | If h = x • g is known, then C(m,r) = C(m′, r+(m−m′)/x). |

independentBlindings samples any joint law for the other coordinates and independently
refreshes coordinate k uniformly. The other coordinates may be correlated.
independent_blindings_joint_law proves the exact product factorization of that
coordinate and the remaining vector (with k zeroed). Coefficients and messages
are fixed, not selected adaptively from the random masks.
correlatedBlindings draws [t,−t] from uniform t: both marginals are uniform, but
with unit weights and zero messages the aggregate is identically zero.
Uniform marginals alone are therefore insufficient, including in characteristic two.

CryptoPedersenHomomorphicSumSuite quantifies over every valid setup; its master
proof establishes all VerifiedProperties and the explicit satisfiability witness.
Standalone results permit arbitrary universe levels and finite index sets.

## Clean Water

Hiding is an exact equality of discrete probability mass functions. Binding is an
algebraic collision-to-DLOG extraction, not unconditional injectivity in messages
and not a computational security theorem. Aggregation concerns the scalar linear
combination only and does not bind the entire vector component by component.
No PPT adversary model, security parameter, negligible advantage, commitment
security game, IND-CPA/EUF-CMA game, runtime bound, or DLOG hardness proof is claimed.
Multi-generator vector commitments, elliptic-curve implementation and setup
ceremonies are not modeled. Python, JSON/SHA-256 and SimLab linkage remain open
obligations. Scientific novelty is not assessed.

Reference: T. P. Pedersen, *Non-Interactive and Information-Theoretic Secure
Verifiable Secret Sharing*, CRYPTO 1991,
[paper](https://cgi.di.uoa.gr/~aggelos/crypto/page8/assets/Pedersen-VSS.PDF).
These proofs concern the explicitly stated algebra and distributions.
Commands and source hashes: [validation snapshot](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `d4a72dfb113fbdb5f4a4157db0f9f824ff5ffb48`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 122 |
| Lean files under Verification/ | 162 top-level + 2 support = 164 |
| Root-inclusive byte-identical export | 165 sources |
| Clean strict private build | 3613 jobs; no warnings |
| Both full axiom audits | 13704 declarations; no violations |
| Private live tests | 70; no failures or skips; 253.922s |
| Export live tests | 67; no failures or skips; 270.780s |
| Export clean strict build | 3613 jobs; no warnings |

Module verify and audit each covered 93 declarations.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3; executable
SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source records v4.32.0-rc1, with the
executable pinned separately. The registry hook passed separately; no second
independent proof kernel is claimed. Counts include generated declarations.
Project build directories started empty, with isolated pinned dependency caches.
Integration is idempotent. Earlier subject proofs are unchanged. Original workspace
HEAD and 406 tracked files outside simulations/ are preserved. This task makes no
writes to simulations/ and does not publish a public release.

## Public release validation

The separate [v0.5.20 report](../../docs/release-v0.5.20.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 122 |
| Lean files under Verification/ | 162 top-level + 2 auxiliary = 164 |
| Root-inclusive sources identical to the private snapshot | 165 |
| Clean strict build | 3613 jobs; no warnings |
| Complete verifier audit | 13704 declarations; no violations |
| Pinned independent full audit | 13704 declarations; no violations |
| Public live tests | 67; no failures or skips; 248.050s |
