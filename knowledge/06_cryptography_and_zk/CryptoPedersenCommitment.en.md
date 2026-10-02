---
id: CryptoPedersenCommitment
language: en
section: cryptography
source: Verification/CryptoPedersenCommitment.lean
source_sha256: 5ea97b426007c289f99b689b1a50439caffee161142a1b03cc356366b6809bff
novelty: not-assessed
status: reviewed
---

# CryptoPedersenCommitment

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoPedersenCommitment.lean)

## Verified result

The original real-scalar commitment API C(m,r)=mG+rH and its earlier theorems are preserved. DLogRelation supplies a nonzero x with H=xG. The new opening formula r'=r+(m-m')/x gives the same commitment for any target message m'; pedersen_hiding_unique additionally proves existence and uniqueness of its blinding scalar.

A collision between distinct messages forces r2-r1≠0 and yields H=((m1-m2)/(r2-r1))*G. The module retains the earlier converse-ratio identity for G/H. It also proves zero commitment, additive and scalar identities, and additivity of the two-message scalar commitment m1*G1+m2*G2+rH.

New entry points: pedersen_perfect_hiding, pedersen_hiding_unique, pedersen_collision_implies_blinding_diff, pedersen_binding_extracts_dlog, vector_pedersen_homomorphic_add and crypto_pedersen_commitment_master_suite.

## Assumptions and limitations

Nonzero real parameters do not establish independent cryptographic generators. DLogRelation is supplied data and H/G is directly available over the reals. Existence and uniqueness of an alternative opening are algebraic facts, not equality of randomized commitment distributions. No randomness or adversary is modeled; neither information-theoretic perfect hiding nor computational binding is proved.

The vector extension contains exactly two message scalars and one blinding scalar; only its additive identity is shown. Arbitrary-dimensional commitments, finite prime-order groups and discrete-log hardness, secp256k1/Ristretto255/Ed25519, NUMS generator derivation and Schnorr opening proofs are not formalized. Scientific novelty has not been assessed.

PedersenGenerators, PedersenSetup with its coercion, commit, and the old theorem signatures and equality directions remain available. Reverse-direction wrapper theorems commit_add_eq_addCommit and commit_smul_eq_smulCommit fill the new suite. CryptoPedersenFormalSuite gains h_extended, which manual constructors must supply. The existing CryptoFullSuite.pedersen_commitment accessor is preserved; its h_extended field exposes the new results without an additional import.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoPedersenCommitment.crypto_pedersen_commitment_master_suite`.
