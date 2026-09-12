---
id: CryptoMerkleTree
language: en
section: cryptography
source: Verification/CryptoMerkleTree.lean
source_sha256: 5e4d846aa87640030fb295f2c574d3d4c9ad2ec7f9df34d5265b91292d0a5f53
novelty: not-assessed
status: reviewed
---

# CryptoMerkleTree

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoMerkleTree.lean)

## Verified result

For any binary function H on real values, each of the four canonical two-step paths reconstructs H(H(l0,l1),H(l2,l3)). A left sibling is combined as H(sibling,current), a right sibling as H(current,sibling). The universal statement is a conjunction of the four canonical checks. An explicit additional lemma states the definitional equivalence between verifyProof and equality of the computed root with the supplied root.

## Assumptions and limitations

H is an arbitrary total function, with no collision-resistance, second-preimage-resistance or injectivity assumption; even a constant H satisfies all completeness results. Accepted proofs therefore do not imply genuine membership under these assumptions. No cryptographic soundness, uniqueness of paths, or exclusion of forged leaves is proved.

Values are real scalars, not bytes or fixed-length digests. There is no leaf-hashing step, domain-separated encoding, 0x00/0x01 prefix scheme, or concrete hash implementation. The depth is fixed at two. Arbitrary-depth trees, sparse Merkle trees, serialization, update algorithms and adversarial security are outside the model. Domain-separation prefixes alone are not a proof of hash security. The function definitions are deterministic; no separate computational cost or executable real-number verifier is supplied.

## Value and novelty

A small reference for sibling orientation and completeness of four canonical paths, suitable for extending to inductive trees and explicit security assumptions. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `CryptoMerkleTree.crypto_merkle_tree_master_verification_suite`.
