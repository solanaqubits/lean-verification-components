---
id: CryptoGroth16SNARK
language: en
section: cryptography
source: Verification/CryptoGroth16SNARK.lean
source_sha256: 01b3257e826f3adbc06d82ed77d1ed574c131cc37a1cfa4bee8917df13b58c01
novelty: not-assessed
status: reviewed
---

# CryptoGroth16SNARK

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoGroth16SNARK.lean)

## Verified result

For nonzero delta, solving C=(a*b-alpha*beta-xPub*gamma)/delta gives a triple accepted by the scalar verification equation. simulateProof uses the same construction and is accepted for every real public input and arbitrary a,b. Two accepted triples sharing a,b satisfy c1-c2=(x2-x1)*gamma/delta. This is an affine difference relation, not aggregation of proofs or additive homomorphism of the entire verification equation.

## Assumptions and limitations

Setup scalars are accessible and pairing is ordinary real multiplication. No source groups, generators, encoded CRS, circuit, QAP or witness relation is defined. Acceptance for arbitrary inputs is possible by construction and does not establish completeness or knowledge soundness of an actual SNARK. The simulation theorem proves acceptance only: no probability distributions, randomness, indistinguishability or zero-knowledge game is modeled. Nonzero gamma is retained in the setup although these proofs only need nonzero delta.

BN254/BLS12-381 asymmetric pairings, algebraic-group-model extraction, prover randomizers r,s, trusted-setup security and correspondence to a Groth16 implementation are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoGroth16SNARK.crypto_groth16_master_verification_suite`.
