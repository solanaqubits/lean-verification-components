# Cryptographic algebra and ZK components

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [CryptoSPNInvariants](CryptoSPNInvariants.en.md) | Invertibility of rational diffusion, a weight-sum lower bound of five, and round bijectivity under invertible substitution. |
| [CryptoZKAir](CryptoZKAir.en.md) | Generation and checking of finite deterministic traces, checker correctness, and trace uniqueness. |
| [CryptoZKFRILowDegree](CryptoZKFRILowDegree.en.md) | Length of pairwise coefficient folding, arithmetic of d/2^k, and a folding identity for cubic polynomials. |
| [CryptoKZGCommitment](CryptoKZGCommitment.en.md) | Division identities for P(x)−P(z) in degrees 2 and 3, linearity of evaluation, and cancellation in a scalar verification equation. |
| [CryptoPedersenCommitment](../06_cryptography_and_zk/CryptoPedersenCommitment.en.md) | For C(m,r)=mG+rH over real scalars, additivity, scalar linearity, an explicit change of opening, and a ratio identity extracted from a collision. H ≠ 0 is required; the collision result also assumes distinct messages. |

## Scope

These components do not prove end-to-end cryptographic security. Finite cryptographic groups, adversaries, probability distributions, and hardness reductions require separate models.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)

- [CryptoR1CSToQAP](../06_cryptography_and_zk/CryptoR1CSToQAP.en.md): two-node interpolation and scalar constraint factorization.

- [CryptoFiatShamirTransform](../06_cryptography_and_zk/CryptoFiatShamirTransform.en.md): scalar Schnorr completeness and conditional witness extraction.

- [CryptoShamirSecretSharing](../06_cryptography_and_zk/CryptoShamirSecretSharing.en.md)

- [CryptoMerkleTree](../06_cryptography_and_zk/CryptoMerkleTree.en.md)

- [CryptoBLSSignatureAggregation](../06_cryptography_and_zk/CryptoBLSSignatureAggregation.en.md)

- [CryptoSchnorrSignature](../06_cryptography_and_zk/CryptoSchnorrSignature.en.md)

- [CryptoElGamalEncryption](../06_cryptography_and_zk/CryptoElGamalEncryption.en.md)

- [CryptoKZGPolynomialCommitment](../06_cryptography_and_zk/CryptoKZGPolynomialCommitment.en.md)

- [CryptoSumcheckProtocol](../06_cryptography_and_zk/CryptoSumcheckProtocol.en.md)

- [CryptoR1CSConstraintSystem](../06_cryptography_and_zk/CryptoR1CSConstraintSystem.en.md)

- [CryptoGroth16SNARK](../06_cryptography_and_zk/CryptoGroth16SNARK.en.md)

- [CryptoFeldmanVSS](../07_cryptography/CryptoFeldmanVSS.md): scalar share consistency and reconstruction against fixed coefficient commitments.

- [CryptoMuSig2Aggregation](../07_cryptography/CryptoMuSig2Aggregation.md): two-signer, two-nonce scalar completeness and a restricted naive-key cancellation barrier; no MuSig2 security claim.

- [CryptoSchnorrBatchVerification](../07_cryptography/CryptoSchnorrBatchVerification.md): exact prime-field batch acceptance counts and independent-round fractions for fixed residuals.

- [CryptoTranscriptForkingLemma](../07_cryptography/CryptoTranscriptForkingLemma.md): Finite uniform matrix forking bound and scalar witness extraction; no adaptive random-oracle reduction.

- [CryptoPedersenHomomorphicSum](../04_cryptography_and_protocols/CryptoPedersenHomomorphicSum.md) — Finite-group homomorphism, exact hiding distributions and collision extraction.

- [CryptoSchnorrIdentification](../04_cryptography_and_protocols/CryptoSchnorrIdentification.md) — Finite-group identification, algebraic extraction and exact HVZK transcript distributions.

- [CryptoSchnorrMultiSignaturesMuSigGroup](../04_cryptography/CryptoSchnorrMultiSignaturesMuSigGroup.md) — Finite-group Schnorr aggregation completeness and naive rogue-key witness.

- [CryptoBLSSignatureAggregationGroup](../04_cryptography/CryptoBLSSignatureAggregationGroup.md) — Bilinear BLS aggregation, rogue-key and error-cancellation counterexamples.

- [CryptoElGamalHomomorphismGroup](../04_cryptography/CryptoElGamalHomomorphismGroup.md) — Group ElGamal correctness, weighted homomorphism, rerandomization and malleability.

- [CryptoCommitmentVectorPedersenGroup](../04_cryptography/CryptoCommitmentVectorPedersenGroup.md) — Vector Pedersen commitments, uniform-PMF hiding and collision relations.

- [CryptoShamirSecretSharingGroup](../04_cryptography/CryptoShamirSecretSharingGroup.md) — Shamir threshold sharing, joint PMF secrecy and group recovery.

- [CryptoThresholdSchnorrFrostGroup](../04_cryptography/CryptoThresholdSchnorrFrostGroup.md) — FROST threshold completeness, canonical sessions and error cancellation.

- [CryptoPedersenRangeProofLinear](../04_cryptography/CryptoPedersenRangeProofLinear.md): interactive range proofs, two-transcript extraction and full joint special HVZK.

- [CryptoBulletproofsInnerProduct](../04_cryptography/CryptoBulletproofsInnerProduct.md) — Recursive IPA completeness, expanded verification and exact payload counts.

- [Bulletproofs algebraic range reduction](../04_cryptography/CryptoBulletproofsRangeReduction.md)
