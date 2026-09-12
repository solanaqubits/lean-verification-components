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
