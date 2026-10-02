---
id: CryptoBLSSignatureAggregation
language: en
section: cryptography
source: Verification/CryptoBLSSignatureAggregation.lean
source_sha256: 168b5e901376319516ed10cae8e98e2bb8d88564f085e98217d2577c5c2cbb71
novelty: not-assessed
status: reviewed
---

# CryptoBLSSignatureAggregation

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBLSSignatureAggregation.lean)

## Verified result

The original scalar interface and its completeness/bilinearity theorems are retained. TwoGenerator adds nonzero real scales g1 and g2, publicKey = sk*g2 and sign = sk*h*g1. Honest signatures satisfy the single verification equation. The sum of two honest signatures on one scalar message value verifies against the sum of public keys. For any two scalar values h1,h2, the pairing of the aggregate signature equals the sum of the individual pairings. The values need not differ. Signing is additive in the supplied scalar h and homogeneous in sk.

New entry points: bls_single_correctness, bls_multisig_same_message_correctness, bls_aggregate_distinct_messages_correctness, bls_sig_additive_messages and bls_sig_homomorphic_scale. The extended registry is crypto_bls_signature_master_suite.

## Assumptions and limitations

Pairing means real multiplication. Setup nonzero assumptions are stored but unnecessary for these polynomial identities. In the scalar model the public ratio pk/g2 directly exposes sk, so no unforgeability is established. The h parameters are supplied scalars; additivity in h is not additivity of raw messages or a hash-to-curve function. Aggregation covers two honestly formed signatures, not arbitrary participant sets or adversarial inputs. There is no operation-count or performance model.

Finite groups, nontrivial elliptic-curve pairings, subgroup checks, EUF-CMA, hash-to-curve SSWU/MapToGroup, rogue-key resistance and Proof of Possession/KOSK are not formalized. No correspondence with a deployed consensus implementation is proved.

The old BLSSetup, sign, publicKey and verifySingle keep their signatures. The incompatible new definitions live in TwoGenerator. CryptoBLSSignatureFormalSuite gains h_two_generator; manual constructors must provide it. CryptoFullSuite.bls_signature_aggregation accesses the existing bls_signature field without adding an import or duplicate component. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoBLSSignatureAggregation.crypto_bls_signature_master_suite`.
