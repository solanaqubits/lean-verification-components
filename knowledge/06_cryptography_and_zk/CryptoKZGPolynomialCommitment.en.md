---
id: CryptoKZGPolynomialCommitment
language: en
section: cryptography
source: Verification/CryptoKZGPolynomialCommitment.lean
source_sha256: a950a5720b8a0f5ebb0b37ca72efdb38f0530b3548cbbbb9ab72feeba91c1212
novelty: not-assessed
status: reviewed
---

# CryptoKZGPolynomialCommitment

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoKZGPolynomialCommitment.lean)

## Verified result

For degree-at-most-two real polynomials, (X-z)*Q(X)=P(X)-P(z) with Q(X)=a*X+(a*z+b). The scalar commitment P(tau)*g1 and witness Q(tau)*g1 satisfy verifyKZG for the honest value P(z). Commitments are additive under coefficientwise polynomial addition. No restriction X ≠ z or tau ≠ z is needed for these identities.

## Assumptions and limitations

KZGSetup contains nonzero real g1/g2 and an accessible real tau. pairing is ordinary multiplication. The setup is not a sequence of encoded powers, a trusted-setup ceremony or a hidden-information model. Completeness is not evaluation binding, hiding or a q-SDH reduction. With accessible tau and tau ≠ z, a scalar witness can be chosen algebraically for any proposed value; no cryptographic soundness follows.

The existing CryptoKZGCommitment component already contains quadratic and cubic scalar identities. This component supplies the requested Poly2/KZGSetup interface and explicit generator factors; it preserves the earlier suite. Arbitrary-degree polynomials are outside this new module, although the older component covers degree three. Finite fields, BLS12-381/BN254 groups, nontrivial pairings, q-SDH, batch openings and correspondence with deployed KZG implementations are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoKZGPolynomialCommitment.crypto_kzg_master_verification_suite`.
