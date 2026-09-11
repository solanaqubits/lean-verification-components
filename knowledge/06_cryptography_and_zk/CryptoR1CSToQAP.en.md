---
id: CryptoR1CSToQAP
language: en
section: cryptography
source: Verification/CryptoR1CSToQAP.lean
source_sha256: 0f7a933cba940db698a9bfdd824ab41c15fee8ca5d46f439ebb49b7f28aafab3
novelty: not-assessed
status: reviewed
---

# CryptoR1CSToQAP

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoR1CSToQAP.lean)

## Verified result

For two distinct real nodes, the Lagrange basis has the prescribed Kronecker values. Interpolation recovers both supplied values, and Z vanishes at both nodes. Two satisfied scalar constraints imply A(x)B(x) - C(x) = H Z(x) for every real x, with the explicit constant H. Conversely, the identity for every x recovers both constraints by evaluation at the nodes.

## Assumptions and scope

The domain requires r1 ≠ r2. All row values are arbitrary real scalars; completeness assumes a1*b1 = c1 and a2*b2 = c2. The functions represent evaluations of linear and quadratic expressions, not values of Mathlib's Polynomial type. Thus the checked result is a pointwise factorization, not a separately encoded Polynomial divisibility theorem.

No general N-row R1CS matrices, shared witness vector, finite field, witness-generation algorithm, SNARK setup, prover, verifier or computational security are modeled. The soundness theorem concerns the algebraic reduction, not Groth16 or Pinocchio security. Degenerate row values are permitted; H may be zero.

## Value and novelty

A reusable, explicit two-row algebraic component illustrating the interpolation-to-factorization step. Mathematical novelty and first-formalization claims have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `CryptoR1CSToQAP.crypto_r1cs_to_qap_master_verification_suite`.

- [`r1cs_to_qap_completeness`](../../Verification/CryptoR1CSToQAP.lean#L54)
- [`r1cs_to_qap_soundness`](../../Verification/CryptoR1CSToQAP.lean#L70)
