---
id: CryptoR1CSConstraintSystem
language: en
section: cryptography
source: Verification/CryptoR1CSConstraintSystem.lean
source_sha256: 17322d8ca0e12328e81a3eec6d781a18cdd6fa9e8bff656d013061668b149d68
novelty: not-assessed
status: reviewed
---

# CryptoR1CSConstraintSystem

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoR1CSConstraintSystem.lean)

## Verified result

Witness4 carries four real coordinates and a proof that one=1. Satisfaction of the canonical multiplication, addition and Boolean constraints is equivalent respectively to x*y=z, x+y=z and x=0 or x=1. Coefficientwise addition and scaling of linear combinations commute with evaluation at a fixed witness.

## Assumptions and limitations

These are exact single-constraint algebraic equivalences over the reals, not cryptographic soundness theorems. The Boolean and addition gates use the normalized constant coordinate. No collection of constraints, circuit synthesis, witness generation, proof protocol, zero-knowledge property or finite-field implementation is defined.

This component does not convert its constraint structures to QAP or interpolate them. The separate CryptoR1CSToQAP module already contains two-point real interpolation and QAP identities, but no bridge to this new interface is proved. Finite fields, arbitrary witness dimensions above four and compiler correctness are outside this model. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoR1CSConstraintSystem.crypto_r1cs_master_verification_suite`.
