---
id: CryptoSumcheckProtocol
language: en
section: cryptography
source: Verification/CryptoSumcheckProtocol.lean
source_sha256: 38954593d744bdf4f1873cae9d1b66aa89ca3e8affabd4b6a853874be0ac7355
novelty: not-assessed
status: reviewed
---

# CryptoSumcheckProtocol

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoSumcheckProtocol.lean)

## Verified result

For P(x1,x2)=a+b*x1+c*x2+d*x1*x2, the sum of round1Poly at zero and one equals the four-point hypercubeSum. Fixing any real r1, the two Boolean evaluations of round2Poly sum to round1Poly(r1). Its evaluation at r2 equals P(r1,r2). The first-round function has the explicit affine form (2*a+c)+(2*b+d)*x1.

## Assumptions and limitations

Round functions are defined directly from the honest polynomial. Challenges are arbitrary real parameters; they are not sampled randomly. The last evaluation and second-round reduction follow from definitions. There is no interactive transcript, malicious prover, verifier acceptance predicate, degree test on submitted polynomials or oracle-access model. These identities establish honest-round consistency, not soundness or zero knowledge.

Schwartz–Zippel, finite fields, soundness-error bounds, arbitrary variable counts above two, and correspondence to GKR/Spartan or deployed proof systems are not formalized. The affine identity is not a theorem about a Polynomial.natDegree representation. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `CryptoSumcheckProtocol.crypto_sumcheck_master_verification_suite`.
