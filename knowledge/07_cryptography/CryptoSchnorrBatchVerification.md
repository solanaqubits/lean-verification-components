---
id: CryptoSchnorrBatchVerification
language: en
section: cryptography
source: Verification/CryptoSchnorrBatchVerification.lean
source_sha256: e034ca9a562a8563e805b3963aeb5c00039bf91db54560d56e75a8808d10e9f8
novelty: not-assessed
status: reviewed
---

# CryptoSchnorrBatchVerification

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoSchnorrBatchVerification.lean)

## Model and results

The counting model uses the finite prime field `ZMod q`, with
`[Fact (Nat.Prime q)]`. A discrepancy vector `d : Fin n → ZMod q` is fixed
before the coefficient vector is chosen. The full coefficient space is
`Fin n → ZMod q`: every coordinate may be zero, and the all-zero vector is
included. The batch predicate is `batchCheck z d ↔ (∑ i, z i * d i) = 0`.

The module proves exact finite cardinalities and rational counting ratios.
These ratios can be interpreted as probabilities under uniform choice from
the stated finite spaces. It does not define a probability measure, random
variables, or a sampling procedure.

- [`batch_verification_completeness`](../../Verification/CryptoSchnorrBatchVerification.lean#L42):
  if every discrepancy is zero, every coefficient vector accepts. This
  algebraic statement holds for arbitrary natural `q` and includes `n = 0`.
- [`batch_verification_counting_soundness`](../../Verification/CryptoSchnorrBatchVerification.lean#L76):
  if `hd : ∃ j, d j ≠ 0`, exactly `q ^ (n - 1)` coefficient vectors accept,
  out of `q ^ n` vectors. The witness `j : Fin n` implies `n > 0`, so the
  natural-number subtraction in `n - 1` has the intended meaning.
- [`batch_verification_false_positive_prob`](../../Verification/CryptoSchnorrBatchVerification.lean#L107):
  `falsePositiveFraction d = 1 / (q : ℚ)` under the same nonzero-discrepancy
  hypothesis. This is an equality of exact rational ratios, not only an
  upper bound or an empirical estimate.

The proof constructs the additive map `batchHom d : (Fin n → ZMod q) →+ ZMod q`.
A nonzero coordinate `d j` makes this map surjective: placing `a / d j` in
coordinate `j` and zero elsewhere attains any `a`. Its kernel is exactly the
accepting set; the kernel/index cardinality identity gives the count.

## Repeated checks

`roundsCheck z d` requires every row of
`z : Fin k → Fin n → ZMod q` to accept the same fixed `d`.
The coefficient space is the full Cartesian product. Uniform choice from
that space is the interpretation corresponding to `k` independent uniform
rounds; reusing one sampled vector in every round is a different experiment.

- [`rounds_accepting_card`](../../Verification/CryptoSchnorrBatchVerification.lean#L133)
  and `rounds_fraction_power` factor the accepting count and ratio into
  their single-round values raised to `k`.
- [`batch_verification_k_rounds_count`](../../Verification/CryptoSchnorrBatchVerification.lean#L153)
  gives exactly `q ^ (k * (n - 1))` accepting arrays among `q ^ (k * n)`
  arrays when `hd : ∃ j, d j ≠ 0`.
- [`batch_verification_k_rounds_bound`](../../Verification/CryptoSchnorrBatchVerification.lean#L161)
  proves the equality `roundsFalsePositiveFraction d k = (1 / (q : ℚ)) ^ k`.
  For `k = 0`, there is one empty array, every required check holds vacuously,
  and the ratio is `1`. Zero rounds therefore provide no rejection guarantee.

`SchnorrBatchVerificationFormalSuite` collects completeness, the two counts,
and the two fractions. Its proved instance is
`schnorr_batch_verification_master_suite`.

## Scalar Schnorr connection and limits

[`discrepancy`](../../Verification/CryptoSchnorrBatchVerification.lean#L29)
is the scalar residual `s * G - R - c * pk`.
`discrepancy_zero_iff` relates its vanishing to `s * G = R + c * pk`.
[`batch_discrepancy_iff`](../../Verification/CryptoSchnorrBatchVerification.lean#L47)
connects the residual predicate to the weighted scalar equation
`(∑ i, z i * s i) * G = (∑ i, z i * R i) + ∑ i, z i * c i * pk i`.
These bridge identities need no primality assumption or condition `G ≠ 0`.
All quantities are field/ring scalars; no elliptic-curve group representation
or equivalence to a concrete signature verifier is proved.

The exact ratio concerns a fixed invalid residual vector. It does not prove
a bound for an adversary that chooses or changes `d` after seeing the
coefficients. The module does not model an adversarial game, random-oracle
security, EUF-CMA security, discrete-logarithm hardness, or a CSPRNG.

This is not the BIP340 coefficient algorithm: fixing the first coefficient,
selecting nonzero coefficients, and deriving coefficients are outside the
model. The `1/q` formula cannot be transferred to a different coefficient
space without a separate argument. Message hashing, point validation,
secp256k1 arithmetic, serialization, and implementation correctness are also
outside the model. Novelty is not assessed.

## Verification

The module passed `verify`, `audit`, and integration as `CryptoFullSuite.schnorr_batch`. Strict build, `verify-all`, independent axiom audit, the public regression tests without skips, and catalog checks passed. A compiler regression checks small-field counts by exhaustive evaluation, cancellation, the zero vector, and k = 0. See the [validation record](../VERIFICATION.en.md).
