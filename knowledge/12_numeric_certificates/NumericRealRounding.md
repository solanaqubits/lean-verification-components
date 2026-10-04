---
id: NumericRealRounding
language: en
section: numeric-certificates
source: Verification/NumericRealRounding.lean
source_sha256: 13e59b66be0e03567abf2301c6a911e05b25e87348c6183e79040bb0a8f45e2b
novelty: not-assessed
status: reviewed
---

# NumericRealRounding

[Section](README.md) · [Lean](../../Verification/NumericRealRounding.lean)

## Real inputs on the existing rational grid

This helper extends the semantic rounding domain from rational numbers to real numbers. It retains `MagnitudeGrid` and `FloatRepresentation` from [NumericRoundingCertificates](NumericRoundingCertificates.md), including the separate sign bit and tagged interpretations of zero and infinity.

`realCrossed` compares a real argument with a rational boundary cast to `ℝ`, using the same lower-code parity rule at an exact tie. `realMagnitudeCode` counts crossed boundaries. `realMagnitudeCode_monotone` is proved by inclusion of the corresponding finite sets; monotonicity is not assumed as an input condition.

`realRound` applies this count to the absolute value and derives the sign from `x < 0`. Arbitrary real comparisons make this a **noncomputable specification**, not an executable real-number rounding algorithm. The efficient certificate checker remains the existing rational local-cell checker.

`realCrossed_ratCast`, `realMagnitudeCode_ratCast`, and `realRound_ratCast` prove agreement with the rational specification on embedded rational inputs. This includes exact zero mapping to `+0`, signed underflow to `−0` for negative nonzero inputs, ties-to-even and the virtual-overflow encoding. A rational virtual endpoint is never treated as a real infinity. NaN and infinite input arguments remain outside the input type.

## Soundness across rational enclosures

`real_interval_rounding_soundness` proves convexity of rounding fibers for arbitrary real endpoints: when both endpoint encodings equal `f`, every enclosed real value also rounds to `f`. The proof treats positive and negative inputs separately, preserving the distinction between signed-zero encodings.

`rational_bounds_real_rounding_soundness` specializes this to rational endpoints using the cast-agreement theorem. The main interface is:

```text
interval_certificate_real_sound:
  checkIntervalCertificate g L U f = decided f
  → (L : ℝ) ≤ x → x ≤ (U : ℝ)
  → realRound g x = f.
```

The target `x` may be irrational. This removes the rational-input restriction at the semantic conclusion while retaining exact rational witness verification. The enclosure hypotheses are explicit; the helper does not establish them for any specific expression.

## Scope

The supporting [NumericSQLIntervalBounds](NumericSQLIntervalBounds.md) module constructs conditional enclosures for a prescribed square-root target. Neither module proves equivalence to Python, a JSON parser, SHA-256, external input bytes, or machine execution. Physical detector behavior and calibration remain external. Mathematical novelty is not assessed. Final build and audit results are recorded separately in the [validation record](../VERIFICATION.en.md).
