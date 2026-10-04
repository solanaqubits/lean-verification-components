---
id: NumericSQLIntervalBounds
language: en
section: numeric-certificates
source: Verification/NumericSQLIntervalBounds.lean
source_sha256: 89f4d8f1ef0533636c6683f45f208b81d507acb516d3733429ac294132661fe7
novelty: not-assessed
status: reviewed
---

# NumericSQLIntervalBounds

[Section](README.md) · [Lean](../../Verification/NumericSQLIntervalBounds.lean)

## Prescribed target and input hypotheses

The target is the real number

```text
sqlTarget(hbar, m, omega) = sqrt(hbar / (m * omega)).
```

It is **not** the SimLab optimization gap `A/I + B*I − 2*sqrt(A*B)`. This module does not claim to verify the existing gap-witness pipeline or its certificates. The SQL name identifies the prescribed scalar target; no physical calibration or universal quantum measurement limit is derived here.

`RatInterval` stores rational endpoints with their order proof. `containsReal` means that a real value lies between the embedded rational endpoints. For input intervals `H`, `M`, and `W`, the lower endpoints must be strictly positive, and localization of `hbar`, mass, and frequency in these intervals is an explicit hypothesis.

## Rational propagation and root witnesses

`mulInterval` multiplies corresponding endpoints for nonnegative intervals; `rat_mul_interval_sound` proves enclosure of the real product. `divInterval` uses opposite denominator endpoints, requiring a nonnegative numerator interval and a denominator bounded strictly away from zero. `rat_div_interval_sound` proves enclosure of the real quotient.

Consequently, `radicandInterval` has the explicit endpoints

```text
H.lo / (M.hi * W.hi),   H.hi / (M.lo * W.lo).
```

`sql_radicand_enclosure` proves that these bound `hbar/(m*omega)` under the input hypotheses.

A supplied root interval `R` is checked through the fully rational predicate `SqrtWitness I R`:

```text
0 ≤ R.lo,  0 ≤ R.hi,
R.lo^2 ≤ I.lo,  I.hi ≤ R.hi^2.
```

The certificate format requires both proposed root endpoints nonnegative. Squaring alone cannot justify a negative upper bound; nonnegativity of a lower bound is a conservative format restriction. For an ordered interval the upper sign also follows from a nonnegative lower endpoint. `checkSqrtWitness` computes this predicate. `rat_sqrt_interval_sound`, `sqrt_witness_sound`, and `check_sqrt_witness_sound` derive the enclosure of `Real.sqrt` from those inequalities. `sql_interval_enclosure` composes the radicand and root steps.

`coarseRootInterval` constructs `[0, I.hi+1]` for an interval with nonnegative lower bound; `coarse_root_witness` verifies it. This gives an explicit computable enclosure, not a guarantee of useful precision or successful rounding. `sqrt_witness_restrict` shows that narrowing the radicand interval preserves an already accepted root witness. It does not implement an adaptive refinement algorithm or prove convergence to a desired bit count.

`sql_coarse_enclosure` packages the explicit coarse witness with its real enclosure theorem. `numeric_sql_interval_master_suite : NumericSQLIntervalBoundsSuite` collects the root, witness, enclosure and rounding results.

## Rounding bridge and limits

`sql_rounding_soundness` combines the proved enclosure with the existing rational interval-certificate checker and [NumericRealRounding](NumericRealRounding.md). If the rational root interval is accepted for encoding `f`, the actual real `sqlTarget` rounds to `f`. The real target may be irrational; the conclusion is not obtained by silently treating it as a rational input.

This result remains conditional on the supplied positive input intervals containing the actual parameters and on the two accepted mathematical witnesses. Wide enclosures may fail to establish a unique rounded result. Nonnegative root witnesses and strict denominator bounds cannot be dropped.

No theorem verifies Python, JSON parsing, hashing, the origin of input intervals, or correspondence with external witness bytes. The existing SimLab gap and its root-generation/refinement implementation remain separate obligations. Detector physics, noise correlations, calibration and physical SQL applicability are not established. Mathematical novelty is not assessed. Final build and audit results are recorded in the [validation record](../VERIFICATION.en.md).
