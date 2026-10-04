---
id: NumericRoundingCertificates
language: en
section: numeric-certificates
source: Verification/NumericRoundingCertificates.lean
source_sha256: 5af92a35e634988e13c860e3c106ea47ccb776653f09d0e1aa599e5692f71292
novelty: not-assessed
status: reviewed
---

# NumericRoundingCertificates

[Lean](../../Verification/NumericRoundingCertificates.lean)[Grid](NumericBinaryGrid.md)

## Exact rounding semantics

`MagnitudeGrid` supplies strictly increasing rational magnitudes beginning at zero. The last code denotes a virtual overflow neighbor. `FloatRepresentation` stores a sign and a bounded magnitude code; `FloatValue` interprets zero and infinity as separate tags. They are not distinct elements or infinities inside the rational field.

`roundNearestEven` counts crossed boundaries between adjacent magnitudes. Each boundary is their exact rational midpoint. At equality it crosses precisely when the lower code is odd. `magnitudeCode_midpoint` derives the even-code result; `cell_nearest` establishes distance minimality among the finite grid magnitudes and the virtual endpoint. For arbitrary grids, parity is ordinal parity by definition. The supporting binary64 grid proves its correspondence with the decoded significand's low bit.

The sign comes from the exact rational argument. Exact zero is canonical `+0`, including a source negative zero after conversion to a rational. A strictly negative argument that underflows produces `−0`. This is a rational-input convention, not a model of all IEEE signed-zero arithmetic. NaNs and infinite input arguments are outside the input type.

For binary64, the quantum is `2^-1074`; the virtual terminal magnitude is `2^1024`. Its infinity result begins at `2^1024 − 2^970`, with equality selecting the even virtual code. Distance to infinity is never taken. The positive midpoint `2^-1075` rounds to `+0` while remaining a strictly positive rational number.

## Interval and midpoint witnesses

`interval_rounding_soundness` proves that equal endpoint encodings imply the same encoding throughout a closed interval. Its essential hypotheses are `L ≤ x ≤ U`; establishing those inequalities for a particular SQL expression is separate work. The proof derives monotonicity of boundary counts rather than assuming correctness of rounding.

`checkInterval` is the specification based on endpoint rounding. `checkIntervalCertificate` instead checks the claimed signed cell at each endpoint. `inMagnitudeCell` examines only the predecessor and successor boundaries; `magnitudeCode_of_cell` connects these local conditions to the global specification. Thus the executable witness path has a constant number of neighbor decodings, although exact integer/rational arithmetic cost depends on operand size. The count-based full binary64 specification is not an efficient enumerating implementation.

`checkExactMidpoint` checks a valid adjacent-code index and exact rational equality, expressed as a zero difference. It derives the even neighbor and the sign; `exact_midpoint_soundness` connects the verdict with `roundNearestEven`. Increased numerical precision or proximity to a midpoint is not evidence of equality.

`CertificateVerdict` distinguishes `decided` from `indeterminate`. Malformed mathematical claims or reversed bounds are conservatively inconclusive in this small core; richer Python statuses such as `invalid_input`, `invalid_witness`, and resource limits are not identified with this type. An inconclusive interval may coexist with a separate successful exact-midpoint witness without changing the original interval verdict.

## Static regressions and provenance

The module includes static binary64 regressions for canonical zero, signed underflow, the exact positive zero/subnormal midpoint, overflow, and the retained original 256-bit interval. The two source records `zero_midpoint_0` and `zero_midpoint_1` share the same bounds:

```text
L = (2^256 − 6) / 2^1331
U = (2^255 + 1) / 2^1330.
```

Their endpoint encodings are respectively `+0` and the least positive subnormal, so `historical_interval_indeterminate` preserves the inconclusive verdict. These are distinct from later `persistent_tie_zero` and `persistent_tie_unity` records at 2048 bits.

The [curated provenance file](../../data/numeric_rounding/regression_provenance.json) records exact fractions, original case IDs, file paths, selectors and SHA-256 values. It also contains seven midpoint fixtures and ordinary interval examples for regression work. Inclusion in this JSON alone is not a Lean proof; only the actual encoded theorem statements and compiled regression checks have that status.

## Scope and verification

`numeric_rounding_certificates_master_suite : NumericRoundingCertificatesSuite` collects interval soundness, local witness soundness, midpoint soundness, nearest-value selection and selected regressions. It does not certify every declaration merely by aggregation.

This module does not establish SQL enclosure construction, correctness or equivalence of Python code, JSON parsing, SHA-256 computation, source authentication, or correspondence between external JSON bytes and Lean constants. SHA-256 metadata identifies bytes but does not authenticate their author. The results do not establish a detector's physical behavior. Mathematical novelty is not assessed. Repository build and audit results are recorded separately in the [validation record](../VERIFICATION.en.md).

The semantic input of this module is rational. [NumericRealRounding](NumericRealRounding.md) now extends the semantics to real enclosed values, and [NumericSQLIntervalBounds](NumericSQLIntervalBounds.md) applies it to `sqrt(hbar/(m*omega))`. The distinct SimLab optimization gap still needs its own real enclosure construction and witness linkage.
