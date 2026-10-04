---
id: NumericSQLGapBounds
language: en
section: numeric-certificates
source: Verification/NumericSQLGapBounds.lean
source_sha256: 6b04b810667cc631f1774b8df002005e1731426722203a9a5c1c188f77861f3d
novelty: not-assessed
status: reviewed
---

# NumericSQLGapBounds

[Section](README.md) · [Lean](../../Verification/NumericSQLGapBounds.lean)

## Target and assumptions

`sqlNoiseGap A B I = A/I + B*I - 2*sqrt(A*B)` is a prescribed scalar optimization gap over real numbers. It differs from the conditional root `sqrt(hbar/(mass*frequency))` in NumericSQLIntervalBounds. Parameters are strictly positive for the nonnegativity and exact-zero theorems.

`sql_gap_affine_enclosure` reverses root endpoints under multiplication by -2: a supplied enclosure `L ≤ sqrt(A*B) ≤ U` gives `[A/I+B*I-2*U, A/I+B*I-2*L]`. This affine statement itself needs no positivity assumption. The result is a closed, nonstrict enclosure, not strict inequalities at its endpoints.

`sql_gap_nonneg` reuses the existing scalar variance bound. `sql_gap_zero_iff` proves `G=0 ↔ A=B*I²` for positive real parameters through the previously proved unique optimum. `sql_gap_exact_zero_rounding` derives the existing binary64 positive-zero encoding. Exact Zero → Canonical +0 is not a midpoint or a tie. A positive gap that underflows to zero is not asserted to be exactly zero; the rounding conclusion has no such converse.

## Executable certificates and real semantics

`sql_gap_real_bounds_rounding` uses real endpoints with matching rounded encodings. `sql_gap_rounding_soundness` accepts the existing rational interval checker verdict and a proved enclosure of the real gap. Both use `NumericRealRounding.realRound`; no second rounding implementation or midpoint-distance condition is introduced.

For exact rational A,B,I, `productInterval` forms the point interval A*B and `gapInterval` computes exact rational affine endpoints. `sql_gap_checked_enclosure` derives root containment from `checkSqrtWitness`, then derives containment of G. `sql_gap_affine_rounding_soundness` composes that inclusion with `checkIntervalCertificate`. The conclusion is about the actual real expression, which may be irrational. This checked affine composition also holds without positivity of the parameters; the physical domain and exact-zero criterion remain strictly positive.

`NumericSQLGapBoundsSuite` collects affine containment, nonnegativity, zero equivalence, positive zero and the complete rational-witness-to-real-gap rounding theorem. `numeric_sql_gap_master_suite` assembles the existing proofs. The module is registered through an explicit idempotent integration recipe.

## Regressions and boundaries

The compiler regression checks the irrational gap `3-2*sqrt(2)`, an ordinary positive gap, a strictly positive gap exactly at the binary64 underflow midpoint, invalid square-root witnesses, rejection of negative zero for exact zero, and the necessity of positivity for the balance criterion. A deliberately broad rational root interval for decimal A=B=1/10, I=1 remains indeterminate while a separate theorem establishes exact zero. The existing historical interval theorem is retained unchanged. These are static exact mathematical examples, not a claim of importing or authenticating a SimLab package.

No rationalized enclosure, exact comparison with quantization-cell boundaries, SimLab cell-search algorithm or adaptive-refinement termination theorem is added. Historical indeterminate results, the separate exact_zero records and frozen simulation certificates are not rewritten. Python execution, JSON/RFC 8259, SHA-256, authenticated provenance and the binding of A,B,I to external bytes are not proved. The earlier conditional digest bridge retains those limitations. No detector characteristics, physical calibration or noise correlations are established. Mathematical novelty is not assessed.

Build and audit evidence is recorded in the [validation record](../VERIFICATION.en.md).
