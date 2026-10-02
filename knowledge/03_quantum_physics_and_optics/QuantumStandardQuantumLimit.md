---
id: QuantumStandardQuantumLimit
language: en
section: quantum-physics
source: Verification/QuantumStandardQuantumLimit.lean
source_sha256: 408f63ff00145bc26d53a998b38c623f85feb98e2584afcc940d28ac8a688aac
novelty: not-assessed
status: reviewed
---

# QuantumStandardQuantumLimit

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumStandardQuantumLimit.lean)

## Scalar model and exact minimum

In namespace `QuantumStandardQuantumLimit`, the prescribed real-valued expression is

\[
V(I)=\operatorname{noiseVariance}(A,B,I)=\frac{A}{I}+BI,
\qquad A>0,\quad B>0,\quad I>0.
\]

The names suggest measurement imprecision and back-action contributions as a
function of intensity. The definition itself is scalar algebra: it introduces no
random variables, stochastic processes, probability measure, variance operator,
or covariance. Omitting a correlation term is an external modeling choice
implicit in the formula, not a proved independence or zero-covariance fact.

The exact identity

\[
V(I)-2\sqrt{AB}=\frac{(\sqrt A-I\sqrt B)^2}{I}
\]

proves the nonstrict bound \(V(I)\ge 2\sqrt{AB}\). The unique positive optimizer
is \(I_*=\sqrt{A/B}\), where the two contributions balance:
\(A/I_*=BI_*\). The bound is attained at \(I_*\) and is strict for every other
positive intensity. Positivity assumptions are essential to this stated domain;
the definition also accepts other real arguments, but these theorems do not
certify those cases.

## Conditional SQL-shaped bounds

The physical parameters `hbar`, `m`, and `omega_m` are additional positive real
numbers. Assuming the calibration inequality

\[
\left(\frac{\hbar}{2m\omega_m}\right)^2\le AB,
\]

the module proves

\[
\frac{\hbar}{m\omega_m}\le V(I),\qquad
\sqrt{\frac{\hbar}{m\omega_m}}\le\sqrt{V(I)}.
\]

This calibration is a hypothesis, not a consequence of a formalized Heisenberg
uncertainty relation or commutation relation. The square-root conclusion follows
by monotonicity of `Real.sqrt`; its interpretation as a standard deviation needs
the external variance interpretation of \(V\). The attained algebraic minimum is
\(2\sqrt{AB}\); the possibly smaller calibrated bound is not asserted to be
attained. Equality in the calibrated bound additionally requires saturation of
the calibration inequality.

## Proof entry points

All names below belong to `QuantumStandardQuantumLimit`.

| Declaration | Result |
| --- | --- |
| `noiseVariance_gap_identity` | Exact square remainder for positive `A`, `B`, `I`. |
| `noiseVariance_lower_bound` | Nonstrict lower bound `2 * Real.sqrt (A * B)`. |
| `optimum_intensity_pos` | Positivity of `Real.sqrt (A / B)`. |
| `noiseVariance_balance_at_optimum` | Equality of the two contributions at the optimizer. |
| `noiseVariance_optimum_value` | Attainment of the algebraic lower bound. |
| `noiseVariance_unique_min` | Equality holds exactly at `I = Real.sqrt (A / B)`. |
| `noiseVariance_strict_away` | Strict bound when positive `I` differs from the optimizer. |
| `sql_variance_bound` | Calibrated variance bound under all positivity and calibration hypotheses. |
| `sql_standard_deviation_bound` | Square-root form under the same hypotheses. |

`QuantumSQLFormalSuite` packages the gap, lower bound, attainment, balance,
uniqueness, and two calibrated conclusions; `quantum_sql_master_suite` supplies
its proof. There are no direct imports from other `Verification` modules.
Dependencies are Mathlib real arithmetic, square roots, and algebraic tactics.

## Physical scope and use

The reusable result is an exact optimization certificate for a supplied
inverse-plus-linear noise model. Applying it to a detector requires justifying
the formula, parameter units, positivity, and calibration for that detector.
There is no Langevin equation, spectral-density model, susceptibility, noise
filter, measurement bandwidth, or conversion of spectra to integrated variance.
No hardware or simulator validation, device certification, or universal limit
for all quantum measurement schemes follows.

For physical context, [Clerk et al., *Introduction to quantum noise, measurement,
and amplification* (2010), Sec. III.B, Eqs. (3.57)–(3.59), and Sec. V.E](https://clerkgroup.uchicago.edu/PDFfiles/RMP2010.pdf)
discuss imprecision/back-action optimization using noise spectra and the role of
correlations. Those spectral quantities are not identified with this module's
scalar variance by a formal theorem. The reference supplies context, not a
derivation of the calibration hypothesis. Scientific and formalization priority
have not been assessed.

## Verification

The module passed `verify`, `audit`, and integration as `QuantumPhysicsFullSuite.standard_quantum_limit`. Strict build, `verify-all`, independent axiom audit, the public regression tests without skips, and catalog checks passed. A compiler regression checks an asymmetric optimum, tight calibration, and counterexamples outside the hypotheses. See the [validation record](../VERIFICATION.en.md).
