> Historical private validation record, reproduced for proof scope. Current public validation is in [v0.5.1](release-v0.5.1.en.md). Private commit identifiers are provenance labels, not public commit links.

# Rational rounding certificate verification

Verified source commit: `aeb6cc9f996e348764bcd70414868f536e335d2b`.

`NumericRoundingCertificates` is the 101st direct MasterSuite import. Its helper
`NumericBinaryGrid` adds a second Lean source file. The repository now contains
136 Lean files under Verification, 132 subject files plus four registry/audit
support files, and 8,522 audited declarations including generated declarations.
The historical hundred-import package remains unchanged; the central registry
adds a separate `rounding_certificates` field.

## Established results

- Exact quotient/remainder decoding of binary magnitudes, strict monotonicity,
  subnormal quantum, virtual overflow neighbor and significand parity.
- A global nearest-even magnitude specification and its nearest-value property.
- Signed representations distinguishing both zeros and both infinities; exact
  rational zero canonicalizes to positive zero.
- Convex rounding fibers: equal rounded endpoints determine every rational input
  between them, with enclosure membership an explicit hypothesis.
- Sound and complete local cell checks, using at most two neighboring boundaries
  instead of enumeration of the binary64 grid.
- Exact midpoint checking and even-code selection, with accepted finite,
  subnormal, signed underflow and overflow examples.

The count-based semantic specification is finite and computable but impractical
for full binary64 enumeration. The certificate checker uses local arithmetic.
Arithmetic runtime still depends on operand sizes; no resource-bound theorem is
claimed.

## Regression evidence

The 11 provenance entries correspond to seven positive midpoint fixtures, the
singleton interval `[1/2,1/2]`, the inconclusive interval `[0,1]`, and two original
256-bit records sharing the same rational enclosure. Tests additionally cover
negative zero, signed overflow, near-ties, wrong adjacent-code indices, reversed
bounds and an incorrect claimed result. Closed computations use `decide +kernel`,
not native-decide shortcuts.

Both original decimal records `zero_midpoint_0` and `zero_midpoint_1` retain:

```
L = (2^256 - 6) / 2^1331
U = (2^255 + 1) / 2^1330
round(L) = +0; round(U) = least positive subnormal.
```

Their interval result remains indeterminate. Later exact evidence is a separate
certificate; it does not modify those historical records. Three source-artifact
SHA-256 values were checked externally while reading simulations. The curated
[provenance metadata](../data/numeric_rounding/regression_provenance.json) is not
itself a Lean theorem or an authenticated source record.

## Checks performed

```bash
python3 tools/verifier_skill.py verify Verification/NumericRoundingCertificates.lean
python3 tools/verifier_skill.py audit Verification/NumericRoundingCertificates.lean
python3 tools/verifier_skill.py integrate Verification.NumericRoundingCertificates NumericRoundingCertificatesSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

Module verify and audit passed: 284 declarations in the new imported module
closure. Integration passed; the final shorter field name was then rebuilt,
and the final integration plan is empty (idempotent).
The strict project build completed with 3,518 jobs and no warnings.
Verify-all passed for 136 modules and 8,522 declarations, with source hashes
unchanged during verification. Independent axiom-audit at pinned tool commit
`46024e005996495c65ef609368e11ab39c4222e3` reported the same 8,522 declarations.
Both audits allow only `propext`, `Classical.choice`, and `Quot.sound`.
All 39 tests passed without skips, including compiler regressions and public
export checks. The catalog covers 136 modules in 12 sections.
The installed CLI does not provide `audit-all`; its complete `verify-all` audit
and the independent audit supply those checks.

## Remaining obligations

The semantic argument is rational. Irrational SQL expressions require a separate
real-input rounding model or a theorem for real values within rational enclosures,
as well as a proof constructing those enclosures. Neither Python equivalence,
JSON parsing, SHA-256 correctness, byte-to-Lean correspondence nor physical
properties of a detector are proved. Simulations were read only; no simulation
artifact or checker was changed. This task updates private main, not the public
v0.5.0 release.
