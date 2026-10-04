> Historical private validation record, reproduced for proof scope. Current public validation is in [v0.5.1](release-v0.5.1.en.md). Private commit identifiers are provenance labels, not public commit links.

# Real SQL interval and rounding verification

Verified Lean source commit: `9c1ffc1b0aff9753ddb55f11dbaaed976f05a439`.

`NumericSQLIntervalBounds` is the 102nd direct import. Its helper `NumericRealRounding`
adds real-input rounding semantics without changing the rational checker. There are
138 Lean files under Verification, 8,604 audited declarations, and 3,528 strict build jobs.
The historical MasterHundredRegistry remains unchanged.

## What is proved

The prescribed target is `sqrt(hbar/(mass*frequency))`. Positive input intervals
and membership of the actual real parameters are explicit hypotheses. Rational
multiplication/division give `H.lo/(M.hi*W.hi)` and `H.hi/(M.lo*W.lo)`.
The Boolean root checker tests nonnegative endpoints and exact square inequalities.
Its accepted witness encloses the real root. An accepted existing rounding
certificate then fixes the encoded result of that real root, including irrational
values. Real semantics agrees with rational rounding on casts and uses the same
signed-zero and virtual-overflow conventions.

An explicit coarse fallback `[0, radicand.hi+1]` is constructed and verified.
Restriction preserves root witnesses when the radicand interval shrinks; no
adaptive refinement algorithm or precision-termination theorem is claimed.

The upper root bound cannot be justified by its square alone. Requiring the lower
bound nonnegative is a conservative format restriction, not a mathematically
necessary condition for every lower estimate.

## Validation

```bash
python3 tools/verifier_skill.py verify Verification/NumericSQLIntervalBounds.lean
python3 tools/verifier_skill.py audit Verification/NumericSQLIntervalBounds.lean
python3 tools/verifier_skill.py integrate Verification.NumericSQLIntervalBounds NumericSQLIntervalBoundsSuite --apply
lake clean
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

Module verify/audit passed, covering 365 declarations in the selected import closure.
Integration passed and the final plan is idempotent. Clean strict build: 3,528
jobs, no warnings. Verify-all: 138 modules, 8,604 declarations, unchanged source
hashes during verification. The independent pinned axiom-audit tool
`46024e005996495c65ef609368e11ab39c4222e3` reports the same declaration count.
Only `propext`, `Classical.choice`, and `Quot.sound` are permitted by both audits.
All 40 tests passed with no skips. The catalog contains 138 modules in 12 sections.
The local CLI has no audit-all/test-all subcommands; the complete audit and test
commands above provide those checks.

The first integration attempt was rolled back when the source-stability check
noticed a concurrent source-comment/audit edit. The subsequent unchanged-source
integration and complete checks passed; no failed result is counted as validation.

## Regression evidence

The compiler regression constructs exact 80-bit rational bounds for `sqrt(2)` and
checks both the enclosure and binary64 code `4609047870845172685` in the kernel.
It composes the entire SQL theorem on parameters `(2,1,1)`, tests uncertain positive
input intervals, rejects negative-upper and too-narrow square witnesses, accepts
zero for the generic root checker, and retains an indeterminate broad interval.
Signed underflow, the exact rational half, and the historical indeterminate
interval are also checked. Examples use `decide +kernel`, not native-decide.
These are mathematical regression constants, not a claim of verified JSON ingestion.

## Boundaries and isolation

This target is distinct from SimLab's gap `A/I+B*I-2*sqrt(A*B)`; its complete
witness pipeline remains outside this module. Physical calibration and confidence
in input intervals are not derived. Python equivalence, JSON parsing, SHA-256 and
byte-to-Lean correspondence remain unverified. SHA-256 does not authenticate authors.

Work was performed in an isolated clone. No simulations files were edited or
regenerated, and the original workspace was not checked out, reset, or merged.
This task pushes the private main only; no public release is made here.
