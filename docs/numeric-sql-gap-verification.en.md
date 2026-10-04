# NumericSQLGapBounds verification

Historical private validation record for source snapshot `fb6176fdd9f0186c8c1406b7bf611d2b6b09af35`. Private test counts and isolation observations below describe that earlier run. The [public v0.5.2 report](release-v0.5.2.en.md) records public validation.

The module adds affine bounds for G=A/I+B*I-2*sqrt(A*B), its positive-parameter zero criterion A=B*I², canonical binary64 +0 and composition with the existing real rounding semantics. The baseline private commit is `2157ef97939cb466d3cc2bfdc34fac011d785c7d`. Exact checked file hashes are in [validation_snapshot.json](../tools/validation_snapshot.json).

## Interface and scope

The existing APIs are `NumericRealRounding.realRound` and `NumericRoundingCertificates.checkIntervalCertificate`; the schematic roundRealNearestEven/realIntervalCertificate names were not introduced. The affine inequality is valid without positivity assumptions. Nonnegativity and the zero equivalence require A,B,I>0. The composed theorem computes rational endpoints from exact rational parameters and derives enclosure of the actual real gap from checked root squares. Real-parameter endpoint composition is also available. No distance from a midpoint is assumed.

Exact zero is not a tie. Rounded +0 alone does not imply exact zero. The new static decimal regression preserves an inconclusive broad interval alongside a separate exact-zero theorem; it does not import or rewrite historical SimLab data. The existing historical interval theorem remains unchanged.

Rationalized enclosures and adaptive termination are separate work. JSON, SHA-256, Python equivalence, source authenticity and binding of external A,B,I bytes remain unproved. No detector physics is established. The earlier conditional digest bridge is not strengthened.

## Validation

- Strict build: **3522 jobs**, no warnings. Dependency and project caches were independent copies in the isolated checkout; this is not a from-source rebuild of Mathlib.
- Local verify/audit of the new module passed with 419 transitive declarations.
- Full verify-all: **140 files, 8710 declarations**, unchanged source hashes.
- Independent audit at `46024e005996495c65ef609368e11ab39c4222e3`: **8710 declarations**.
- Both audits allow only propext, Classical.choice, Quot.sound.
- **42 live tests**, zero skips; including irrational G, exact zero, a positive underflow tie, malformed root witnesses, sign handling, integration and public export.
- **104 unique direct imports** in MasterSuite; the historical hundred registry is unchanged.
- The new integration recipe is idempotent (empty second diff).
- RU/EN catalog and local links checked. Public export includes the new compiler regression and Python test.

```bash
python3 tools/verifier_skill.py verify Verification/NumericSQLGapBounds.lean
python3 tools/verifier_skill.py audit Verification/NumericSQLGapBounds.lean
python3 tools/verifier_skill.py integrate Verification.NumericSQLGapBounds NumericSQLGapBoundsSuite
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

The independent audit uses the existing pinned project CI tool. There is no audit-all CLI subcommand.

Work took place in an isolated checkout. The original workspace and simulations were not modified by this task. No public release was requested or published as part of this change.

The original 406 tracked-file hashes and HEAD remained identical. SimLab ran concurrently: its metadata snapshot grew from 18,211 to 20,524 entries during validation, so whole-directory immutability is not claimed. These external additions were neither edited nor reverted by this task.
