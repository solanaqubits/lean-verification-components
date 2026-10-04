# Release v0.5.2 verification record

The release adds NumericSQLGapBounds: affine enclosures of G=A/I+B*I-2*sqrt(A*B),
G=0 iff A=B*I² for positive parameters, canonical binary64 +0 and composition
with the existing real rounding checker. It adds one direct registry import and
one Lean file; the historical hundred registry and previous proofs are unchanged.

## Source and export

Private source: `fb6176fdd9f0186c8c1406b7bf611d2b6b09af35`.
Previous public main: `6c4e097b59444f4f178feb9ea3e0e030e409dccc`.
All **141 Lean source files including Verification.lean** match that private snapshot
byte-for-byte. Existing public CI, package metadata, dependency manifest, license,
English documentation corrections and release history were preserved. Version is 0.5.2.

The existing allowlisted exporter supplied the new source, integration, compiler
regression, Python test and English card. Older exporter page templates were not
allowed to overwrite current public documentation. No Russian cards or simulation
archive were copied. Existing static provenance and chip placement data are unchanged.
The integration recipe produces an empty second diff.

## Measured checks

- **104 unique direct imports**, **140 Lean files**, **8710 declarations**.
- Strict build: **3522 jobs**, zero warnings, fresh project build directory and
  a separate copy of pinned dependency artifacts.
- verify-all: all **140 modules** checked, source hashes unchanged.
- Independent axiom audit pinned at `46024e005996495c65ef609368e11ab39c4222e3`:
  **8710 declarations**, matching the local audit.
- Both audits permit only propext, Classical.choice, Quot.sound.
- **39 public tests**, zero failures and skips (private baseline: 42 tests).
- English catalog and local links checked; source hashes verified.
- Existing 256-node chip manifest converter and input hashes checked.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.NumericSQLGapBounds NumericSQLGapBoundsSuite
```

There are no audit-all/test-all CLI subcommands; complete verification, independent
audit and live unittest discovery provide those checks.

## Boundaries

The affine enclosure is nonstrict and does not need positive parameters when root
containment is supplied. Nonnegativity and the zero equivalence assume A,B,I>0.
The checker composition actually derives the real gap enclosure from rational
square-root witnesses and exact rational parameters; it requires no distance from
a midpoint. Exact Zero is not a tie. A positive underflow midpoint can also round
to +0; a regression checks that separate case.

Historical indeterminate outcomes remain unchanged alongside separate exact-zero
and exact-midpoint evidence. Rationalized enclosures, exact comparisons of G with
quantization-cell boundaries, the new SimLab search and adaptive termination are
not formalized here. Python, JSON/RFC 8259, SHA-256, source authenticity and binding
of A,B,I to external bytes remain separate obligations. Digest equality does not
prove byte equality. The full third byte-correspondence obligation remains open.
No physical detector properties are established.

[Validation snapshot](../tools/validation_snapshot.json) stores the exact source hashes.
[Module card](../knowledge/12_numeric_certificates/NumericSQLGapBounds.md) documents
interfaces. The [private report](numeric-sql-gap-verification.en.md) is labeled
historical; its test counts and isolation observations describe the earlier run.

Work was performed in isolated trees. No command modified the original workspace
or simulations. Only the public main and a new annotated release tag are published.

The original 406 tracked-file hashes and HEAD remained identical. Concurrent SimLab work changed its own artifacts (metadata entries: 21,908 at start, 31,333 at final validation). Those changes were not edited or reverted by the release task; whole-directory immutability is not claimed.
