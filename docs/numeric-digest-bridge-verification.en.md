> Historical private validation record, reproduced for proof scope. Current public validation is in [v0.5.1](release-v0.5.1.en.md). Private commit identifiers are provenance labels, not public commit links.

# Conditional certificate digest bridge verification

Verified Lean source commit: `b3ca57fde6b5919a83a00d9501a3d539a0512036`.

`NumericCertificateDigestBridge` is the 103rd direct MasterSuite import. The project
contains 139 Lean files under Verification and 8,680 audited declarations.
The historical hundred-module registry is unchanged; the central registry has an
additional `digest_bridge` field.

## Exact result

The digest algorithm and decoder are explicit pure-function parameters. Digest32
has 32 byte-valued coordinates; its width does not specify SHA-256. ParsedCertificate
contains rational endpoints and an encoded result for a context-fixed magnitude
grid. No invented SHA-256 implementation or custom axiom is used.

`validate_payload_eq_some_iff` proves that acceptance of a record means all three
of the following hold for that same record and input bytes:

1. The parameterized digest equals the caller's expected value.
2. The parameterized parser returns that record on those bytes.
3. The existing rational interval checker accepts the record's claimed result.

The end-to-end theorem derives real rounding when the real target lies between
the parsed bounds. The SQL specialization derives containment for
`sqrt(hbar/(mass*frequency))` under positive localized input intervals and a checked
root witness. Explicit endpoint equalities connect that root witness to the parsed
record. H/M/W and the root witness are external arguments, not fields proved to
have been decoded from those bytes. The SimLab optimization gap is a different target.

Digest congruence and its contrapositive are proved for every pure function.
A constant-digest counterexample demonstrates that equal outputs do not imply equal
bytes in this abstraction. The source of the expected digest is not authenticated.
Grid, parser and digest configuration are external context; no format/version,
domain separator, signature, or configuration commitment is checked.

This is a conditional composition result, not completion of the full third
obligation. SHA-256 implementation, JSON syntax/conformance, equivalence to Python,
external byte-to-input binding, cryptographic authentication and detector physics
remain outside the proof.

## Checks performed

```bash
python3 tools/verifier_skill.py verify Verification/NumericCertificateDigestBridge.lean
python3 tools/verifier_skill.py audit Verification/NumericCertificateDigestBridge.lean
python3 tools/verifier_skill.py integrate Verification.NumericCertificateDigestBridge NumericCertificateDigestBridgeSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

Module verify and audit passed, covering 440 declarations in the selected
import closure. Integration passed with unchanged source hashes; the final plan is
empty. Full strict build: 3,521 tasks and no warnings. This run reused dependency
build artifacts; task counts are not directly comparable with the earlier clean
Mathlib rebuild. Verify-all freshly checked 139 modules and audited 8,680
declarations with unchanged sources. The independent tool pinned at
`46024e005996495c65ef609368e11ab39c4222e3` audited the same 8,680 declarations.
Both audits allow only `propext`, `Classical.choice`, and `Quot.sound`.
All 41 tests passed without skips. The catalog covers 139 modules in 12 sections.
The CLI has no audit-all/test-all commands; verify-all, independent axiom audit and
unittest discovery supply those checks.

## Regression evidence

[Compiler regressions](../tests/lean/numeric_digest_bridge_regression.lean) use
explicitly labeled toy adapters, not SHA-256/JSON test vectors. They cover successful
half-value parsing, wrong digest, failed parse, wrong claimed result, reversed
bounds, colliding digest values, two different decoders accepting different values
on identical bytes, extracted parse/digest equations, rational specialization,
and a full irrational sqrt(2) composition using exact rational bounds. Incorrect
root witnesses and unlinked endpoint choices are checked separately.
Closed examples are kernel-checked with `decide +kernel`; no native-decide shortcut
is used. Independent proof review found no substantive gap in the scoped theorem.

## Isolation

All changes were made in an isolated clone. No simulations artifacts were edited,
regenerated or reformatted. No checkout, reset or merge was performed in the original
workspace. This task updates private main only and does not publish a public release.
