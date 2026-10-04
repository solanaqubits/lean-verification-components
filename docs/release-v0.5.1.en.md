# Release v0.5.1 verification record

This release adds three registry suites in five Lean files:

- NumericBinaryGrid: exact magnitude decoding and parity.
- NumericRoundingCertificates: rational nearest-even rounding and local certificates.
- NumericRealRounding: real-input semantics agreeing with rational casts.
- NumericSQLIntervalBounds: conditional root enclosures and the real rounding bridge.
- NumericCertificateDigestBridge: conditional composition with supplied digest/parser functions.

The package has **103 unique direct MasterSuite imports**, **139 Lean files** under
Verification and **8,680 audited declarations**, including generated declarations.
The historical MasterHundredRegistry remains unchanged. Relative to v0.5.0,
this adds five source files, three direct imports and 443 declarations.

## Source and export checks

The selected private source snapshot is
`2157ef97939cb466d3cc2bfdc34fac011d785c7d`; the public base is
`602c2db51ff1c8ee8f3aed6c74fac8b2083ed4b6`. These identify source provenance, not
an assertion that private commits exist in the public history.
All **140 Lean source files including Verification.lean** match the selected private
snapshot byte-for-byte. The toolchain, license and dependency manifest agree
(the manifest package name differs intentionally).

The existing allowlisted exporter supplied the source, tests, English cards,
recipes and curated data. Its older public page templates were reconciled with
the current snapshot. Existing public CI, package metadata and reviewed Raft
scope documentation were preserved. No Russian cards, simulation environment,
Git history from the private repository, or full simulation archive was copied.

The curated rounding provenance file is unchanged, SHA-256:
`8972e247d30147a80fb6d12c5e335a37c99d40d6cdcf819e5ea34f4718ab3729`.
Its simulation paths describe external provenance; those source artifacts are not
included here and no Lean theorem parses or authenticates the metadata.
The existing chip converter reproduces all 256 rational placement records and
checks the packaged input hashes.

## Measured validation

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The project build directory was fresh; dependency artifacts were copied into an
isolated cache. The strict build completed with **3,521 jobs**, no warnings.
The local CLI freshly checked **139 modules**, audited **8,680 declarations**,
and reported unchanged source hashes. The independent axiom-audit tool pinned at
`46024e005996495c65ef609368e11ab39c4222e3` reported the same declaration count.
Both audits permit only `propext`, `Classical.choice`, and `Quot.sound`.

All **38 public tests passed with zero skips**. The private snapshot recorded
41 tests; the public test selection is intentionally different. Tests include the
three numerical compiler regressions, recipe idempotence and rollback behavior.
The three new integration plans also independently produce empty diffs.
The English catalog contains **139 cards in 12 sections**; local links pass.
The CLI does not implement audit-all/test-all; verify-all, independent audit and
live unittest discovery supply the corresponding complete checks.

## Boundaries retained

Rational and real rounding are mathematical specifications; equivalence to Python
or CPU instructions is not proved. Signed zeros, subnormal midpoint ties,
overflow, and historical indeterminate intervals retain their recorded meanings.
Later exact-midpoint/exact-zero evidence does not replace old interval outcomes.

The SQL target is `sqrt(hbar/(mass*frequency))`, conditional on positive input
intervals and containment hypotheses. It is not the SimLab optimization gap
`G=A/I+B*I-2*sqrt(A*B)`, whose specific enclosure composition remains separate.
Physical detector calibration, noise correlations and device characteristics
are not certified.

The digest bridge fixes external pure digest/parser functions and a magnitude grid.
The expected digest and SQL inputs also remain external context. SHA-256's bit-level
implementation, JSON/RFC 8259 conformance, Python equivalence, byte binding of those
inputs and source authenticity remain unproved. Equal digests do not imply equal
bytes. The full third obligation is **not** declared complete.

Earlier boundaries also remain: scalar MuSig2 is not a cryptographic security
proof; the forking result is an elementary matrix bound; visibility is not quantum
decoherence; the optomechanical approximation regime is documented, not derived.

## Reproducible artifacts

[Validation snapshot](../tools/validation_snapshot.json) records exact source hashes
and measured public counts. [Numeric cards](../knowledge/12_numeric_certificates/README.md)
state theorem premises and interfaces. The three imported private numerical reports
are labeled historical records; this file records the public release validation.

Work was performed in isolated clones and a separate dependency copy. The original
workspace and simulations were not modified by this release task.
