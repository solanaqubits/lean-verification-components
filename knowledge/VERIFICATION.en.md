# Verification record — v0.4.0

[Knowledge base](README.md)

This release contains 108 Lean files under `Verification/`, 84 direct MasterSuite
imports, and 6,442 declarations including generated declarations. The registry
assembles eleven suites. The root `Verification.lean` is counted separately from
the 108 files in that directory.

## Public-source validation

A clean rebuild of this package completed successfully with 3,490 jobs, including
dependencies, using Lean 4.33.1 and Mathlib v4.33.1. No warnings or errors were
reported. The independent `leanprover-community/axiom-audit` tool at commit
`46024e005996495c65ef609368e11ab39c4222e3` audited all 6,442 declarations; every
axiom dependency was within `propext`, `Classical.choice`, and `Quot.sound`.

`verify-all` passed for all 108 modules with no policy or axiom violations and
unchanged source hashes during verification. All 19 public tests passed with live
compiler tests enabled and no skips. The knowledge checker confirmed 108 cards
across 11 sections and checked local links in 127 Markdown files. Private
export-tool tests are not included in this public distribution.

Reproduce the release checks with:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

The source hashes and individual check results are recorded in
[validation_snapshot.json](../tools/validation_snapshot.json). `verify-all`
checks every project module and audits all project declarations. The single
registry audit in `Verification/AxiomAudit.lean` checks the selected registry
theorem's dependencies. CI also runs the independent project-wide audit.

## Export scope

The public package has independent Git history and English-only documentation.
Compared with the synchronized source distribution, 17 modules received standard
copyright headers and module documentation. `SolarisPhysicalModels` uses explicit
tactic imports instead of `Mathlib.Tactic`. These packaging corrections leave all
declaration and proof bodies unchanged; the snapshot hashes describe the actual
public files after those corrections.

MZI results are identities of a scalar trigonometric model, not a certification
of physical-device unitarity or hardware collapse. The thermal value 9.812 MPa is
computed from a one-dimensional scalar proxy, not a physical von Mises tensor.
Paxos safety concerns one ballot and explicitly assumes `SingleVote`; protocol
transitions and cross-ballot safety are outside that theorem.

Formal claims retain their hypotheses. Successful compilation and an allowed
axiom list do not establish end-to-end cryptographic security, the correctness
of a production implementation, or scientific novelty.
