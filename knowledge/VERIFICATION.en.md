# Verification record

[Knowledge base](README.md)

The Lean sources are distributed with SHA-256 hashes in
[validation_snapshot.json](../tools/validation_snapshot.json). The imported proof
snapshot contains 74 Lean files under Verification/, 51 direct MasterSuite
imports, and 3,809 declarations including generated declarations.

The public export is checked separately with:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

The allowed axioms are propext, Classical.choice, and Quot.sound. The single
registry audit checks the selected theorem; verify-all audits all project
modules. The CI workflow also runs an independent project-wide axiom audit.

Formal claims retain their hypotheses. Successful compilation and an allowed
axiom list do not establish end-to-end cryptographic security, the correctness
of a production implementation, or scientific novelty.

## v0.2.0 local validation

Strict full build: 3379 jobs. The verifier checked all 74 Lean files and audited
3809 declarations; the independent pinned axiom auditor reported the same count
and no violations. All 19 public regression tests passed without skips.
The knowledge catalog contains 74 cards across 11 sections; 93 Markdown files
passed local link validation. All Lean sources match the reviewed source hashes.
