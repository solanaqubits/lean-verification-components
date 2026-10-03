# Release v0.5.0 verification record

The release has 100 unique direct MasterSuite imports, 134 Lean files under
Verification, and 8,237 audited declarations, including generated declarations.
The file count comprises 130 subject files and four registry/audit support files;
the milestone registry adds no independent domain theorem.

The delta from v0.4.5 contains three domain packages (threshold time envelopes,
elementary transcript forking, and a real beam-splitter model) plus the milestone
registry and its shared-component helper. Existing propositions and hypotheses
are preserved. English cards describe the limits of each model.

A fresh public compilation exposed missing copyright/license comment headers in
the three new domain files and the milestone file. Headers were added in both
repositories; no definition or proof changed. All 135 Lean source files, counting
the root file, were compared byte-for-byte between the final private and public
snapshots. Documentation source hashes were refreshed.

Validation commands:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The final strict build uses a fresh project build directory and the pinned
Lean/Mathlib 4.33.1 dependency cache: 3,516 jobs and no warnings. Public discovery
passes 35 tests without skips; private discovery passes 38. The CLI verifies
134 modules, reports unchanged source hashes, and audits 8,237 declarations.
An independent axiom-audit run, pinned to tool commit
`46024e005996495c65ef609368e11ab39c4222e3`, reports the same declaration count.
Both audits permit only `propext`, `Classical.choice`, and `Quot.sound`.

The catalog contains 134 English cards in 11 sections. Placement provenance
checks reproduce all 256 rational records and the existing input hashes.
JSON parsing and SHA-256 remain external checks, not Lean-proved implementations.
No simulation files or simulation environments are included or changed.

The current CLI has no `audit-all` or `test-all` subcommands. The complete
`verify-all` command, independent axiom audit, and live unittest discovery above
provide the corresponding checks. Source identities are recorded in
[the validation snapshot](../tools/validation_snapshot.json).
