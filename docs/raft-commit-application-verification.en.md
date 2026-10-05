# Raft commitment and application verification record

Private baseline: `6a991c4e68244e11ca95a97a456ad8511c54eb32`.

The existing operational Step and entry types are unchanged. The new main module
uses two support files: a chronological commit-index invariant and a reachable
old-term-majority counterexample. This is one new direct registry module and
three new Lean source files, not three new direct registry entries.

The server/RPC induction proves that every positive local committed prefix has
an earlier actual current-term commit event. Propagated partial prefixes are
covered and retained. An asynchronous application overlay then derives ordered,
non-repeating local application, agreement with deterministic foldl replay and
commit provenance for every applied entry, without adding safety witnesses as
guards. Full-entry equality remains explicit in the cross-node fold theorem.
A new global State Machine Safety theorem, liveness or client exactly-once
semantics is not claimed.

The proposed legacy LogsMatchUpTo premise was insufficient: its entry type has
no command field. A kernel-checked counterexample records the correction. Explicit
adapters relate the distinct pre-existing entry types. Snapshot majority uniqueness
is kept separate from operational commitment across time. A 45-transition reachable
Figure-8-style scenario has an acknowledged old-term majority which is later
overwritten; the current-term commit guard rejects it.

## Validation

The registry has **109 direct imports** and **147 Lean files**.
A fresh project build completed **3529 jobs**, without warnings. Module verify
and audit each checked **1436 imported project declarations**. Full verify-all
and the pinned independent audit checked **9820 declarations**, with only the
three allowed axioms. The strict AxiomAudit.lean hook passed.

All **47 private live tests** passed in **76.977 seconds**, without errors,
failures or skips. Source hashes remain unchanged after testing. Integration is
idempotent. RU/EN catalog, links and static placement provenance pass. The exporter
preserves all **148 Lean sources**, including the root, byte for byte and
includes the new tests and English cards. No simulations archive or .ru.md card
is exported. This prepares export but does not publish a public release.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify Verification/DistributedRaftCommitApplication.lean
python3 tools/verifier_skill.py audit Verification/DistributedRaftCommitApplication.lean
python3 tools/verifier_skill.py integrate Verification.DistributedRaftCommitApplication DistributedRaftCommitApplicationSuite --apply
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The independent audit uses leanprover-community/axiom-audit v0.1.2, pinned at
`46024e005996495c65ef609368e11ab39c4222e3`. Only propext, Classical.choice and
Quot.sound are allowed. No audit-all/test-all commands, native-decide shortcuts,
new axioms or proof placeholders are used. No new linter is disabled.

The compiler regressions contain a real election, commit, leaderCommit propagation
and application by both leader and follower, alongside early/duplicate/wrong-entry
rejection and ordered noncommutative fold checks. The positive run has eleven
network transitions. Full audit includes the 45-transition negative example.

Integration targets MasterSuiteComponents with an explicit recipe. The allowlisted
exporter includes all three Lean sources, their English cards, regression files
and this report. No public release is performed in this task. See the
[scope card](../knowledge/09_distributed_systems/DistributedRaftCommitApplication.md)
and [validation snapshot](../tools/validation_snapshot.json).

## Limits and isolation

Loss, duplication and arbitrary delivery order belong to the existing fixed-cluster
model. Timers, fairness, eventual application, dynamic membership, Byzantine injection,
crash/recovery, fsync/WAL and deployed partition behavior are outside this proof.
Python, JSON/SHA-256, source authenticity and external SimLab input-byte binding
remain separate obligations. Historical simulation outcomes are not modified.

Work used an isolated clone and external scratch paths. Original HEAD and all
**406 tracked-file hashes** were preserved. Concurrent SimLab activity added
0 metadata entries and changed 0, with 0 removed between
control snapshots. This task made no writes to simulations and did not revert
parallel work; directory-wide immutability is not claimed. The isolated working
tree is clean after commit and private-main push.
