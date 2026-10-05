# Release v0.5.7 verification record

This release adds operational Raft commit-index provenance and ordered local state-machine application, with integration, compiler regressions and English scope cards.

## Source and packaging

Private source: `6d95f3a009bcb6057997f3f28d08e331e61ad2cc`.
Previous public main: `1d82058566af1f7b1c38acb284a4acac69e666ce`.
Package version: 0.5.7.

The existing allowlisted exporter supplies all three new files:
DistributedRaftCommitApplication, DistributedRaftCommitIndexInvariant and
DistributedRaftCommitApplicationExample. All 148 Lean sources, including
Verification.lean, match the private snapshot byte for byte. The package also
includes integration recipes, the new Python/Lean regressions, all three English
cards and the historical private verification report. Public settings, dependencies,
CI, licenses, historical releases and previously corrected scope cards are retained.
No Russian cards or simulations archive is copied.

## Mathematical scope

Induction over the existing server/message transitions derives the provenance of
positive commitIndex prefixes from earlier actual current-term commit events,
including partially propagated prefixes, and proves prefix retention. An application
overlay derives ordered non-repeating local application, deterministic List.foldl
replay and commitment provenance for every applied entry. Desired safety facts are
not added as transition guards. The underlying operational Step is unchanged.

Cross-node fold agreement requires equality of full prefix entries, including
commands. Matching only legacy index/term metadata is insufficient, with a checked
counterexample. A reachable 45-transition old-term-majority trace demonstrates that
an acknowledged majority alone is not a current-term commitment certificate.
Compiler regressions also cover an eleven-network-transition positive execution,
leader/follower application and rejection of early, duplicate and wrong-entry steps.

This extension does not prove a new global State Machine Safety theorem, liveness,
client exactly-once behavior, asynchronous timeout behavior, crash/recovery,
fsync/WAL or deployed network-partition behavior. The existing abstract operational
model already permits packet loss, duplication and arbitrary delivery order.

## Validation

- **109 unique direct imports**, **147 Lean files** under Verification/.
- Fresh strict build: **3529 jobs**, zero warnings.
- Full local verify-all: **147 modules**, **9820 declarations**, no violations or source changes.
- Independent pinned audit: **9820 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **44 public tests** passed in **78.996 seconds**, no errors, failures or skips.
- Integration is idempotent; all source hashes match after live tests.
- Catalog, local links and the 256-node static placement provenance checks pass.
- Original HEAD and all **406 tracked-file hashes** are unchanged.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.DistributedRaftCommitApplication DistributedRaftCommitApplicationSuite
```

The separate independent audit uses leanprover-community/axiom-audit v0.1.2,
pinned at `46024e005996495c65ef609368e11ab39c4222e3`, with allowlist
`propext,Classical.choice,Quot.sound`. Compilation of AxiomAudit.lean is an
additional registry hook, not a substitute for that independent tool.
The verifier CLI has no audit-all/test-all commands.

The [validation snapshot](../tools/validation_snapshot.json) records measured public
results. The [historical private report](raft-commit-application-verification.en.md)
retains its distinct private-test result. See the
[scope card](../knowledge/09_distributed_systems/DistributedRaftCommitApplication.md).

## Isolation and remaining obligations

The public release is prepared in an isolated clone from remote main; the private
source clone is fixed at the selected commit. The new annotated tag and main are
published together with git push --atomic, without force or tag replacement.

Numerical rationalization, exact cell-boundary comparison and SimLab search remain
unformalized. Python, JSON/RFC 8259, SHA-256 implementations, source authenticity
and binding external inputs to bytes remain separate obligations. Equal digests
do not prove equal bytes. Historical indeterminate results keep their status.

This task makes no writes to simulations and does not revert parallel SimLab work;
directory-wide immutability is not claimed. Final control snapshots check the
original HEAD and all 406 tracked-file hashes. Both isolated Git trees are checked
clean after publication.
