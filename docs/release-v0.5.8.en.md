# Release v0.5.8 — operational 2PC timeout safety

Private source: `fac78833f819eb57ec9d69e67dc80ef5613e4c8c`.
Previous public main: `ea4f93ce791d5a60ef7a2c8a6131a259a63bcf5e`.

This release adds [DistributedTwoPhaseCommitTimeout](../knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md), registry integration and operational regression tests. All 149 Lean sources, including the root file, match the private snapshot byte for byte.

## Guarantees and boundaries

The reachable operational model derives agreement, permanent pre-vote abort safety,
and two reachable histories with identical complete prepared local views. Any
local deterministic policy forced to choose commit or abort on that timeout view
violates agreement in one history. Waiting is not ruled out.

With both participants prepared and the coordinator stopped, absence of queued
decision packets is equivalent to absence of a finite continuation reaching a
terminal participant. Channels need not be empty: other packets may remain.
An in-flight decision permits delivery after the crash. Guaranteed delivery,
completion of both participants, fairness, coordinator recovery, peer resolution,
3PC, disk durability and physical timeout detection are not established.

Python, JSON parsing, SHA-256 implementation, source authenticity and external
SimLab input binding remain separate obligations. Historical indeterminate
results and separate exact-zero evidence are not reclassified.

## Validation

- **110 unique direct imports**, **148 Lean files** under Verification/.
- Strict build: **3530 jobs**, zero warnings. Dependency caches are isolated copies; this is not a from-source rebuild of Mathlib.
- Full local verify-all: **148 modules**, **10333 declarations**, no violations or source changes.
- Independent pinned audit: **10333 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **45 public live tests** passed in **78.809 seconds**, without errors, failures or skips.
- Integration is idempotent; all audited source hashes still match after tests.
- Catalog, local links and static 256-node placement provenance checks pass.
- All **149 Lean sources** match the private snapshot.
- Original HEAD and all **406 tracked-file hashes** are unchanged.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The independent audit uses leanprover-community/axiom-audit v0.1.2 pinned at
`46024e005996495c65ef609368e11ab39c4222e3`, allowing only `propext`,
`Classical.choice`, `Quot.sound`. The AxiomAudit.lean invocation is an additional
strict hook. No audit-all or test-all commands are assumed.

## Isolation and publication

The public checkout and private source snapshot are isolated from the original
working environment. Existing public configuration and release history are retained.
No Russian cards or simulations directory are exported. This task makes no writes
to simulations; concurrent simulation work is not reverted or claimed immutable.
The release uses an annotated tag and `git push --atomic origin main v0.5.8`,
without force or replacement of an existing tag.
