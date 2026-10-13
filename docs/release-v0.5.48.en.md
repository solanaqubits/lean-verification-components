# Release v0.5.48: Raft joint-consensus reconfiguration

Private proof snapshot: `6c11fa68d512262675d779ef4568e3782caa9f43`.
Previous public main: `022ca82b846b3fbee8aa23c5f55b94670f93b440`.

## Proven scope and assumptions

This release proves safety for one arbitrary fixed transition from stable-old
through joint-old-new to stable-new, with commands, leader changes and delayed,
duplicated or reordered messages. Configurations activate from the latest local
log entry before commitment and roll back deterministically on suffix removal.

Reachability implies historical commit-index soundness, committed-prefix
preservation, Election Safety in every term, Log Matching and Leader Completeness.
Old and new stable quorums may be disjoint; incompatible successful elections are
excluded by the historical joint-commit barrier, not by assuming they intersect.
The regressions include a reachable disjoint handover, leader retirement and
rollback after a leader change. The direct-switch counterexample is an algebraic
split-vote construction, not a separate unsafe protocol execution.

Unbounded reconfiguration chains, snapshots, Byzantine faults, crash/recovery
and liveness are outside scope. The static Raft bridge concerns local command-only
log merging, not a full simulation. Python, JSON/SHA-256 and SimLab obligations
remain open; running the test harness does not verify a Python Raft implementation.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 150 |
| Lean files under Verification/ | 190 top-level + 2 auxiliary = 192 |
| Root-inclusive sources identical to the private snapshot | 193 |
| Clean strict build | 3741 jobs; no warnings |
| Complete verifier audit | 20338 declarations; no violations |
| Pinned independent full audit | 20338 declarations; no violations |
| Public live tests | 95; no failures or skips; 303.516s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

All 193 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.48. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedRaftJointConsensusReconfig.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
