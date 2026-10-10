# Release v0.5.30: State-based LWW register and strong convergence

Private proof snapshot: `fb5b736e7f4794f96e1ee5f61d9b50af7cd8a571`.
Previous public main: `7fec9076e21cd3d90c3c5979401585ecee383ecf`.

## Proven scope and assumptions

The model is a state-based LWW register for a fixed group of replicas. Stamps
are ordered lexicographically by logical counter and replica ID. Operational
freshness proves that equal issued stamps carry equal values. Merge forms a
bounded join semilattice on states compatible with a common valid history;
commutativity is not asserted for malformed conflicting values at one full stamp.

The payload is the maximum of its included update history. Equal included update
sets imply equal payloads, independently of ordering and duplicates. This strong
convergence result is distinct from conditional dissemination. Reliable availability
of authentic immutable snapshots, fair sending and per-useful-snapshot weak
fairness imply eventual information subsumption. After new writes cease, all
replica payloads permanently stabilize to the global maximum.

An incremental adapter replays snapshots along actual DistributedCausalBroadcast
application delivery logs. Its finite-batch and checkpoint theorems derive
saturation from reliable arrival and weak fairness. A coupled serializer and
arbitrary ongoing-write transport implementation are not asserted. Regressions
cover bottom, one replica, concurrent equal counters resolved by ID, stale and
duplicate snapshots, fresh relay writes, and malformed tie/stale-write rules.

Convergence concerns the register value, not clocks or ghost logs. Linearizability,
distributed consensus, preservation of all concurrent versions, physical-clock
or NTP synchronization, crash recovery or recovery after nonvolatile-memory failure,
Byzantine participants and dynamic membership are not modeled. Mathematical natural
counters do not overflow; bounded machine-counter implementations are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 132 |
| Lean files under Verification/ | 172 top-level + 2 auxiliary = 174 |
| Root-inclusive sources identical to the private snapshot | 175 |
| Clean strict build | 3623 jobs; no warnings |
| Complete verifier audit | 16006 declarations; no violations |
| Pinned independent full audit | 16006 declarations; no violations |
| Public live tests | 77; no failures or skips; 271.527s |

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

All 175 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.30. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedCRDTStateLWW.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
