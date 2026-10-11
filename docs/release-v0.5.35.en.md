# Release v0.5.35: Operational Multi-Paxos consensus

Private proof snapshot: `c3a0f1586f2d4271fd1bb0ff3d1a22261341b235`.
Previous public main: `720856b936c4de9d68ffc799eb07b9fdb642309f`.

## Proven scope and assumptions

The operational Multi-Paxos model derives promise monotonicity, uniqueness of proposals per (ballot, slot), preservation of chosen values across ballots, slot Agreement and comparability of executed log prefixes. A phase-one certificate is reused across multiple slots. SingleVote is derived for the older model, not assumed as an external hypothesis. Chosen records historical votes; proposals use write-once storage. Concrete faulty traces show disagreement when maximum-ballot selection or ballot ownership with write-once proposals is weakened.

Safety covers an ideal static, non-Byzantine asynchronous network with arbitrary delays, reordering and duplicates; the model also permits message loss. No liveness or FLP theorem is proved. FLP motivates separating safety from progress: a future progress contract needs a stable leader, an available quorum, suitable delivery/retransmission and scheduling fairness. A stable leader alone does not guarantee termination.

Reconfiguration, checkpoints, log compaction, recovery after loss of durable state and Byzantine attacks are outside scope. Linearizability, client deduplication and exactly-once effects are not proved. Python, JSON/SHA-256 and SimLab correctness obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 137 |
| Lean files under Verification/ | 177 top-level + 2 auxiliary = 179 |
| Root-inclusive sources identical to the private snapshot | 180 |
| Clean strict build | 3727 jobs; no warnings |
| Complete verifier audit | 17615 declarations; no violations |
| Pinned independent full audit | 17615 declarations; no violations |
| Public live tests | 82; no failures or skips; 278.315s |

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

All 180 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.35. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedMultiPaxosConsensus.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
