# Release v0.5.31: Observed-remove set and causal add-wins

Private proof snapshot: `9502d727465b13c7895370b4a6dc3f5000616e38`.
Previous public main: `f7c89535451f5893632941ef03922d733bd043f0`.

## Proven scope and assumptions

The OR-Set retains finite sets of all added element/tag pairs and removed pairs.
Visibility requires an added tag without a tombstone. Componentwise union gives an
unconditional join semilattice; reachable transitions preserve removed subset added.
Persistent per-replica counters imply unique operation IDs and fresh add tags.
Removal captures its observed live tags once; reception never recomputes that context.

Independent observation causality supports add-wins for a concurrent add/remove pair,
including their complete post-operation snapshots. A later removal that observes the
new tag may remove it. Tombstones prevent resurrection of a fixed removed tag;
a new add restores visibility using a fresh tag. Metadata are monotone; visible
membership is not. Equal included immutable updates, with their captured removal
contexts, imply equal states independently of delivery order and duplicates.

Authentic sent snapshots remain reliably available. Recurring sends and weak fairness
for continuously useful receptions imply eventual dissemination. After updates cease,
all replicas stabilize to the finite global join. The causal-broadcast adapter uses
actual delivery logs and proves convergence for an announced covering finite batch,
including snapshots of a fixed reachable checkpoint. It does not claim a fully coupled
serializer for arbitrary ongoing updates. Full-state union does not need causal order.

Regressions cover empty state, local add/remove/re-add, concurrent add/remove, partial
observation, stale snapshots and duplicates. Counterexamples show suppression by tag
reuse and resurrection after premature tombstone collection followed by a stale snapshot.

Correct tombstone garbage collection, ORSWOT compression, linearizability, dynamic
membership, memory-loss recovery and Byzantine behavior are not modeled. Natural
counters do not overflow; bounded machine counters are outside this model. Python,
JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 133 |
| Lean files under Verification/ | 173 top-level + 2 auxiliary = 175 |
| Root-inclusive sources identical to the private snapshot | 176 |
| Clean strict build | 3624 jobs; no warnings |
| Complete verifier audit | 16494 declarations; no violations |
| Pinned independent full audit | 16494 declarations; no violations |
| Public live tests | 78; no failures or skips; 277.247s |

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

All 176 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.31. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedCRDTORSet.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
