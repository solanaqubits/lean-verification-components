# Release v0.5.22: General Chandy-Lamport snapshots

Private proof snapshot: `d06eee279392f800cbb8a5ff8dff3af30b051edc`.
Previous public main: `b11f5ca5ea2d619bd678155f069e447c098e9c7c`.

## Proven scope and assumptions

The model covers arbitrary finite directed networks with edge-indexed FIFO queues,
arbitrary application payloads and local data. A node captures its actual local
value and event counter once, atomically appending markers to outgoing queues.
The cut is consistent: every receipt before the destination cut has a matching
send before the source cut. Phase observations are linked to strict event order.

Every closed channel records exactly the ordered crossing messages: sent before
the sender cut and received after the receiver cut. Packet identities distinguish
repeated payloads. Snapshots and closed channel records remain unchanged.

Termination requires directed reachability of all nodes from the initiator,
ReliableDelivery and WeakFairness. ReliableDelivery means each already queued
item is eventually processed or offered at the FIFO head; it includes progress
past earlier packets and is stronger than absence of transport loss alone.
Weak fairness governs continuously enabled initiation and marker reactions.
The theorem supplies a finite common completion index, not a uniform latency bound.
An explicit reliable fair execution witnesses satisfiability of the assumptions.

A non-FIFO counterexample adds only an adjacent swap: a marker overtakes an older
packet, and the closed channel record misses that packet. This demonstrates failure
of exact recording; it does not claim every reordering violates cut consistency.
A reliable fair disconnected execution demonstrates the need for root reachability.

One snapshot and fixed topology are modeled. Permutation/causal equivalence via
commuting application events, global termination detection, snapshot collection,
crashes, loss, recovery, dynamic topology, overlapping snapshots and Byzantine
behavior are outside the model. Python, JSON/SHA-256 and SimLab remain open obligations.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 124 |
| Lean files under Verification/ | 164 top-level + 2 auxiliary = 166 |
| Root-inclusive sources identical to the private snapshot | 167 |
| Clean strict build | 3615 jobs; no warnings |
| Complete verifier audit | 14271 declarations; no violations |
| Pinned independent full audit | 14271 declarations; no violations |
| Public live tests | 69; no failures or skips; 260.408s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py" -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

Regressions cover arbitrary graphs and payloads, an empty-channel fair execution,
three nodes with multiple incoming channels, repeated string payloads with distinct
packet IDs, captured local data and strict cut event order, unreachable nodes and
incoming senders, and an adjacent-swap anomaly unreachable in the FIFO semantics.

All 167 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.22. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedChandyLamportGeneral.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
