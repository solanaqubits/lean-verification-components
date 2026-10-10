# Release v0.5.29: Causal broadcast and delivery safety

Private proof snapshot: `77948161a169a42dee824a8a2e1236e582665be4`.
Previous public main: `6e854f173ad61238396888c0d8a5298087682b68`.

## Proven scope and assumptions

DistributedCausalBroadcast formalizes fixed-group causal multicast with authentic
immutable messages and delivered-prefix vector counters. Broadcast atomically
self-delivers; Arrive only buffers; Deliver requires the next sender sequence
and every cross-sender dependency. Induction over operational transitions proves
continuous prefixes, at-most-once application delivery, exact reflexive causal-past
timestamps and causal delivery safety: if m1 precedes m2 and m2 is delivered at t,
m1 was delivered at a strictly earlier step. Independent message causality is
linked to actual delivery-before-broadcast events, not defined by vector comparison.

Eventual delivery requires reliable network arrival and per-message weak fairness.
It follows by induction on finite causal pasts; readiness is derived rather than
assumed. Reordered and duplicate network arrivals are allowed. Regressions cover
three-process relay, independent broadcasts, immediate self-delivery, a one-node
group, and counterexamples to weakened cross-sender or next-sequence guards.
Buffered arrival alone does not create an application causal dependency.

Causal order does not imply total order or physical simultaneity. Crashes, restarts,
Byzantine messages, dynamic membership, bounded-machine counter overflow, vector
compression and physical delays are outside this model. Mathematical natural
numbers themselves do not overflow. The full ISIS membership and virtual-synchrony
protocol is not claimed. Python correctness, JSON/SHA-256 correctness and the
SimLab-to-Lean correspondence remain open obligations.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 131 |
| Lean files under Verification/ | 171 top-level + 2 auxiliary = 173 |
| Root-inclusive sources identical to the private snapshot | 174 |
| Clean strict build | 3622 jobs; no warnings |
| Complete verifier audit | 15608 declarations; no violations |
| Pinned independent full audit | 15608 declarations; no violations |
| Public live tests | 76; no failures or skips; 272.330s |

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

All 174 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.29. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedCausalBroadcast.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
