# Release v0.5.19: Raymond tree mutual exclusion

Private proof snapshot: `d4a72dfb113fbdb5f4a4157db0f9f824ff5ffb48`.
Previous public main: `f8e4f82bc37faf855699264cb3e3deef2cf39edd`.

## Proven scope and assumptions

The model uses a fixed finite connected acyclic graph, one initial token owner,
empty queues/channels, and serialized local ASSIGN_PRIVILEGE / MAKE_REQUEST handlers.
The network permits reordering; receipt is exact-once and rejects fabricated messages.
Occurrence serials identify REQUEST packets, not protocol priorities. No mechanical
refinement to an implementation or the original pseudocode is asserted.

Reachable-state proofs establish exactly one privilege token across nodes and transit,
mutual exclusion (each inCS node is an actual owner), and duplicate-free FIFO queues.
Queue uniqueness is derived from request accounting, not imposed by a constructor.

Effective holder paths end at the current owner or the destination of an in-flight
PRIVILEGE. A reachable two-node counterexample has holder(0)=1 and holder(1)=0 while
the token travels from 0 to 1. Thus raw holder pointers need not be globally acyclic;
the effective path stops at the packet destination and suppresses its outgoing edge.

Every requesting observation eventually reaches inCS under ReliableDelivery (eventual
receipt of every REQUEST and PRIVILEGE), WeakFairness of local internal handlers and
FiniteCS (eventual exit). These contracts do not assume eventual service. Concurrent
later requests are allowed. The proof uses finite FIFO positions and the finite holder
path; it does not assert that distance to the token decreases under contention.

For isolated executions from quiescent initialization with only application client u,
at completed entry each message kind has exactly dist(u,initialOwner) sends: total
2*dist. Arbitrary legal delays and interleavings are allowed. Retained-token reentry
adds no traffic. This counts sends, not time or local steps. A chain can require
2*(n-1) messages; O(log n) is not a universal bound and no such bound is claimed under
arbitrary contention.

Node/link failures with token loss, token regeneration, dynamic topology/membership,
Byzantine behavior and real-time guarantees are outside scope. Python, JSON/SHA-256
and external SimLab input-to-byte binding remain open obligations. Scientific priority
has not been assessed.

## Independently measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 121 |
| Lean files under Verification/ | 161 top-level + 2 auxiliary = 163 |
| Root-inclusive sources identical to the private snapshot | 164 |
| Clean strict build | 3585 jobs; no warnings |
| Complete verifier audit | 13610 declarations; no violations |
| Pinned independent full audit | 13610 declarations; no violations |
| Public live tests | 66; no failures or skips; 253.584s |

The final public version was set to 0.5.19 before the recorded complete validation run.
A preparation assertion caught a stale 0.5.18 version field. The initial incomplete
build was stopped, its log retained separately, and validation restarted from an empty
project build directory. Only the complete corrected run supplies the metrics above.
Pinned dependency caches were copied into the isolated clone; this is not a source
rebuild of all Mathlib dependencies. Counts include generated declarations.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent full auditor is pinned to source commit
`46024e005996495c65ef609368e11ab39c4222e3`, executable SHA-256
`8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254`.
It runs through `lake env` with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
The project is pinned to Lean v4.33.1. The auditor source toolchain records v4.32.0-rc1;
the executable is pinned separately. The registry hook is an additional check,
not a second independent proof kernel.

Regressions cover retained-token reentry, duplicate/fabricated receive rejection,
serialized handlers, competing requests on a star, REQUEST overtaking PRIVILEGE,
completion of both clients, and a five-node chain with four messages of each kind.
Generic tests retain the actual tree, liveness and isolated-execution hypotheses.

Integration is idempotent. Repeated English exports agree byte-for-byte. All 164
Lean sources match the private commit. Earlier subject proofs and historical release
reports are preserved. The new card distinguishes historical private/export validation
from these public measurements. No Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

The annotated v0.5.19 tag is published by sequential pushes:
`git push origin main`, verify the remote commit, then `git push origin v0.5.19`.
This is not atomic. Existing tags are not overwritten. The final commit, tag object
and peeled SHA are checked against the remote and saved in the publication receipt.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are preserved.
This task makes no writes to simulations/; no global immutability claim is made about
concurrent external activity.

[Detailed contract](../knowledge/09_distributed_systems/DistributedRaymondTreeMutex.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
