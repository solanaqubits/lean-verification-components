# Release v0.5.16: Suzuki–Kasami mutual exclusion

Private proof snapshot: `ef9c48132533ccbf950462326a7282c335bf0777`.
Previous public main: `c74927aa6794a387d870600ca51ff34a03d8cef8`.

## Proven scope and assumptions

The fixed-membership, crash-free model uses Fin n, unbounded natural request
sequences and serialized client invocations. Reachability implies exactly one token,
counting both holders and the channel, mutual exclusion, and a duplicate-free queue.
The payload is a global semantic coordinate exposed only to the holder; it is
unchanged in transit. No runtime shared memory is assumed.

ReliableDelivery requires eventual delivery of actual REQUEST and token messages.
WeakFairness schedules continuously enabled send and enter actions. FiniteCS requires
every critical-section visit eventually to leave. Under these contracts, every
Requesting observation eventually reaches InCS, including runs with later requests.
Safety does not require fairness. No numerical waiting-time bound is proved.

The model separates immediate idle-holder handoff into queue reservation and a
separately scheduled send. New local requests cannot bypass an already reserved
handoff. This serialization is explicit; no mechanized refinement to the original
program is claimed. FIFO holds after queue insertion, not as global request order.
REQUEST fanout is atomically enqueued; individual deliveries are separate, unordered
and exact-once. Token transport uses one in-flight slot, without loss or duplication.

RN and LN are nondecreasing, with LN[j] ≤ RN_j[j] ≤ LN[j]+1 at the sender. The stronger
claim LN[j] ≤ RN_holder[j] is false: a reachable three-node trace leaves node 2 holding
a token with LN[1]=1 and RN_2[1]=0 before a delayed REQUEST arrives. Receiving the token
does not silently synchronize RN. Retained-token reentry does not increment the
network request number and need not join the queue. LN is not a count of every CS visit.

Crashes, lost-token recovery, dynamic membership, partitions, Byzantine behavior,
finite counter overflow, real-time bounds and network/application implementations
are outside scope. Python, JSON/SHA-256 and binding external SimLab inputs to bytes
remain open obligations. No scientific-priority claim is made.

## Public verification

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 118 |
| Lean files under Verification/ | 158 top-level + 2 support = 160 |
| Root-inclusive sources identical to the private snapshot | 161 |
| Clean strict build | 3543 jobs; no warnings |
| Complete verifier audit | 12794 declarations; no violations |
| Pinned independent audit | 12794 declarations; no violations |
| Public live tests | 63; no failures or skips; 251.324s |

The project build directory started empty. A further strict build passed after
finalizing version 0.5.16; proof sources remained unchanged throughout. Pinned dependency caches were copied
into the isolated clone; this is not a full source rebuild of Mathlib. Declaration
counts include generated definitions and constructors. Both complete audits allow
only propext, Classical.choice and Quot.sound. The registry hook and catalog passed.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The separate full auditor is leanprover-community/axiom-audit v0.1.2, pinned source
`46024e005996495c65ef609368e11ab39c4222e3`, executable SHA-256
`8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254`.
It is invoked through `lake env` with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
Project toolchain: leanprover/lean4:v4.33.1. The auditor source toolchain file records
v4.32.0-rc1; the executable is pinned separately and its successful audit is measured.
Neither audit constitutes another independent proof kernel.

Regressions check competing requests, FIFO handoff, token transit, two completions,
stale and out-of-order REQUESTs, rejection of fabricated/duplicate receipt,
retained-token reentry and CS deferral. Generic progress tests retain all contracts.
A run that withholds delivery forever is explicitly outside ReliableDelivery.

Integration is idempotent. Repeated exports agree in all 436 files, and every one of
161 proof sources matches the private commit. Certificate reproduction checks
7824 three-phase-commit states; the chip manifest reproduces 256 nodes. These Python
checks are reproducibility evidence, not formal verification of Python.
Previous release reports and prior subject proofs are preserved. No Russian cards
are exported. Historical private/export counts in the card are labeled separately.
Reservoir metadata are retained; external indexing is not asserted.

## Publication and preservation

The annotated v0.5.16 tag is published by two sequential pushes:
`git push origin main`, remote SHA verification, then `git push origin v0.5.16`.
This procedure is not atomic. Existing tags are not rewritten. Commit and tag object
IDs are recorded in the external publication receipt after creation and remote checks.

The original workspace HEAD and all 406 tracked files outside simulations/ are
preserved. This task does not write to simulations/; concurrent external activity
is not a claim of global directory immutability.

[Theorems and assumptions](../knowledge/09_distributed_systems/DistributedSuzukiKasamiMutex.md)
· [Source hashes and measured commands](../tools/validation_snapshot.json)
