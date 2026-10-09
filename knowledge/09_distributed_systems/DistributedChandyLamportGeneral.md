---
id: DistributedChandyLamportGeneral
language: en
section: distributed
source: Verification/DistributedChandyLamportGeneral.lean
source_sha256: 5d7064f4692c8bdffeb3150e4f760babebca41b4bc1a03e00ff6447fba48acff
novelty: not-assessed
status: reviewed
---

# Chandy–Lamport snapshots on finite directed networks

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedChandyLamportGeneral.lean)

## Operational model

Nodes are Fin n. Edge is a subtype of ordered node pairs carrying a proof of the
adjacency predicate. Only existing directed edges have channels; self-loops are
allowed. The theorems cover all finite n with an initiator, including the requested
n≥2 case. Arbitrary payload type M and abstract application data type D are used.
The old two-process module is imported and preserved; its channel proof pattern
is generalized to M in this namespace. No old definition or theorem is replaced.

A Node stores its current value, application-event count and optional localSnap
containing the captured value/count. started is derived from localSnap.isSome.
The recording flag on an incoming edge is derived as receiver.started && !closed.
recordedChan exposes the payload list; the channel also retains packet identities.
Snapshot state is not redundantly stored in conflicting boolean fields.

Packet IDs are channel-local send ordinals. Sender and receiver phase stamps
are ghost observations assigned by actual send/receive transitions. They never
control whether a received packet is accepted or recorded. Repeated equal payloads
remain different packets. Application transitions supply arbitrary next local
data, modeling nondeterministic application behavior without assuming its correctness.

The root can initiate once. Capturing the local state and appending one marker
to every outgoing channel is one atomic local action. First-marker handling does
the same at a previously unrecorded receiver and closes that incoming channel.
Other incoming channels keep recording. Later markers close their own channels.
Application sends append; application receives consume only the FIFO head.
An offer transition marks that head ready for its local reaction. Stuttering is allowed.
All channels start empty; arbitrary application traffic can occur before initiation.

## Kernel-checked contract

| Declaration | Result |
|---|---|
| reachable_invariant | Marker separation, ordered send/receive ledger, unique IDs, correct recording and no future sends are derived by transition induction. |
| consistent_cut_safety | Every pre-cut receipt has a matching pre-cut send. |
| channel_recording_soundness | A closed channel records exactly the ordered crossing receipts, equivalently pre-cut sends filtered to exclude pre-cut receipts. |
| send_event_precedes_cut / receive_event_precedes_cut | Phase-false at an application event is equivalent to its strict event index preceding the local false-to-true capture. |
| snapshot_single_assignment | Captured local data and event count are never overwritten. |
| closed_recording_preserved | Once a channel closes, its recorded list never changes. |
| first_marker_empty | The first-marker incoming channel is empty in the snapshot, derived from reachable history. |
| snapshot_conditional_termination | Under directed reachability and the stated delivery/fairness contracts, there is a finite T after which all nodes are captured and all channels closed. |
| non_fifo_anomaly_counterexample | A reachable relaxed execution with marker overtaking loses a crossing packet from the closed record. |
| reachability_assumption_necessary | A reliable, weakly fair execution with an unreachable node never completes globally. |

The recorded equality is an equality of lists, preserving FIFO order and multiplicity.
Before channel closure it describes crossing receipts seen so far; closure implies
that every pre-cut send has been received. The phase/event-index bridge uses an
actual capture transition; no numerical timestamp is supplied as a hidden safety premise.

## Environment contracts and termination

ReliableDelivery quantifies over every already queued item. At some finite later
index it is either recorded as processed, or offered at the FIFO head to its receiver.
This is an end-to-end eventual offering/processing contract for the modeled channel;
it includes progress past earlier queued packets. It is stronger than saying only
that a transport never drops bytes. It does not assert snapshot completion or
that any unsent marker is delivered.

WeakFairness concerns the continuously enabled root-initiation reaction and each
continuously enabled offered-head marker reaction. It requires a corresponding
false-to-true state transition. marker_enabled_step proves that an offered marker
remains enabled until it is processed. No assumption says all nodes eventually
capture, all channels close, or the final invariant already holds.

The proof first starts the root, then combines eventual offering with weak fairness
to close each channel from a captured sender. Directed path induction reaches every
node. Finiteness and monotonicity give one bound for all nodes and channels, after
which completion persists. Strong connectivity is unnecessary: reachability from
the initiator suffices. The proof gives existence of a finite bound, not a uniform
latency or message-processing complexity estimate.

An explicit two-node execution satisfies both contracts and completes. A disconnected
execution satisfies both but leaves a node unrecorded forever. The non-FIFO model
adds only an adjacent queue swap before offering; it loses or duplicates no packets.
A marker overtakes an older application packet, closes the incoming record, and the
packet arrives after the receiver's cut without being recorded. This demonstrates
failure of exact channel recording, not a claim that every reordering violates cut safety.

## Regression evidence and Clean Water

Regressions use a three-node directed graph, two incoming edges, two equal string
payloads with different IDs, first and later markers, exact FIFO recording, and
captured application values. An unreachable source leaves another node's incoming
channel recording. The relaxed anomaly is also proved unreachable in the FIFO model.

This is one snapshot in a fixed topology with unbounded FIFO queues and atomic
capture/broadcast reactions. Collecting the distributed records at a coordinator and
detecting global completion are not modeled. Reordering an entire application trace
to realize the captured global state (permutation/causal equivalence) is not proved.
Crash-stop or crash-recovery, channel loss, Byzantine behavior, changing membership
or topology, overlapping snapshots, bounded buffers and implementation correctness
are outside scope. Python, JSON/SHA-256 and SimLab linkage remain open obligations.
Scientific novelty is not assessed.

[Chandy and Lamport (1985)](https://lamport.azurewebsites.net/pubs/chandy.pdf).
[Commands and source hashes](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `0c7104839e071108f4f9d08d6a75c4799f6d2581`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 124 |
| Lean files under Verification/ | 164 top-level + 2 support = 166 |
| Root-inclusive byte-identical export | 167 sources |
| Clean strict private build | 3615 jobs; no warnings |
| Both full axiom audits | 14271 declarations; no violations |
| Private live tests | 72; no failures or skips; 253.046s |
| Export live tests | 69; no failures or skips; 269.251s |
| Export clean strict build | 3615 jobs; no warnings |

Module verify and audit each covered 828 declarations in the imported project closure,
including the original two-process snapshot module. Both full audits permit only
propext, Classical.choice and Quot.sound. Independent auditor source is pinned to
46024e005996495c65ef609368e11ab39c4222e3; executable SHA-256:
8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. The registry hook passed additionally;
no second independent proof kernel is asserted. Counts include generated declarations.
Both project build directories started empty, with isolated caches of pinned dependencies.
Integration is idempotent. Prior subject proof sources are unchanged. Original
workspace HEAD and 406 tracked files outside simulations/ are preserved. This task
makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.22 report](../../docs/release-v0.5.22.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 124 |
| Lean files under Verification/ | 164 top-level + 2 auxiliary = 166 |
| Root-inclusive sources identical to the private snapshot | 167 |
| Clean strict build | 3615 jobs; no warnings |
| Complete verifier audit | 14271 declarations; no violations |
| Pinned independent full audit | 14271 declarations; no violations |
| Public live tests | 69; no failures or skips; 260.408s |
