---
id: DistributedChandyLamportSnapshot
language: en
section: distributed
source: Verification/DistributedChandyLamportSnapshot.lean
source_sha256: 7db4e83d0a10a51665e09d8c7283d7df011a3ca0827611c2a80286a68c9449d2
novelty: not-assessed
status: reviewed
---

# DistributedChandyLamportSnapshot

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedChandyLamportSnapshot.lean)

## Operational model

Two processes have one FIFO channel in each direction. An application send appends to the queue; a receive removes only the head. Local application state is a natural-number accumulator (payloads are added on receipt), with an application-event counter. Snapshot initiation stores the local state, counter and ghost send/receive histories, and appends an outgoing marker atomically before any subsequent application send. The first marker records the receiver and sends its outgoing marker; a marker at an already recorded receiver closes incoming recording. Mirroring supplies the symmetric operations for the other process.

There is one snapshot instance. Each process emits one marker; “later marker” means a marker at a process that already recorded, not network duplication. In this topology a process has only one incoming channel, so there are no other incoming channels to activate on its first marker.

`recording receiver channel` is derived as `receiver.started && !channel.closed`, rather than stored redundantly. Receive actions append to transit according to these local flags. First-marker processing retains an already empty transit list; `first_marker_empty` derives that emptiness from reachability. The application message does not need to satisfy a proved invariant to be received: `Step` checks the FIFO head only.

Packet metadata contains a channel-local send ordinal and a ghost observation of the sender's snapshot phase. Receipts have a corresponding ghost observation of the receiver's phase. These stamps are assigned by the send/receive rules; receiving never branches on the sender stamp. Equal payloads can occur repeatedly without conflating their identities. Histories and phase metadata support the proof; this is not a wire-format or memory-efficiency claim.

## Derived guarantees

`reachable_invariant` proves the channel ledger equation (sent = received packets ++ queued application packets), consecutive unique send IDs, marker separation, recording correctness, and exclusion of receives from future sends. The inductive `WirePhase` explicitly separates old application packets, the queued marker, and new application packets. It is an invariant proved from `initState` and `Step`, not a transition premise.

`reachable_saved_cuts` connects ghost phases to the actual lists stored in each local snapshot. `snapshots_preserved` proves that recorded values, counters and lists are not overwritten by subsequent steps. `fifo_marker_ordering` exposes the two queue invariants. `no_future_messages_in_snapshot` shows that a post-snapshot packet at the delivery head requires an already recorded receiver; the reverse direction follows by `reachable_mirror`.

`chandy_lamport_cut_consistency` proves that every receive in either saved local cut has its matching send in the other saved cut. This is the no-orphan-message formulation of consistency for these captured local prefixes. It is not a separately defined arbitrary-event happens-before graph or a theorem about all possible application automata.

`transit_channel_soundness` requires that this channel's marker has been received and both local snapshots are available. The recorded ordered packet list equals the sender's saved sends filtered to exclude the receiver's saved receives. FIFO provenance and unique IDs justify exact order and multiplicity, including equal payloads. Closed channels contain no remaining pre-snapshot packets. `transit_partial_soundness` instead characterizes precisely the crossing receipts seen so far, without asserting completion. `closed_transit_preserved` freezes the recorded channel list after closure.

`ChandyLamportFormalSuite` and `chandy_lamport_master_suite` collect the reachable invariant, connection to stored cuts, no-future theorem, consistency, completed transit equality and symmetry. The suite extends DistributedSystemsFullSuite through MasterSuiteComponents; existing aggregate projections therefore include this new field. The historical hundred-import manifest is not recounted as a new hundred-module milestone.

## Regression evidence and boundaries

A kernel-checked nonempty execution includes two equal payloads with distinct IDs, traffic before and after markers, initiation at the receiver, both marker-handling branches, an incomplete transit prefix and a completed two-message channel. Another execution has a nonempty saved receive cut. A forged queue that lets a post-snapshot packet overtake the marker admits a head-receive step but is proved unreachable. These checks demonstrate that safety is not inserted as an operational guard.

Assumptions are two fixed processes, two unbounded lossless FIFO queues, atomic local snapshot/marker emission, and one snapshot instance. No losses, duplicated deliveries, crash/Byzantine behavior, recovery, topology changes, arbitrary n, overlapping snapshot instances, fairness, eventual completion, or distributed termination detection are modeled. Nor is reordering an entire application execution to reconstruct an intermediate global state proved. No production implementation or network runtime is certified. Simulations are neither imported nor modified. Novelty is not assessed.

[Chandy and Lamport (1985)](https://lamport.azurewebsites.net/pubs/chandy.pdf) supplies the original FIFO marker algorithm. This module formalizes the stated two-process safety specialization, not every result of that paper. Build and audit evidence is recorded in the [validation record](../VERIFICATION.en.md).

For public v0.5.3, the unused broad `Mathlib.Tactic` import was removed to satisfy the header linter on a fresh strict build. Definitions and proof bodies are unchanged from private source 520eef27466667237fff4d6ef7d9821e17f9fcfe.
