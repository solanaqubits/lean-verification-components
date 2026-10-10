---
id: DistributedCausalBroadcast
language: en
section: distributed
source: Verification/DistributedCausalBroadcast.lean
source_sha256: 70df1aaad822890c05b1de3e832b22cb2854cc1a79b62e0e87a23b97cc39c8cc
novelty: not-assessed
status: reviewed
---

# Causal broadcast with delivered-prefix vector counters

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedCausalBroadcast.lean)

## Model and established results

A fixed group uses NodeId = Fin n; the intended deployment has n >= 1.
The theorems also hold vacuously for an empty node type. A message identifier
contains a sender and a natural sequence number. Positivity and unique numbering
are proved for issued messages; the ambient identifier type also contains zero.
A message carries immutable vector timestamps. Each process stores delivered
prefix counters, a finite buffer, and a ghost application-delivery log.

Broadcast increments only the broadcaster's own counter, snapshots the resulting
vector and atomically self-delivers. Arrive authenticates against the sent-message
archive and inserts into the buffer without changing delivered counters. Deliver
requires buffer membership, the next sender sequence number, and satisfaction
of every other coordinate dependency. It increments the sender coordinate and
erases the packet. Reordered and repeated network arrivals are permitted.
Already delivered duplicate packets may remain buffered but cannot be redelivered.
The archive models authentic immutable sends; no transport FIFO order is assumed.
Idle steps allow finite completed schedules to extend to infinite executions.

Causality is independent of vector comparison. On broadcast, ghost parents record
exactly the application's earlier delivery log at the sender. MsgHappensBefore
is the strict transitive closure of these edges. The event-trace bridge proves
that they are precisely actual delivery-before-broadcast edges. Earlier broadcasts
by the same sender are included through atomic self-delivery; sender_sequence_causal
proves the local numbering order is causal. Later broadcasts cannot change the
causal past of an already issued message.

Induction over the three operational transitions (and idle) establishes:
- delivered logs are duplicate-free continuous sender prefixes;
- buffers contain authentic messages and identifiers determine unique archive records;
- delivered sets and stored parent sets are causally closed;
- parent edges have strictly increasing broadcast ranks;
- the reflexive causal past is exactly the prefix set described by the timestamp.

No causal safety condition is a delivery guard or assumed execution invariant.
The theorem timestamp_causal_past_exact counts sender messages in the reflexive
past, including the current message itself at its sender coordinate.
causal_delivery_safety gives the strict global-step conclusion: if a precedes b
and b is delivered at t, a was delivered at some u < t. A strengthened version
allows causality to be evaluated in a later execution prefix. Two delivery steps
for the same process and message must have the same step index.

The operational counter rules differ from all-event clocks in module 129:
receiving does not increment the receiver's own coordinate. tick_bridge reuses
the earlier coordinate tick; ready_merge_bridge proves that, when Ready holds,
merging the timestamp equals ticking the sender coordinate. There is no assertion
that multicast traces literally satisfy the earlier one-recipient message model.

## Conditional liveness

ReliableArrival says every issued packet eventually reaches each process's buffer
unless it is already application-delivered, including atomic self-delivery.
WeakFairness is per message: a packet continuously buffered and ready must
get a delivery step. Scheduling the process alone is not this fairness condition.
Neither eventual readiness nor eventual application delivery is assumed.

Strong induction on the cardinality of the strict causal past proves eventual
delivery of every issued message. Parent sets are finite at broadcast time;
new broadcasts need not cease. Buffer persistence and eventual delivery of all
predecessors establish continuous readiness in a hypothetical starvation execution,
contradicting weak fairness. No bounded delivery-time claim is made.

## Executable regressions and boundaries

Kernel-checked schedules cover reversed network arrivals, a three-process relay,
independent broadcasts delivered in opposite orders, immediate self-delivery,
a one-process group and repeated network arrivals. Counterexamples start from
reachable correct configurations and execute one weakened delivery: omitting the
cross-sender check loses causal order; accepting a sender sequence gap loses
both prefix integrity and causal order. External live regressions additionally
check that mere network arrival does not influence a later application's broadcast.

Causal order does not imply total order, application-operation commutativity or
physical simultaneity. Node crashes, restarts, Byzantine messages, changing group
membership, bounded-machine counter overflow, clock compression and physical
latencies are outside this fixed-group model. Naturals themselves do not overflow.
Python correctness, JSON/SHA-256 correctness and SimLab-to-Lean correspondence
remain open. Novelty is not assessed. The model isolates the failure-free fixed-group
causal-delivery core; the full ISIS virtual-synchrony and membership protocol is
not claimed.

Reference: [Birman, Schiper and Stephenson, Lightweight Causal and Atomic Group Multicast (1991)](https://ntrs.nasa.gov/api/citations/19910009352/downloads/19910009352.pdf).

## Validation

Base private snapshot: 629e2ceb6441538c0abdf75331db6e1be6f2bcd7.
All required project and export checks passed; measured results follow.

## Private snapshot validation: causal broadcast

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 131 |
| Lean sources | 173 under Verification/; 174 including root |
| Strict clean private build | 3622 jobs; no warnings |
| Both full axiom audits | 15608 declarations; no violations |
| Private live tests | 79; no failures or skips; 268.34s |
| Export live tests | 76; no failures or skips; 275.769s |
| Strict clean export build | 3622 jobs; no warnings |

Module verify and audit each covered 807 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent audit source commit is 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256 is 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. A second independent proof kernel is not claimed.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. All 174 exported Lean files match;
repeated exports agree. Integration is idempotent. The original HEAD and 406 tracked
files outside simulations/ are preserved. No task writes to simulations/; this earlier private check did not publish a public release.


## Source theorem links

- [reachable_invariant](../../Verification/DistributedCausalBroadcast.lean#L519)
- [prefix_integrity_invariant](../../Verification/DistributedCausalBroadcast.lean#L525)
- [no_duplicate_delivery](../../Verification/DistributedCausalBroadcast.lean#L529)
- [timestamp_causal_past_exact](../../Verification/DistributedCausalBroadcast.lean#L609)
- [causal_delivery_safety](../../Verification/DistributedCausalBroadcast.lean#L736)
- [causal_delivery_safety_extended](../../Verification/DistributedCausalBroadcast.lean#L922)
- [parent_event_trace_bridge](../../Verification/DistributedCausalBroadcast.lean#L1110)
- [liveness_under_fairness](../../Verification/DistributedCausalBroadcast.lean#L873)
- [counterexample_missing_cross_check](../../Verification/DistributedCausalBroadcast.lean#L1052)
- [counterexample_skip_sequence](../../Verification/DistributedCausalBroadcast.lean#L1065)
- [distributed_causal_broadcast_master_suite](../../Verification/DistributedCausalBroadcast.lean#L1155)

## Public release validation

The [v0.5.29 report](../../docs/release-v0.5.29.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 131 |
| Lean files under Verification/ | 171 top-level + 2 auxiliary = 173 |
| Root-inclusive sources identical to the private snapshot | 174 |
| Clean strict build | 3622 jobs; no warnings |
| Complete verifier audit | 15608 declarations; no violations |
| Pinned independent full audit | 15608 declarations; no violations |
| Public live tests | 76; no failures or skips; 272.330s |
