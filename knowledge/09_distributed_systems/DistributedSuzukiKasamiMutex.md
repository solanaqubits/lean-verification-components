---
id: DistributedSuzukiKasamiMutex
language: en
section: distributed
source: Verification/DistributedSuzukiKasamiMutex.lean
source_sha256: e8b467090c753c4594eb5c061c248748b605ff26d4f1ccb31839cd2b088c335f
novelty: not-assessed
status: reviewed
---

# Suzuki–Kasami token mutual exclusion

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedSuzukiKasamiMutex.lean)

## Operational contract

Nodes are Fin n with fixed membership and one designated initial owner. The requested
n≥2 setting is covered; the theorems also cover n=1. There is no initial owner at n=0.
Processes serialize their invocations, do not crash, and use unbounded natural counters.
Modes are idle, requesting and inCS. Cancellation and counter reset are absent.

State contains local RN rows, a finite set of token owners, an optional in-flight
token destination, a token payload (LN and queue), and sent/received REQUEST histories.
The payload is a coordinate of the global semantics, not shared runtime memory.
localToken exposes it only at a holder. Its value is unchanged during transit,
as proved by in_flight_payload_stability. States can syntactically have zero or
multiple owners; conservation is derived from reachability, not encoded as a guard.
The transport has one token-message slot. No token duplication or loss step is modeled.

A REQUEST records sender, sequence and recipient. Pending requests are sent history
minus received history. Receipt requires a genuine pending message and updates RN by
max. Channels are unordered and exact-once; reordered and delayed requests are allowed.
A nonholder creates one new sequence and atomically enqueues fanout to all other nodes.
Deliveries remain separate. A holder can request locally without a new sequence or
broadcast. Only the token holder can enter CS; leaving updates its own LN entry.

The queue is an ordinary list: Nodup is proved for the append/filter and tail
operations, rather than assumed as a constructor field. Release appends outstanding
locally known requests in increasing node-ID order, preserving existing FIFO order.
An idle holder also appends locally known outstanding requests on REQUEST receipt.
Token sending then removes the queue head and moves ownership to the channel;
delivery moves it from the channel to the addressed node.

This model separates the original immediate idle-holder handoff into queue reservation
and a separately scheduled send. New local entry cannot overtake a reserved handoff:
requesting at a holder requires an empty queue. An already requesting holder finishes
its own entry/exit before handing off. The proof concerns this specified serialization;
no mechanized refinement theorem to the original program is claimed. The payload and
queue are read only by the holder's local actions, never by a remote scheduling guard.

## Safety and corrected counter statements

reachable_safety is an induction over Execution. token_uniqueness_invariant proves
owners.card + flight.toList.length = 1. mutual_exclusion_safety uses the derived
fact that every inCS node is an owner. Neither theorem assumes fairness.

reachable_counters proves RN_i[j]≤RN_j[j] and LN[j]≤RN_j[j]≤LN[j]+1; an idle sender
has RN_j[j]=LN[j]. sequence_number_monotonicity proves nondecreasing RN and LN along
valid steps. Sent request numbers have their origin at the corresponding sender.
New nonholder requests strictly increment their sequence; retained-token invocations
do not. LN records a network request sequence, not a count of all CS invocations.

The proposed LN[j]≤RN_holder[j] is false. holder_rn_can_lag_ln supplies a reachable
three-node trace: node 2 holds a token with LN[1]=1 while its RN_2[1]=0, because the
old broadcast to node 2 is still pending. The token carries newer service knowledge.
No synchronization of every RN row is silently imposed on token receipt.

reachable_routing proves that queue members are requesting, are not current holders
or the in-flight destination, and that a token in flight is addressed to a requesting
node. Pending nonholders have a fresh broadcast. reachable_ready proves completeness
of an idle holder's queue relative to its own RN row, not to global remote knowledge.

## Conditional progress

Run is an infinite sequence of enabled Steps beginning at initial, including idle.
ReliableDelivery requires eventual receipt of each enqueued REQUEST and eventual
execution of delivery for each in-flight token. Absence of loss alone is insufficient.
WeakFairness schedules every continuously enabled send or enter action. It does not
force a client to request. FiniteCS requires eventual leave for every inCS observation.
None of these contracts assumes that a requesting node is granted the token.

starvation_freedom_under_liveness proves that every Requesting observation eventually
reaches InCS under exactly these three contracts. Later client invocations are allowed.
queued_eventually_token first proves service for a queued node: appending cannot move
it backwards, and sending an earlier queue head strictly decreases its index. An
infinite descending sequence is impossible. Reliable broadcast, finite membership
and local queue completeness then ensure that a persistently waiting request reaches
the queue. Retained-token local requests can enter directly and need not join the queue.

This is FIFO after insertion, not global first-come-first-served ordering of requests.
The theorem gives eventual service on infinite runs, not just existence of a favorable
finite continuation. No numerical wall-clock or message-complexity bound is proved.
withheldRun contains a real request and then idles forever: it never enters and
violates ReliableDelivery. It is not a counterexample under the progress contracts.

## Regressions and boundaries

Kernel-checked regressions exercise competing requests, FIFO handoff, token transit,
two completions, delayed old requests, out-of-order sequence delivery, duplicate and
fabricated receive rejection, repeated requests, retained-token reentry and deferral
while in CS. Generic tests retain arbitrary n and all liveness assumptions. The stale
RN holder and unfair withheld-delivery execution are explicit formal counterexamples.

Crashes, crash-recovery, token regeneration, partitions, Byzantine behavior, dynamic
membership, finite counter overflow, real-time bounds, network implementation and
application code inside CS are outside scope. Python, JSON/SHA-256 and external SimLab
input-to-byte binding remain open obligations. No scientific-priority claim is made.

Primary reference: I. Suzuki and T. Kasami, *A Distributed Mutual Exclusion Algorithm*,
ACM TOCS 3(4), 1985, 344–349, [DOI](https://doi.org/10.1145/6110.214406).
The operational model and the differences described above are authoritative for this
formalization, rather than an assertion of full implementation equivalence.

## Verification

The source hash identifies this card's proof snapshot. Full measured verification,
including audits and live regression counts, is recorded in
[the validation record](../VERIFICATION.en.md) and
[validation_snapshot.json](../../tools/validation_snapshot.json).

## Historical private implementation and export validation

Base private snapshot: `110558af4e7411ac48d75c1a6fc9795db6c2fde1`.

| Check | Result |
|---|---:|
| Direct subject imports | 118 |
| Lean files under Verification/ | 158 top-level + 2 support = 160 |
| Root-inclusive byte-identical export | 161 sources |
| Clean strict private build | 3543 jobs; no warnings |
| Both full axiom audits | 12794 declarations; no violations |
| Private live tests | 66; no failures or skips; 241.601s |
| Export live tests | 63; no failures or skips; 254.589s |
| Export clean strict build | 3543 jobs; no warnings |

Module verify and audit each checked 434 declarations. Both complete audits allow
only propext, Classical.choice and Quot.sound; the independent auditor is pinned at
46024e005996495c65ef609368e11ab39c4222e3. The strict AxiomAudit registry hook also passed.
Declaration counts include generated definitions; this is not a second proof kernel.
Project build directories were empty; isolated pinned dependency caches were reused.
Integration is idempotent. All earlier subject Lean files are unchanged. The original
workspace HEAD and 406 tracked files were preserved, with no task writes to simulations/.
That implementation task made no public release. Fresh public measurements appear in the [v0.5.16 report](../../docs/release-v0.5.16.en.md).
