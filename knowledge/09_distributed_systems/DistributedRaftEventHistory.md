---
id: DistributedRaftEventHistory
language: en
section: distributed
source: Verification/DistributedRaftEventHistory.lean
source_sha256: 5f4b973c83c1d90a35a98976cb354fc56e614713b48cd47ef681b15f53593a7a
novelty: not-assessed
status: reviewed
---

# DistributedRaftEventHistory

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftEventHistory.lean)

## Chronological evidence for RPC and election events

`Execution` gives a finite sequence beginning at `initState` whose adjacent states satisfy the original `Step`. `Execution.reachable` and `Execution.path` connect each bounded prefix to the existing operational semantics.

## Proved witnesses

- `network_witness`: queued RequestVote, AppendEntries, and positive AppendEntriesReply messages have matching events or source snapshots in this same execution.
- `RequestWitness` records the exact timeout and advertised candidate-log endpoint. `AppendWitness` records a leader snapshot and the contiguous batch cut from it.
- `AckWitness` records an actual successful AppendEntries delivery, its predecessor check, and acknowledged endpoint.
- `cast_witness` and `received_witness` identify the actual self-vote or granted-vote event behind each persistent ballot; a granted vote includes the `mayVote` guard and request provenance.
- `match_witness` ties each positive match counter used by a current leader to a historical successful-delivery acknowledgment in that leader's current term.
- `elections_witness` and `leader_election_witness` identify the actual candidate-to-leader majority-counting event.

## Boundaries

A match counter is historical evidence, not a claim that the follower still contains the acknowledged prefix at the current time. AppendEntries provenance refers to a historical sender snapshot rather than the sender's current log. Irrelevant packet variants satisfy the specific witness predicate trivially; no general cryptographic authentication theorem is asserted. The execution has static membership, no external packet injection, and no fairness or crash/recovery extension. These witnesses support a separate completeness argument.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
