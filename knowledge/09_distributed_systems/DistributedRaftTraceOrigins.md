---
id: DistributedRaftTraceOrigins
language: en
section: distributed
source: Verification/DistributedRaftTraceOrigins.lean
source_sha256: 974d4e4bf074ce99dce5ea26e867dd3eca928f2be65348204e59eddbf3c7c25e
novelty: not-assessed
status: reviewed
---

# DistributedRaftTraceOrigins

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftTraceOrigins.lean)

## Entry creation within one execution

`TraceGenerated` records an actual client append event on a supplied finite `Execution`: an earlier state has a leader, the entry has index equal to that leader's previous log length plus one and its current term, and the next state is exactly `leaderAppend`.

## Proved statements

- `trace_generated`: every entry stored at time `k ≤ run.length` has such a creation event strictly before `k` in the same execution.
- `trace_record_origin`: there is a time `j ≤ k` and a leader of the entry's own term whose log at `j` contains the entry.

The proof follows delayed partial AppendEntries batches through `AppendWitness` source snapshots and uses strong induction on time. Existing and incoming entries are distinguished by the actual conflict-sensitive merge. The origin is not an unrelated existentially reachable state.

## Boundaries

An origin snapshot is historical; it need not describe the node's current role or log. Creation does not imply commitment, and this module does not establish that the entry survives all future transitions. The finite execution starts from `initState` and consists exclusively of the original operational steps; no fairness, external message injection, crash recovery, or dynamic membership is added.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
