---
id: DistributedRaftLogOrder
language: en
section: distributed
source: Verification/DistributedRaftLogOrder.lean
source_sha256: ee3b4b761134c924ea97cc91c4b5a93bf95c48f028361fd61a0bf171b1089acc
novelty: not-assessed
status: reviewed
---

# DistributedRaftLogOrder

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftLogOrder.lean)

## Reachable log structure

The module derives log structure from the original operational `Step` and `Reachable`, without adding global conditions to the protocol guards. `Bounds` simultaneously tracks server entry-term bounds and bounds on entries carried by AppendEntries packets. A strengthened historical archive establishes positive, nondecreasing entry terms.

## Proved statements

- `reachable_log_bound`: every stored entry has term at most the server's current term.
- `reachable_candidate_strict`: a candidate's stored entries have terms strictly below its current term.
- `reachable_active_positive`: a non-follower has a positive current term.
- `reachable_wellFormed`: server logs have consecutive one-based indices, positive terms, unique indices, endpoint bounds, and index order compatible with strictly increasing terms.
- `wellFormed_lastIndex_eq_length`: the last index of a well-formed log is its length, including the empty-log sentinel case.
- `matching_transfers_prefix`: matching entries at the same index and term transfer any source prefix ending at or before that index to the candidate log. Both logs must be well formed and satisfy `LogMatching`.

## Boundaries

Term order is nondecreasing: multiple entries may share a term. Follower logs may lose conflicting suffixes, so log length is not globally monotone. The module proves structural ingredients, not committed-entry persistence or Leader Completeness by itself. It inherits a fixed nonempty cluster and the original model's absence of external RPC injection and crash/recovery.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
