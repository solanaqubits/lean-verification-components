---
id: DistributedRaftCompleteBridge
language: en
section: distributed
source: Verification/DistributedRaftCompleteBridge.lean
source_sha256: f7f149d890c8b09e481ff55acd7a36ebe3eb4a7d4d100f76257fa5afd7b4f35a
novelty: not-assessed
status: reviewed
---

# DistributedRaftCompleteBridge

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftCompleteBridge.lean)

## Result and commitment semantics

The module proves operational Leader Completeness for the fixed-cluster Raft model. `committedInTerm s e t` records a finite execution from `initState` to `s` containing an actual successful `Step.commit`. The committing leader has a majority replication quorum and a current-term entry at the committed index. Every entry in the committed prefix, including entries from older terms, is covered. The predicate does not assume that future leaders contain the entry.

`reachable_leader_completeness` concludes that any leader in a greater term contains the committed entry. For a fixed actual commit event in one execution, `committed_prefix_preserved` says that a node already containing the entire committed prefix at position `a` retains it at every `b` with `a ≤ b ≤ run.length`. The initial possession may precede the commit event. This does not assert that every replica contains the prefix or that replication eventually succeeds. These are safety statements for the original operational transitions; no extra Log Matching, Record Origin, VoterEvolution, or committed-entry preservation guard is added to `Step`.

## Proof structure

An indexed finite `Execution` keeps request, vote, AppendEntries, acknowledgement, election, and commit witnesses in the same run. A counted acknowledgement supplies a historical replica snapshot containing the committed prefix. A counted vote supplies a snapshot satisfying the actual Up-to-Date check against the candidate's campaign log. Term monotonicity orders these snapshots even when an old leader receives a delayed acknowledgement after a later election.

The replication and election majorities intersect. Strong induction on the new leader's term proves prefix retention up to the intersecting server's vote. Historical Log Matching, same-term leader uniqueness, and record origin then transfer the prefix to the candidate. Candidate logs remain fixed during a campaign; elected leaders retain their logs while their term stays unchanged.

Partial AppendEntries are handled by the original conflict-sensitive merge. A delayed short matching batch keeps the existing suffix. The auxiliary `ComparableSourcesAt` premise is discharged from operational history and the induction hypothesis; it is not an extra network transition condition.

The proof reuses the archive and historical strengthening of `reachable_global_log_matching`. Its support modules are [EventHistory](DistributedRaftEventHistory.md), [TraceMatching](DistributedRaftTraceMatching.md), [LogOrder](DistributedRaftLogOrder.md), [TraceOrigins](DistributedRaftTraceOrigins.md), [CommittedPrefixLemmas](DistributedRaftCommittedPrefixLemmas.md), [CandidateHistory](DistributedRaftCandidateHistory.md), and [VoterRetention](DistributedRaftVoterRetention.md).

## Boundaries

“Unconditional” means derived from reachability and an actual commit in this model, rather than assumed abstract history invariants. The model still assumes a fixed nonempty cluster and authenticated protocol-generated messages. Message loss, duplication, and arbitrary delivery order are included. Byzantine injection, dynamic membership, crash/recovery and stable storage, snapshots, timing, fairness, and liveness are not modeled.

The earlier abstract `VoterEvolution.synchronize` replaces a whole log. This module proves the operational conclusion directly for partial RPC batches; it does not claim a literal instantiation of that whole-log transition system. It does not certify a deployed Raft implementation or an application state machine. No novelty claim is made.

A concrete regression executes commitment in term 1 and election of a different leader in term 2, then applies the general theorem to that execution. [Validation](../VERIFICATION.en.md).
