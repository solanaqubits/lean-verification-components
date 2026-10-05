---
id: DistributedRaftCommitApplication
language: en
section: distributed
source: Verification/DistributedRaftCommitApplication.lean
source_sha256: 7d35377b5dc62edd6472db7ec9a659e00d02416a36c07f344e36c946f2a2af8b
novelty: not-assessed
status: reviewed
---

# DistributedRaftCommitApplication

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftCommitApplication.lean)

## Operational result

An application overlay interleaves network moves of an existing finite Raft Execution with local application moves. Network moves advance execution time without changing application state. An apply move reads exactly log[lastApplied], requires lastApplied < commitIndex and advances lastApplied by one while applying step : σ → ℕ → σ. It does not require a supplied safety or commitment witness. The initial application state has empty histories, zero indices and arbitrary s₀.

application_invariant derives lastApplied ≤ commitIndex ≤ log.length, applied history equal to the current log prefix, and value equal to the ordered List.foldl of its commands. application_replay connects incremental execution to applyCommitPrefix. Application history and indices only grow; no earlier log position is reapplied by this model. application_enabled proves local enabledness when a committed entry is pending, not eventual application or fairness.

The supporting CommitIndexInvariant module simultaneously proves server and queued-message certificates by induction over the actual network transitions. Positive commitIndex has an earlier real CommitEvent witness, including follower advancement through leaderCommit and partial batches. It is not defined as an arbitrary majority snapshot. Committed subprefixes are retained once the replica has reached the committing term; that term bound is derived for certificates. Existing operational Leader Completeness discharges later-source compatibility. below_commit_is_committed and applied_has_commit give an earlier commit event containing the entry at its actual position.

## Types, indices and conditional consistency

The operational Cluster, NodeId and LogEntry come from DistributedRaftLeaderCompleteness and are reused by DistributedRaftStateMachine. Commands are ℕ; no pre-existing abstract Command type is assumed. List positions are zero-based, while entry.index is one-based and commitIndex/lastApplied are prefix lengths. applyCommitPrefix folds log.take c; it is total for arbitrary lists, whereas the operational invariant establishes the needed bounds.

The older Consensus.LogEntry has only index and term. Its LogsMatchUpTo predicate cannot imply equality of executed commands: metadata_matching_insufficient proves a same-index/same-term counterexample with commands 7 and 9. state_machine_prefix_consistency therefore explicitly requires equality of FULL optional entries below c. The toConsensus adapter intentionally forgets commands; toReplication preserves all three fields for the separately declared legacy LogReplication entry. applyCommitPrefix_legacy identifies the fold with that module's applyEntries. No new LogEntry structure is introduced.

commit_prefix_take_monotonic and applyCommitPrefix_advance prove prefix growth and exact application of the newly added slice. They do not impose commutativity on step.

MajorityReplicatedAt uses a fixed Cluster and one immutable collection of logs. Intersecting quorums force the same term at the same position in that snapshot, without any leader-uniqueness hypothesis. This is not a cross-time commitment theorem. IsCommittedAt instead refers to an earlier actual current-term CommitEvent in the same execution.

## Counterexample and validation

DistributedRaftCommitApplicationExample executes 45 original Step transitions on five nodes, with legitimate elections in terms 1–4. A term-1 entry has an acknowledged majority under a term-3 leader, but fails the current-term commit guard. A subsequently elected term-4 leader replaces it with a differing command at a member of the earlier majority. Both endpoint commit indices remain zero. A hypothetical premature fold changes from 10 to 20. No illegal apply transition is inserted. This reproduces the mechanism of [Raft Figure 8](https://raft.github.io/raft.pdf), not its literal labels or a crash model.

Compiler regressions include a real positive commit, leaderCommit propagation, leader/follower application, early/duplicate/wrong-command rejection, noncommutative fold order, the metadata counterexample and the reachable old-term-majority trace. See the [verification report](../../docs/raft-commit-application-verification.en.md).

## Boundaries

This proves operational commitment provenance and local application correctness. The cross-node fold theorem retains full-prefix agreement as an explicit hypothesis; a new global State Machine Safety theorem is not claimed. The overlay consumes a fixed execution; application moves do not modify the underlying protocol. The fixed-cluster model includes loss, duplication and arbitrary message scheduling, but no timing, fairness, eventual delivery/application, dynamic membership, Byzantine injection, crash/recovery, disk fsync/WAL or deployed network implementation. No client exactly-once or external side-effect guarantee follows. Python, JSON/SHA-256, source authentication and SimLab byte binding remain separate obligations. Novelty is not assessed.
