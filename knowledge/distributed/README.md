# Distributed consensus

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [BFTConsensusQuorum](BFTConsensusQuorum.en.md) | The intersection bound 2Q−N; honest intersection when N+f < 2Q; quorum availability when Q+f ≤ N, including classical exact thresholds. |
| [DistributedRaftConsensus](DistributedRaftConsensus.en.md) | Nonempty majority intersection, candidate uniqueness under a shared vote function, and transitivity of nondecreasing terms. |
| [DistributedRaftLogAppend](../09_distributed_systems/DistributedRaftLogAppend.en.md) | Local append preserves existing entries and places the new entry at the old length. Equal-length matching logs still match after identical append. Monotone terms remain monotone if the new term bounds every old term; a second theorem derives this from a last-entry bound. The last-entry condition is vacuous for an empty log. |

## Scope

Quorum intersection alone does not establish Leader Completeness. The operational Raft model proves election safety for reachable message-passing states. Leader Completeness remains conditional on log-history assumptions; global reachable-state Log Matching and the VoterEvolution bridge are not yet proved. No complete production Raft implementation or crash/recovery model is certified.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)

- [DistributedVectorClocks](../09_distributed_systems/DistributedVectorClocks.en.md): two-counter order, ticks, least-upper-bound merge and incomparability.

- [DistributedTwoPhaseCommit](../09_distributed_systems/DistributedTwoPhaseCommit.en.md)

- [DistributedPaxosConsensus](../09_distributed_systems/DistributedPaxosConsensus.en.md)

- [DistributedBullyElection](../09_distributed_systems/DistributedBullyElection.en.md)

- [DistributedLamportClocks](../09_distributed_systems/DistributedLamportClocks.en.md)

- [DistributedRaftLogReplication](../09_distributed_systems/DistributedRaftLogReplication.en.md)

- [DistributedPBFTConsensus](../09_distributed_systems/DistributedPBFTConsensus.en.md)

- [DistributedPaxos](../09_distributed_systems/DistributedPaxos.en.md)

- [DistributedRaftLeaderCompleteness](../09_distributed_systems/DistributedRaftLeaderCompleteness.md): conditional strong-induction proof over archived logs, explicit provenance/Log Matching and admissible voter histories; committed-prefix and application safety.

- [DistributedRaftStateMachine](../09_distributed_systems/DistributedRaftStateMachine.md): reachable-state election safety, historical single voting, and conditional local Log Matching lemmas; the global log-history bridge remains open.
