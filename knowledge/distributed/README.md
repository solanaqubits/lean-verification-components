# Distributed consensus

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [BFTConsensusQuorum](BFTConsensusQuorum.en.md) | The intersection bound 2Q−N; honest intersection when N+f < 2Q; quorum availability when Q+f ≤ N, including classical exact thresholds. |
| [DistributedRaftConsensus](DistributedRaftConsensus.en.md) | Nonempty majority intersection, candidate uniqueness under a shared vote function, and transitivity of nondecreasing terms. |
| [DistributedRaftLogAppend](../09_distributed_systems/DistributedRaftLogAppend.en.md) | Local append preserves existing entries and places the new entry at the old length. Equal-length matching logs still match after identical append. Monotone terms remain monotone if the new term bounds every old term; a second theorem derives this from a last-entry bound. The last-entry condition is vacuous for an empty log. |

## Scope

The operational machine establishes election safety; NetworkInduction establishes reachable-state global Log Matching. Quorum intersection alone does not establish Leader Completeness. The separate CompleteBridge develops operational committed-prefix preservation using events from one execution, rather than literally instantiating the abstract `VoterEvolution`. Its own card records the final verification status. Crash recovery and dynamic membership remain outside the model.

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

- [DistributedRaftStateMachine](../09_distributed_systems/DistributedRaftStateMachine.md): reachable-state election safety, historical single voting, and conditional local Log Matching lemmas; the separate NetworkInduction module closes global Log Matching; the separate CompleteBridge handles the operational completeness argument without literally instantiating abstract VoterEvolution.

- [DistributedRaftNetworkInduction](../09_distributed_systems/DistributedRaftNetworkInduction.md)

- [DistributedRaftNetworkHistory](../09_distributed_systems/DistributedRaftNetworkHistory.md)

- [DistributedRaftNetworkLogLemmas](../09_distributed_systems/DistributedRaftNetworkLogLemmas.md)

- [DistributedRaftTraceMatching](../09_distributed_systems/DistributedRaftTraceMatching.md)

- [DistributedRaftEventHistory](../09_distributed_systems/DistributedRaftEventHistory.md)

- [DistributedRaftLogOrder](../09_distributed_systems/DistributedRaftLogOrder.md)

- [DistributedRaftTraceOrigins](../09_distributed_systems/DistributedRaftTraceOrigins.md)

- [DistributedRaftCommittedPrefixLemmas](../09_distributed_systems/DistributedRaftCommittedPrefixLemmas.md)

- [DistributedRaftCandidateHistory](../09_distributed_systems/DistributedRaftCandidateHistory.md)

- [DistributedRaftVoterRetention](../09_distributed_systems/DistributedRaftVoterRetention.md)

- [DistributedRaftCompleteBridge](../09_distributed_systems/DistributedRaftCompleteBridge.md)

- [DistributedMarzulloAlgorithm](../09_distributed_systems/DistributedMarzulloAlgorithm.md): exact-real threshold envelope, true-time inclusion under a fault budget, and a counterexample to maximum-overlap truth localization.

- [DistributedChandyLamportSnapshot](../09_distributed_systems/DistributedChandyLamportSnapshot.md): operational two-process FIFO snapshots, consistent saved cuts and exact completed channel contents.

[DistributedRaftCommitApplication](../09_distributed_systems/DistributedRaftCommitApplication.md)

[DistributedRaftCommitIndexInvariant](../09_distributed_systems/DistributedRaftCommitIndexInvariant.md)

[DistributedRaftCommitApplicationExample](../09_distributed_systems/DistributedRaftCommitApplicationExample.md)

- [DistributedTwoPhaseCommitTimeout](../09_distributed_systems/DistributedTwoPhaseCommitTimeout.md): operational two-participant timeout safety, indistinguishable prepared histories, and conditional finite-escape blocking.

- [DistributedThreePhaseCommitCore](../09_distributed_systems/DistributedThreePhaseCommitCore.md) — two-participant 3PC, operational transitions and conditional completion.

- [DistributedThreePhaseCommitCertificate](../09_distributed_systems/DistributedThreePhaseCommitCertificate.md) — two-participant 3PC, operational transitions and conditional completion.

- [DistributedThreePhaseCommit](../09_distributed_systems/DistributedThreePhaseCommit.md) — two-participant 3PC, operational transitions and conditional completion.

- [DistributedChandyMisraHaasDeadlock](../09_distributed_systems/DistributedChandyMisraHaasDeadlock.md) — static-epoch AND probes, soundness, fair delivery and dynamic counterexample.

-  — static-epoch AND wait-graph detector.
