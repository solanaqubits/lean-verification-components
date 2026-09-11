# Distributed consensus

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [BFTConsensusQuorum](BFTConsensusQuorum.en.md) | The intersection bound 2Q−N; honest intersection when N+f < 2Q; quorum availability when Q+f ≤ N, including classical exact thresholds. |
| [DistributedRaftConsensus](DistributedRaftConsensus.en.md) | Nonempty majority intersection, candidate uniqueness under a shared vote function, and transitivity of nondecreasing terms. |
| [DistributedRaftLogAppend](../09_distributed_systems/DistributedRaftLogAppend.en.md) | Local append preserves existing entries and places the new entry at the old length. Equal-length matching logs still match after identical append. Monotone terms remain monotone if the new term bounds every old term; a second theorem derives this from a last-entry bound. The last-entry condition is vacuous for an empty log. |

## Scope

Quorum intersection alone does not establish Leader Completeness. No full message-passing, failure, or distributed RPC model is proved correct.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)
