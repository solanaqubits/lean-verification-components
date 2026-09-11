---
id: DistributedRaftConsensus
language: en
section: distributed
source: Verification/DistributedRaftConsensus.lean
source_sha256: 89cf3887f090c80d0fbcc0058a1c1733ce524d906253a67a3489e081f6b045c2
novelty: not-assessed
---

# DistributedRaftConsensus

[Section](README.md) · [Lean source](../../Verification/DistributedRaftConsensus.lean)

## Verified result

Nonempty majority intersection, candidate uniqueness under a shared vote function, and transitivity of nondecreasing terms.

## Assumptions and scope

Quorum intersection alone does not establish Leader Completeness. No full message-passing, failure, or distributed RPC model is proved correct.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`majority_intersection_nonempty`](../../Verification/DistributedRaftConsensus.lean#L14)
- [`election_safety_unique_leader`](../../Verification/DistributedRaftConsensus.lean#L23)
- [`leader_commit_quorum_overlap`](../../Verification/DistributedRaftConsensus.lean#L34)
- [`distributed_raft_master_verification_suite`](../../Verification/DistributedRaftConsensus.lean#L77)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
