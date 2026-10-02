---
id: DistributedRaftLogReplication
language: en
section: distributed
source: Verification/DistributedRaftLogReplication.lean
source_sha256: 4ba9d4701f459629c616cc990a87e537eea85aa9c3e8735654349135acbf30d7
novelty: not-assessed
status: reviewed
---

# DistributedRaftLogReplication

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftLogReplication.lean)

## Verified result

Matching index and term yield equal entries provided command equality is assumed through h_leader. logsMatchUpTo is reflexive. Appending an entry preserves the old list as a prefix, and prefixes preserve every old position. If two logs have sufficient length and equal entries at all positions below commitIndex, applyEntries returns equal command lists.

## Assumptions and limitations

The command-uniqueness implication is a premise, not derived from leader behavior. No theorem derives prefix agreement from matching one entry. logsMatchUpTo compares only shared valid positions and can be vacuous for an empty log. Entry index fields are not constrained to equal list positions or form a contiguous sequence. commitIndex in applyEntries is a count/exclusive bound, while logsMatchUpTo uses an inclusive bound. applyEntries maps a prefix to command numbers; it does not execute an arbitrary state transition function or prove agreement becomes true during network execution.

These list properties overlap the earlier DistributedRaftLogAppend component, which remains intact. RequestVote, joint consensus, conflicting suffix rollback, snapshots, message delivery, crash recovery and inductive Raft safety are not modeled here. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedRaftLogReplication.distributed_raft_master_verification_suite`.
