---
id: DistributedRaftLogAppend
language: en
section: distributed
source: Verification/DistributedRaftLogAppend.lean
source_sha256: 2c0570f8c65fc8f65b505d77c1c18bbea5fda3e4a628caf5f4f0de9dac145449
novelty: not-assessed
---

# DistributedRaftLogAppend

[Section](../distributed/README.md) · [Lean source](../../Verification/DistributedRaftLogAppend.lean)

## Verified result

Local append preserves existing entries and places the new entry at the old length. Equal-length matching logs still match after identical append. Monotone terms remain monotone if the new term bounds every old term; a second theorem derives this from a last-entry bound. The last-entry condition is vacuous for an empty log.

## Assumptions and scope

Quorum intersection alone does not establish Leader Completeness. No full message-passing, failure, or distributed RPC model is proved correct.

LogEntry reuses the existing Raft entry type. Its index field is not proved equal to its list position. LogsMatchUpTo compares optional entries; the append theorem restricts the comparison to the actual equal lengths. AppendEntries RPC and distributed preservation of Log Matching are not modeled.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`append_length`](../../Verification/DistributedRaftLogAppend.lean#L18)
- [`get_append_old`](../../Verification/DistributedRaftLogAppend.lean#L22)
- [`get_append_last`](../../Verification/DistributedRaftLogAppend.lean#L26)
- [`logs_match_preserved_on_append`](../../Verification/DistributedRaftLogAppend.lean#L30)
- [`append_preserves_monotonicity`](../../Verification/DistributedRaftLogAppend.lean#L47)
- [`append_preserves_monotonicity_of_last`](../../Verification/DistributedRaftLogAppend.lean#L75)
- [`distributed_raft_log_append_master_verification_suite`](../../Verification/DistributedRaftLogAppend.lean#L108)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
