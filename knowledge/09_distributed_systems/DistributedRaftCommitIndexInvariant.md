---
id: DistributedRaftCommitIndexInvariant
language: en
section: distributed
source: Verification/DistributedRaftCommitIndexInvariant.lean
source_sha256: 20c95970a99250176a1a7c558317ebebc1fb1374d4f555a5f75db4ae09df5ae2
novelty: not-assessed
status: reviewed
---

# Chronological commit-index invariants

PrefixCertificate records an empty prefix or an earlier actual CommitEvent and a committing-term bound. CommitPacket carries such evidence for the prefix advertised by leaderCommit. execution_certified proves server and message invariants together from the original Step rules. execution_commitIndex_bound, execution_commitIndex_monotone, execution_commit_prefix_stable and execution_commit_provenance are derived consequences. committed_subprefix_preserved explicitly needs the recipient term at least the committing term; the main certificate induction supplies it. This does not modify RPC guards or assume the desired commitment invariant.

See the [application contract](DistributedRaftCommitApplication.md) and [validation](../../docs/raft-commit-application-verification.en.md). No liveness, runtime or physical implementation claim is made.
