---
id: DistributedRaftLeaderCompleteness
language: en
section: distributed
source: Verification/DistributedRaftLeaderCompleteness.lean
source_sha256: fc62d005b9ad27383c19258dd72ddea6a1b5066f9d3cf3c5230151ecedf337cd
novelty: not-assessed
status: reviewed
---

# DistributedRaftLeaderCompleteness

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftLeaderCompleteness.lean)

## Verified result

`leader_completeness` proves that under `HistoryValid H`, a directly committed entry e in term t belongs to the archived log of every elected leader in term u > t. The proof uses strong induction on natural-number terms, allowing terms with no leader. The committing term supplies the base case; intermediate leaders are handled by the induction hypothesis.

`Cluster` has a positive size, `NodeId` is `Fin size`, and quorums are finite sets satisfying `size < 2 * card`. `quorum_intersection` supplies an actual common server. `NodeState` records currentTerm, role and a list of entries (index, term, cmd). `logUpToDate` compares last term, then last index. Empty logs have zero endpoint labels.

`committedInTerm` requires e.term = t > 0, an elected leader, e in that leader's log, and e on every member of a majority quorum. Counting replicas of an older entry does not directly commit it. `Committed` also covers earlier prefix entries anchored by a directly committed current-term entry. `committed_prefix_leader_completeness` proves retention for those entries.

## Explicit history assumptions

`History` archives candidate, leader, voter and replication snapshots. A single canonical leader per term is supplied by elected, not derived from election transitions. `votedForCandidate` describes members of the winning candidate's quorum, not all voting traffic.

`HistoryValid` requires:

- well-formed logs: consecutive one-based indices, positive terms, unique indices, endpoint bounds, and term order consistent with index order;
- provenance of every entry from the archived leader of that entry's term;
- Log Matching between recorded logs: a common index and term transfers all preceding entries;
- append-only extension from candidate log to archived leader log;
- majority elections, Up-to-Date for every vote, candidate entries older than the election term, and consistent role/term labels;
- an inductive `VoterEvolution` witness between replication and subsequent voting snapshots.

`VoterEvolution` allows identity, suffix append, replacement by the whole archived log of a leader with term k in [t,u), and composition. It abstracts local histories; it does not implement partial AppendEntries. Existence of such histories and the term bounds on synchronization sources are premises.

`voter_preserves_committed_entry` is proved by induction over these histories using retention by earlier leaders. Retention of the target committed entry is not a field of `HistoryValid`. Equal last terms use provenance and Log Matching through their common origin leader. A strictly newer candidate last term uses an intermediate leader and strong induction. `up_to_date_alone_insufficient` exhibits lists with different commands at the same index, showing that Up-to-Date alone cannot imply prefix inclusion.

## State Machine Safety and consistency witness

`committed_entries_agree` equates committed entries with equal indices, including different commitment terms. `Applied` is a supplied application-event relation. `state_machine_safety` equates applied commands under the separate premise that every application event refers to a committed entry. Command execution and equality of entire machine states are not modeled.

`ExampleHistory.valid` constructively satisfies all obligations for a single server: command 7 is committed in term 1 and retained after reelection in term 2. Application events are also shown to refer to committed entries. This witnesses that the premises are consistent with nonempty commitment.

## Boundaries and reference

The module does not prove that a Raft implementation or a complete network transition system preserves `HistoryValid`. Asynchronous RPCs, partial conflicting AppendEntries, heartbeats/timeouts, crashes and recovery, durable storage, compaction, membership changes, Byzantine behavior and liveness are absent. State fields for roles and currentTerm do not constitute verified transition rules. Scientific novelty has not been assessed.

Reference: Ongaro and Ousterhout, [extended Raft paper, §5.4](https://raft.github.io/raft.pdf). This card describes the Lean model's actual premises, not a formalization of the entire paper.

[Validation](../VERIFICATION.en.md). Suite theorem: `raft_leader_completeness_master_suite`.
