---
id: DistributedRaftStateMachine
language: en
section: distributed
source: Verification/DistributedRaftStateMachine.lean
source_sha256: 9ad20662f35a4be873b876c18c98935a0e177d93ecaa1199a87f775ead059601
novelty: not-assessed
status: reviewed
---

# DistributedRaftStateMachine

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftStateMachine.lean)

## Operational model

A fixed nonempty cluster uses `NodeId = Fin C.size`, server states, an addressed queue of four RPC kinds, small steps `Step`, and inductive `Reachable` from empty logs. `Cluster`, `Role`, and `LogEntry` are reused from conditional Leader Completeness. Its `HistoryValid` is not an assumption of the election proofs.

Servers store currentTerm, votedFor, role, log, commitIndex, and matchIndex. Rules implement candidate timeouts, current-term voting with the Up-to-Date test, positive vote delivery, majority election, leader command append, AppendEntries transmission and handling, replication acknowledgement, and leader commit advancement. Direct commitment requires a current-term entry and a majority of acknowledgements. Negative replies, message loss, and duplication are permitted.

Observing a higher term and promoting a candidate are separate small steps. Observation increases the term, clears votedFor, and sets follower, leaving the RPC queued for a subsequent step. Delivery can select any queue position. Finite sets count distinct votes rather than packets. A current-term AppendEntries demotes a candidate even when the predecessor check fails.

The persistent `cast` and `elected` records are ghost proof history: actual vote grants and successful elections. `received` stores delivered votes for operational majority counting; elections select only the candidate's current term. The vote-grant rule does not consult `cast`; it checks currentTerm/votedFor/Up-to-Date. Positive-reply authenticity is proved from queue transitions. There is no external message injection.

## Invariants derived from transitions

- `term_step_monotone`: every step preserves or increases every server's term.
- `vote_history_reachable`, `single_vote_preserved`: all historical votes by a voter in one term name the same candidate. This is an event-history property, not merely uniqueness of an Option field.
- `transport_reachable`: positive queued replies and collected votes correspond to votes actually cast.
- `election_history_safety`: any two successful elections in one term select the same node, even at different historical times. The proof combines majority intersection with historical vote uniqueness.
- `election_safety`, `election_safety_step`: simultaneous leaders with equal terms are identical.
- `leader_append_only_step`: while a node remains leader in the same term, its old log is a prefix of its new log. This does not assert append-only behavior after demotion to follower.

## Exact boundary of the log results

`mergeSuffix` retains matching-term entries and preserves the remaining local suffix when the incoming batch ends. Only the first term conflict replaces the suffix. Heartbeats and short duplicate batches therefore do not truncate a valid longer suffix. `append_entries_preserves_predecessor` proves preservation of the prefix through the checked predecessor.

`LogMatching` is positional: equal entry terms at a shared position imply equal prefixes through that position. For consecutively indexed logs this is the usual (index, term) condition. `log_matching_step` preserves this relation with a third log under explicit input assumptions: equal prefixes through prev, agreement of aligned entries with equal terms, and Log Matching of both old/source logs with that third log. `log_matching_append` requires a fresh term at the appended position relative to the compared log.

**The global theorem `Reachable s → LogMatching` for all servers and RPC snapshots is not proved here.** The separate [DistributedRaftNetworkInduction](DistributedRaftNetworkInduction.md) now derives that global result and input compatibility from entry provenance and transmission history. These premises are not authorization guards in `Step`, and no output invariant is assumed to enable a transition. The package establishes operational election safety and local log lemmas, not the entire requested global Raft invariant set.

## Checked executions and remaining obligations

`Examples.committed_reachable` constructs a three-server execution: timeout, higher-term observation, second vote grant/delivery, majority election, appending command 7, replication, acknowledgement, and committing index 1. Additional kernel-checked examples exercise a duplicate reply without extra voting weight, rejection of another candidate, short-batch suffix retention, and conflicting-suffix replacement. Finite checks use `decide`, not native-decide.

This module alone does not prove preservation of committed entries or operational Leader Completeness; the separate [DistributedRaftCompleteBridge](DistributedRaftCompleteBridge.md) develops that argument from actual execution histories and records its own validation status. It does not literally instantiate the abstract `HistoryValid`/`VoterEvolution` interface. Local commitIndex may lag global commitment; a local truncation guard is not a substitute for the historical preservation argument. Crash/recovery, stable storage, physical timers, nextIndex retry optimization, snapshots, membership changes, Byzantine behavior, command application, and liveness are outside this model. No delivery or scheduling fairness is assumed.

Reference: Ongaro and Ousterhout, [Raft, Figure 2 and §5](https://raft.github.io/raft.pdf). This is a scoped model, not certification of a Raft implementation. Novelty is not assessed.

[Validation](../VERIFICATION.en.md). Suite theorem: `raft_state_machine_master_suite`.
