---
id: DistributedRaftNetworkInduction
language: en
section: distributed
source: Verification/DistributedRaftNetworkInduction.lean
source_sha256: dea39913e94b22e08afe089f8160e2d4db5f527ad88ca505c0e86033065f2809
novelty: not-assessed
status: reviewed
---

# DistributedRaftNetworkInduction

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftNetworkInduction.lean)

## Result

`reachable_global_log_matching` proves `GlobalLogMatching s` from the existing operational `Reachable s`, for every fixed nonempty cluster. For any two server logs, equal terms at position `k` imply equal prefixes through `k`, including the command at that position. The theorem has no assumed Log Matching, input compatibility, valid abstract history, or additional transition guard.

The original `DistributedRaftStateMachine.Step`, `Reachable`, and RPC handlers are unchanged. Reachability includes partial batches, arbitrary delivery positions, delayed packets, duplication, and loss. This is a safety theorem over all finite executions of that model; no fair delivery is assumed.

## Induction and provenance

A proof-only archive contains current logs, historical source logs, and their prefixes. `ArchiveInvariant` strengthens the induction hypothesis with pairwise matching, entry provenance, server membership, and backing for queued messages. The initial archive contains only the empty log. Only an actual leader append introduces a fresh log; every other log-changing step produces an already represented prefix.

`Backed` connects each queued AppendEntries batch to a reachable historical state with the indicated node acting as leader in the indicated term. It records the exact source log, checked predecessor term, contiguous `drop`/`take` slice, and a sequence of original `Step` transitions from that historical state to the present. The sender's current log need not equal this historical snapshot.

`Generated` supplies a concrete reachable leader-append event for every archived entry, including its command, generating term, and position. Theorems `reachable_record_origin` and `reachable_network_entry_origin` expose that witness for server logs and packet entries; `reachable_entry_index` proves the stored index is the one-based list position.

Election-history safety and same-term leader tenure establish that a new entry's term cannot already occur at the new position in an archived log. The predecessor check and the induction hypothesis establish prefix agreement before applying the batch. Compatibility of equal-term entries is derived, not assumed by the operational transition.

The actual merge retains the old suffix when an incoming short batch matches it. A first term conflict replaces the suffix. The helper theorem proves that a successful merge is either the old log or a prefix of the archived source; it does not replace every AppendEntries handler by unconditional truncation.

Supporting modules are [NetworkHistory](DistributedRaftNetworkHistory.md) and [NetworkLogLemmas](DistributedRaftNetworkLogLemmas.md). The main suite is `RaftNetworkInductionSuite`, constructed by `raft_network_induction_master_suite`.

## Boundaries

This module closes global Log Matching for this operational model. Preservation of committed entries and operational Leader Completeness are treated separately in [DistributedRaftCompleteBridge](DistributedRaftCompleteBridge.md), whose card records its own validation status. That argument uses events from the same execution rather than literally instantiating the abstract `HistoryValid`/`VoterEvolution` premises. Neither unconditional State Machine Safety nor eventual convergence follows from Log Matching alone.

The model has a fixed cluster, authenticated protocol-generated messages, and no external packet injection. Crash/recovery with stable storage, membership changes, snapshots, Byzantine behavior, physical timing, and liveness are not modeled. No claim of correctness for a production implementation or novelty is made.

Reference: Ongaro and Ousterhout, [Raft, §5.3 and Figure 3](https://raft.github.io/raft.pdf). The archive makes the historical information needed by the replication argument explicit; §5.4's separate committed-entry argument is handled by [CompleteBridge](DistributedRaftCompleteBridge.md).

[Validation](../VERIFICATION.en.md).
