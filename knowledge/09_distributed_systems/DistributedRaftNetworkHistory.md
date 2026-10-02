---
id: DistributedRaftNetworkHistory
language: en
section: distributed
source: Verification/DistributedRaftNetworkHistory.lean
source_sha256: d1203d13a78f51266ef0fa67ef168bda7764fd298d714266f4d547dbe4064832
novelty: not-assessed
status: reviewed
---

# DistributedRaftNetworkHistory

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftNetworkHistory.lean)

## Historical elections and message provenance

This supporting module derives election-tenure and AppendEntries provenance facts from the unchanged [DistributedRaftStateMachine](DistributedRaftStateMachine.md). It uses the machine's historical `elected` records, previously proved election uniqueness, term monotonicity, and actual queue-construction rules. Neither global Log Matching nor `HistoryValid` is assumed.

`MessageAuth` states that an AppendEntries packet names an elected leader of its term and has a destination different from that leader. Other message variants satisfy this particular predicate trivially; it is not a general authentication theorem for every RPC payload. `NetworkAuth` applies the predicate to every queued envelope.

Here authentication means provenance within the transition system, which has no external message-injection step. No cryptographic signature scheme, authenticated transport implementation, or Byzantine adversary is modeled.

## Proved statements

- `elected_step_monotone` preserves all historical election records.
- `network_auth_step` preserves AppendEntries provenance under every modeled transition, including loss, duplication, and arbitrary-position delivery.
- `elected_bound_step` keeps each elected term below or equal to the elected node's current term.
- `reachable_history` derives all fields of `HistoryFacts` for every state reachable from initialization: elected-term bounds, same-term leadership tenure, and AppendEntries provenance.
- `active_elected_log_length_step` proves that an elected node's log length cannot decrease across a step if its post-step current term still equals that election term.

The tenure statement has an explicit same-term condition: if `(t, n)` is in `elected` and node n's current term is still t, its role is leader. It does not assert that leadership survives observation of a higher term. A same-term AppendEntries packet addressed to that leader would require a different elected sender in the same term; historical election uniqueness and exclusion of self-directed packets rule this out.

The log-length result combines this tenure theorem with the existing `leader_append_only_step`. It is not a blanket monotonicity theorem for follower logs, which may replace conflicting suffixes.

## Boundaries and use

This module does not prove payloads are contiguous slices of a leader log. Historical source snapshots and global prefix consistency are handled by [DistributedRaftNetworkInduction](DistributedRaftNetworkInduction.md). This helper alone does not derive preservation of committed entries or Leader Completeness. The separate [DistributedRaftCompleteBridge](DistributedRaftCompleteBridge.md) develops the operational argument using actual execution histories, without literally instantiating abstract `VoterEvolution`; see its own validation status.

The inherited machine has a fixed nonempty cluster and no external RPC injection, crash/recovery, membership changes, or fairness assumption. Historical election records are proof state produced by actual modeled elections, not extra conditions checked by the protocol.

## Validation

Strict full-project build, per-module verification/audit of the importing network suite, `verify-all`, independent axiom audit, and the complete live test suite passed. Exact source hashes and project counts are in the [validation record](../VERIFICATION.en.md). No disallowed axioms were found; mathematical novelty is not assessed.
