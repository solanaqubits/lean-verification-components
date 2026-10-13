---
id: DistributedRaftJointConsensusReconfig
language: en
section: distributed
source: Verification/DistributedRaftJointConsensusReconfig.lean
source_sha256: 50a422131f127e3f9772e2157f510a65bce23f855bff4e20f70ce0b541fbb2e1
novelty: not-assessed
status: reviewed
---

# Operational Raft joint-consensus reconfiguration

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftJointConsensusReconfig.lean)

## Model and result

One arbitrary transition uses two nonempty finite sets of natural-number node
identifiers: stable-old, joint-old-new, stable-new. Commands may occur throughout
the transition. Every node activates the latest configuration in its local log
immediately, before commitment; removing an uncommitted suffix recomputes that
configuration from the surviving log. Nodes can have different active configurations.

The transition rules include timeouts, higher-term observation, persistent voting
within each term, candidate log-freshness checks, authenticated RPC delivery,
partial AppendEntries batches, acknowledgments, current-term commits, message
loss, duplication and reordering. The network may delay messages arbitrarily.
An excluded leader retires when it commits stable-new. There is no external message
injection and no Byzantine behavior. Snapshots and crash/recovery are not modeled.

The completed suite proves, from operational reachability:

- **Election Safety:** all historical successful elections in any one term name
  the same node, including elections under old and new configurations.
- **Log Matching:** entries at the same position with the same term have equal
  log prefixes through that position.
- **Leader Completeness:** every prefix fixed by a real current-term commit on
  a stable or joint quorum is present in every later-term leader's log. Entries
  retain their original terms, which need not equal the committing term.
- **Commit-index soundness:** every entry below a local commitIndex has the exact
  contents of an earlier actual commit on the same execution.
- **Joint-before-new:** appending stable-new requires an actual strictly earlier
  joint-quorum commit whose prefix contains the joint entry. The result also
  covers identical old and new memberships.

Stable quorums are majorities within their membership. Joint quorums require
separate majorities of both sets. Old–joint, joint–new and joint–joint intersections
are proved; the last includes a witness in each membership. Stable-old and
stable-new quorums can be disjoint. Their successful elections are made incompatible
by the operational joint barrier, not by asserting a nonexistent intersection.

## Proof architecture

`HistoricalCommitPrefix` identifies the real historical commit, its index bound,
the exact local prefix and a term bound. Partial batches may inherit a shorter
prefix than the original commit. `HistoricallyCommitted` refers to an actual
`CommitEvent` on the same trace; it does not require that all replicas still hold
the entry at the time of observation. `commit_origin_implies_quorum_replication`
provides the corresponding historical replica snapshots and acknowledges delayed replies.

The proof nests induction on terms inside induction on execution length. Under
safety of a finite prior history, term induction establishes completeness, then
content-sensitive commit provenance, then provenance of new-configuration entries.
These lemmas rule out conflicting old/new campaigns before the next election.
The outer induction proves safety of the extended execution and discharges the
auxiliary hypotheses. No desired invariant is a guard of `Step`, `mayVote` or
`mayAppend`. The exported suite has no assumed Election Safety or Leader Completeness.

`committed_prefix_preserved_at_election` also covers a quorum-backed candidate
before it becomes leader. Log freshness alone would not imply prefix inclusion;
the proof uses entry origins, historical matching and intermediate-term induction.
Retirement is supported: an elected node can become a follower in its own term.

## Main interfaces and regressions

The master theorem is `distributed_raft_joint_consensus_master_suite`.
Core interfaces are `raft_reconfig_election_safety`, `raft_reconfig_log_matching`,
`raft_reconfig_leader_completeness`, `commit_index_soundness`,
`joint_committed_before_new_created` and `raft_reconfig_rollback_on_truncate`.

`Examples` proves a reachable complete disjoint handover `{0} → Joint {0} {1} → {1}`,
commitment of both configuration entries, old-leader retirement and a new leader
in term 2. `RollbackExample` gives a reachable leader change that overwrites an
uncommitted joint entry and restores the old configuration. Regressions cover
singleton elections, activation before commit, premature-new rejection, retained
suffixes after short batches, and the insufficiency of freshness alone.

`fixed_cluster_append_entries_bridge` is an exact local bridge to the existing
static Raft model for command-only log merging. It is not a full simulation
relation between the two automata. The direct-switch split-brain example is an
algebraic pair of disjoint quorums with consistent split votes, not a trace of a
separate unsafe protocol.

## Validation and Clean Water

The verification workflow uses `verifier_skill.py verify` / `audit`, strict
`lake build --wfail`, `verify-all`, live unittest, the pinned independent axiom
auditor, `Verification/AxiomAudit.lean` and `scripts/check_knowledge.py`.
The only permitted axioms are `propext`, `Classical.choice`, `Quot.sound`.

The scope is one fixed transition, arbitrary commands and reachable asynchronous
message schedules. Unbounded sequences of reconfigurations, snapshots, Byzantine
faults, crash/recovery and liveness are excluded. Python, JSON/SHA-256 and SimLab
obligations remain open. The Python regression harness invokes Lean; it does not
verify a Python Raft implementation.

Specification: [Ongaro–Ousterhout, §§5.3–5.4 and §6](https://raft.github.io/raft.pdf).

## Public release validation

The [v0.5.48 report](../../docs/release-v0.5.48.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 150 |
| Lean files under Verification/ | 190 top-level + 2 auxiliary = 192 |
| Root-inclusive sources identical to the private snapshot | 193 |
| Clean strict build | 3741 jobs; no warnings |
| Complete verifier audit | 20338 declarations; no violations |
| Pinned independent full audit | 20338 declarations; no violations |
| Public live tests | 95; no failures or skips; 303.516s |
