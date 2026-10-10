---
id: DistributedCRDTORSet
language: en
section: distributed
source: Verification/DistributedCRDTORSet.lean
source_sha256: ba7dc0f173dadbdd417e7b45511deceba6c6a81cd9abcccd99a79dfc165c4452
novelty: not-assessed
status: reviewed
---

# Observed-remove set: causal add-wins and operational convergence

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedCRDTORSet.lean)

## Model and established results

The intended group is Fin n with n >= 1. Generic theorems also admit the vacuous
empty group. Elements require decidable equality, not an order or a finite domain.
Tags are natural counters paired with replica IDs. Each local update (add or remove)
increments its replica's persistent counter. No total order on tags is used, and
receiving a snapshot does not need to advance this counter.

ORSetState contains finite sets added and removed of element/tag pairs. added retains
all included additions, including removed ones. Membership requires a tag in added
but not removed. Both components grow monotonically; the visible set need not grow.
The empty state is bottom. Componentwise inclusion and union give unconditional
PartialOrder, SemilatticeSup and OrderBot instances, without a compatibility premise.
The reachable invariant removed subset added is proved from the transitions.

add inserts a freshly generated pair. remove captures exactly the currently live
tags of its selected element and unions this fixed context into removed. Other
elements remain visible. Operational commit merges immutable effects: an add effect
contains one added pair; a remove effect contains its captured context in both
components. Since that context was already added, remove_payload proves equality
with the direct remove operation. Receiving never recomputes a removal context.

## Operational provenance and causality

A Config has replica payloads, persistent counters, an issued-operation archive and
an archive of authentic sent snapshots. Snapshots carry proof-only histories.
Update IDs label both kinds of update; the ID of an add is also its element tag.
The serial field records creation position for proofs only. Neither serial nor
causal histories participate in payload merge, tag generation or element queries.

Induction on Reachable proves ID uniqueness, freshness, origin counter bounds,
exact payload-as-join-of-history, provenance of every added tag in an actual add,
and provenance of every tombstone in an observed add. The relation HappensBefore
uses the operation IDs observed before an update, independently of visible values.
Local histories accumulate local updates and received histories. Closure and strict
creation order imply transitivity and irreflexivity on one reachable execution.
Concurrent requires distinct operations and neither causal direction.

concurrent_add_wins derives absence of the new tag from the other operation's
removal context. concurrent_add_wins_snapshots proves survival in complete
post-operation snapshots, including prior metadata; commit_operation_snapshot
supplies the required boundary property for real local transitions. This is a
statement about the concurrent pair, not permanent survival against later observed
removals. removed_tag_never_resurrects concerns a fixed tag; operational_readd
proves that a new local add becomes visible even after a previous removal.

## Convergence and dissemination

sec_strong_convergence equates payloads for equal sets of included immutable
updates, including across executions. Captured removal contexts are part of those
updates. Equal sequences of unannotated add/remove commands are not enough.
Ordering and repetition of merges do not affect their metadata join.

The persistent sent archive models reliable availability without a delay bound.
FairSend sends each replica's current snapshot after every prefix. WeakFairness
requires receiving a continuously available snapshot if its information remains
missing at the recipient. eventual_dissemination derives eventual inclusion of each
issued effect without quiescence. eventual_stabilization derives a finite common
time after NoUpdatesAfter after which all payloads remain the global join.
global_join_exact identifies it with the finite supremum of the replicas at the
quiescence checkpoint. Already completed dissemination is not a premise.

BroadcastBridge.adapter reads actual DistributedCausalBroadcast delivery logs with
an immutable message-ID-to-payload binding. adapter_step proves incremental merge;
replay_same_messages permits permutations and duplicates. The general finite-batch
bridge uses ReliableArrival and WeakFairness to deliver an announced covering batch.
The concrete checkpoint bridge requires every participant to announce its snapshot
of a fixed reachable configuration. It proves convergence to that configuration's
global join. This does not assert an ongoing coupled serializer for arbitrary local
updates interleaved with CBcast. Full-state union itself does not require causal delivery.

## Regressions and Clean Water boundaries

Kernel proofs cover empty state, one replica add/remove/re-add, a shared old tag
followed by concurrent add/remove, both receive orders, removal of only the observed
tag, duplicate and stale snapshots. The external live regression applies the full
snapshot add-wins theorem, removes the later-observed concurrent tag, rejects a stale
snapshot, re-adds again, and checks a Boolean element type without an ordering.

Explicit counterexamples show that tag reuse suppresses a new add and that premature
tombstone collection resurrects a removed element upon receiving an old snapshot.
The latter discards both removed pairs and their tombstones, so the collected state
is initially empty: the stale message is what causes resurrection.

Tombstone garbage collection, causal-context compression/ORSWOT, linearizability,
consensus, dynamic membership, Byzantine messages and recovery after memory loss
are not modeled. Naturals do not overflow; bounded machine counters are outside the
model. Python correctness, JSON/SHA-256 correctness and SimLab correspondence remain
open. Novelty is not assessed.

References: [Shapiro et al., CRDTs (2011)](https://www.lip6.fr/Marc.Shapiro/papers/2011/CRDTs_SSS-2011.pdf);
[Bieniusa et al., OR-Set and optimizations (2012), section 4.1](https://www.lip6.fr/Marc.Shapiro/papers/RR-8083.pdf).
The representation here retains all additions; the live-entry representation of the
latter paper is obtained as E = added minus removed, with T = removed.

## Validation

Private base snapshot: fb5b736e7f4794f96e1ee5f61d9b50af7cd8a571.
All required project and export checks passed; measured results follow.

## Private snapshot validation: observed-remove set

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 133 |
| Lean sources | 175 under Verification/; 176 including root |
| Strict clean private build | 3624 jobs; no warnings |
| Both full axiom audits | 16494 declarations; no violations |
| Private live tests | 81; no failures or skips; 275.411s |
| Export live tests | 78; no failures or skips; 287.013s |
| Strict clean export build | 3624 jobs; no warnings |

Module verify and audit each covered 1691 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent audit source commit is 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256 is 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. A second independent proof kernel is not claimed.
Counts include generated declarations. Project build directories started empty,
with isolated copies of pinned dependency caches. All 176 exported Lean files match;
repeated exports agree. Integration is idempotent. The original HEAD and
406 tracked files are preserved. No task writes to simulations/;
that earlier private integration did not publish a public release.

## Source theorem links

- [observed_remove_exact](../../Verification/DistributedCRDTORSet.lean#L75)
- [removed_tag_never_resurrects](../../Verification/DistributedCRDTORSet.lean#L89)
- [reachable_invariant](../../Verification/DistributedCRDTORSet.lean#L443)
- [tag_uniqueness](../../Verification/DistributedCRDTORSet.lean#L454)
- [state_is_join_history](../../Verification/DistributedCRDTORSet.lean#L458)
- [sec_strong_convergence](../../Verification/DistributedCRDTORSet.lean#L466)
- [happens_before_irrefl](../../Verification/DistributedCRDTORSet.lean#L479)
- [concurrent_add_wins](../../Verification/DistributedCRDTORSet.lean#L500)
- [operational_readd](../../Verification/DistributedCRDTORSet.lean#L519)
- [eventual_dissemination](../../Verification/DistributedCRDTORSet.lean#L614)
- [eventual_stabilization](../../Verification/DistributedCRDTORSet.lean#L658)
- [global_join_exact](../../Verification/DistributedCRDTORSet.lean#L685)
- [adapter_step](../../Verification/DistributedCRDTORSet.lean#L737)
- [causal_broadcast_bridge](../../Verification/DistributedCRDTORSet.lean#L789)
- [concurrent_add_wins_snapshots](../../Verification/DistributedCRDTORSet.lean#L857)
- [counterexample_tag_reuse](../../Verification/DistributedCRDTORSet.lean#L972)
- [counterexample_tombstone_gc](../../Verification/DistributedCRDTORSet.lean#L981)
- [distributed_crdt_orset_master_suite](../../Verification/DistributedCRDTORSet.lean#L1041)

## Public release validation

The [v0.5.31 report](../../docs/release-v0.5.31.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 133 |
| Lean files under Verification/ | 173 top-level + 2 auxiliary = 175 |
| Root-inclusive sources identical to the private snapshot | 176 |
| Clean strict build | 3624 jobs; no warnings |
| Complete verifier audit | 16494 declarations; no violations |
| Pinned independent full audit | 16494 declarations; no violations |
| Public live tests | 78; no failures or skips; 277.247s |
