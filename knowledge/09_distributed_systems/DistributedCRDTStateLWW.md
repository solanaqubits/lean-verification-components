---
id: DistributedCRDTStateLWW
language: en
section: distributed
source: Verification/DistributedCRDTStateLWW.lean
source_sha256: fa4b9e8c73c03e0d28eebb2f49e6868646828d20d8cc46d88b3c169bfa851454
novelty: not-assessed
status: reviewed
---

# State-based LWW register with operational convergence

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedCRDTStateLWW.lean)

## Model and established results

The intended group is Fin n with n >= 1; general statements also admit the vacuous
empty group. A stamp is a natural counter and replica ID with lexicographic order.
The register is Option (Stamp × value), with none as the initial bottom. Values
need no ordering. Merge selects the greater complete stamp; equal stamps select
the right argument. This rule is commutative on compatible states, whose equal
stamps necessarily carry equal values.

Write uses the local observed counter plus one and its own replica ID. Receive
merges the payload and raises the local clock to the maximum of the old clock
and the received counter. Send captures a snapshot. Induction from the empty
configuration proves uniqueness of issued stamps' values, authentic snapshots,
clock bounds, monotonicity, and the exact maximum-of-history representation.
Uniqueness is derived from fresh generation and persistent per-replica clocks;
it is not a transition guard or an assumption of the reachable-state theorem.
fresh_above_observed proves that a new counter exceeds every included update.

Histories are ghost observations; the sent archive models available transport snapshots.
Histories may contain
duplicates and are not read by operational merge or clock generation. The stored
register, unlike the ghost history, contains only one winning entry. IsMax says
that this winner occurs in the history and bounds every entry; payload_is_max_history
also equates the payload to the executable summarize function.

On ValidState H for a common Unique H, actual PartialOrder, SemilatticeSup and
OrderBot instances are constructed. Associativity, commutativity, idempotence,
least-upper-bound, monotonicity and inflationarity are proved. No partial-order
or commutativity claim is made for arbitrary malformed stamp/value pairs.
RegLE on unrestricted registers is only the stamp-induced preorder.

Equal sets of included entries imply equal register payloads, including across
different admissible traces. Reordering and repeated entries do not change the
result. Equality is not claimed for ghost logs, network archives or clock metadata.

## Dissemination and quiescent stabilization

The persistent sent archive models reliable availability of authentic immutable
snapshots to every participant. It permits arbitrary delays, reordering and repeated
reception, and has no loss or capacity bound. FairSend schedules every continuously
enabled sender again after any prefix. WeakFairness is per recipient and snapshot:
a continuously available snapshot whose information is still missing eventually
gets a receive step. Already subsumed snapshots need not be processed again.

eventual_dissemination proves that each issued update eventually lies below every
replica's payload, without requiring writes to cease. It expresses dissemination
of information: obsolete individual versions can be superseded before transmission.
After an explicit NoWritesAfter prefix, eventual_consistency_stabilization derives
a finite common bound after which all register payloads permanently equal the
global history maximum. Receipt of all snapshots or equality of replicas is not
assumed. Strong convergence and this conditional liveness theorem are separate.

## Causal-broadcast adapter

BroadcastBridge.adapter replays immutable message-ID-bound snapshots along the
actual application delivery log of DistributedCausalBroadcast. adapter_step proves
the incremental merge equation, including atomic self-delivery. replay_same_messages
proves independence from order and duplicates for compatible snapshots.

The general finite-batch bridge assumes authentic payload bindings bounded by a
common compatible history and that already announced snapshots collectively cover
its information. It uses the earlier ReliableArrival and WeakFairness theorem to
derive eventual saturation of all receivers. snapshot_valid_at derives snapshot
validity from the LWW operational execution. The concrete checkpoint corollary
captures one fixed reachable configuration: after every participant announces its
snapshot, all receivers eventually stabilize to that configuration's global maximum.
Further broadcasts of the same checkpoints are harmless. The transport's numerical
clock rules are unchanged. A simultaneous coupled protocol for arbitrary ongoing
LWW writes and payload serialization is not asserted by the checkpoint corollary.

## Regressions and boundaries

Kernel-checked witnesses cover bottom, one replica, equal counters resolved by ID,
both receive orders, duplicate and late snapshots, and writing above an observed
remote counter. Counterexamples show failure of commutativity when replica IDs
are ignored, failure for conflicting values at one complete stamp, and loss of
monotonicity under stale overwrite of a reachable state. The external live test
adds a relay write followed by a stale packet and a Boolean-valued register.

Logical last-write-wins does not identify the latest physical-time write. Convergence
does not establish consensus, linearizability, a multi-value register, physical-clock
synchronization, Byzantine tolerance, crash recovery or dynamic membership.
Mathematical naturals do not overflow; finite machine counters and resetting clocks
after memory loss are outside the model. Python correctness, JSON/SHA-256 correctness
and SimLab-to-Lean correspondence remain open. Scientific novelty is not assessed.

References: [Shapiro et al., comprehensive CRDT study (2011), §3.2.1](https://www.lip6.fr/Marc.Shapiro/papers/2011/Comprehensive-CRDTs-RR7506-2011-01.pdf);
[Strong Eventual Consistency and CRDTs (2011)](https://www.lip6.fr/Marc.Shapiro/papers/2011/CRDTs_SSS-2011.pdf).

## Validation

Private base snapshot: 77948161a169a42dee824a8a2e1236e582665be4.
All required project and export checks passed; measured results follow.

## Private snapshot validation: state-based LWW register

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 132 |
| Lean sources | 174 under Verification/; 175 including root |
| Strict clean private build | 3623 jobs; no warnings |
| Both full axiom audits | 16006 declarations; no violations |
| Private live tests | 80; no failures or skips; 275.266s |
| Export live tests | 77; no failures or skips; 284.181s |
| Strict clean export build | 3623 jobs; no warnings |

Module verify and audit each covered 1204 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent audit source commit is 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256 is 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1. Auditor source toolchain file: v4.32.0-rc1;
the executable is pinned separately. A second independent proof kernel is not claimed.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. All 175 exported Lean files match;
repeated exports agree. Integration is idempotent. The original HEAD and 406 tracked
files outside simulations/ are preserved. No task writes to simulations/; this earlier private check did not publish a public release.


## Source theorem links

- [stamp_le_iff](../../Verification/DistributedCRDTStateLWW.lean#L28)
- [reachable_invariant](../../Verification/DistributedCRDTStateLWW.lean#L382)
- [stamp_uniqueness](../../Verification/DistributedCRDTStateLWW.lean#L392)
- [merge_comm](../../Verification/DistributedCRDTStateLWW.lean#L122)
- [merge_assoc](../../Verification/DistributedCRDTStateLWW.lean#L127)
- [payload_is_max_history](../../Verification/DistributedCRDTStateLWW.lean#L396)
- [sec_across_traces](../../Verification/DistributedCRDTStateLWW.lean#L410)
- [eventual_dissemination](../../Verification/DistributedCRDTStateLWW.lean#L527)
- [eventual_consistency_stabilization](../../Verification/DistributedCRDTStateLWW.lean#L565)
- [adapter_step](../../Verification/DistributedCRDTStateLWW.lean#L653)
- [causal_broadcast_bridge](../../Verification/DistributedCRDTStateLWW.lean#L721)
- [counterexample_tie_breaking](../../Verification/DistributedCRDTStateLWW.lean#L834)
- [counterexample_stale_stamp](../../Verification/DistributedCRDTStateLWW.lean#L844)
- [distributed_crdt_state_lww_master_suite](../../Verification/DistributedCRDTStateLWW.lean#L880)

## Public release validation

The [v0.5.30 report](../../docs/release-v0.5.30.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 132 |
| Lean files under Verification/ | 172 top-level + 2 auxiliary = 174 |
| Root-inclusive sources identical to the private snapshot | 175 |
| Clean strict build | 3623 jobs; no warnings |
| Complete verifier audit | 16006 declarations; no violations |
| Pinned independent full audit | 16006 declarations; no violations |
| Public live tests | 77; no failures or skips; 271.527s |
