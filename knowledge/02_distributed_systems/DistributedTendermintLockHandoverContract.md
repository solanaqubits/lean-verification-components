---
id: DistributedTendermintLockHandoverContract
language: en
section: distributed
source: Verification/DistributedTendermintLockHandoverContract.lean
source_sha256: f663fad6a79ba4d9f7cec3cfc36528c163899c4bd565f065e6c16153179171df
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintLockHandoverContract.lean)

# Checked lock handover and conditional round-zero agreement

Module 198 separates weighted quorum intersection from the local rules that make
it useful for agreement. Context fixes source/target epochs, one decision height
and two EpochConfigs over stable global IDs. The source/target local dimensions
may differ. Certificate contains the epoch, height, round, value, phase and a finite
set of actual CoreSafety.Vote records. certificateSigners filters the required
phase/round/value and maps local senders through the epoch injection; repeated
records or irrelevant votes cannot increase signer weight.

## Thresholds and checking

Polka means prevote quorum; commit means precommit quorum. Threshold.weak uses
>=2/3 and requires common honest mass >2/3; Threshold.strict uses >2/3 and permits
common honest mass >=2/3. shared_honest applies module 197 with the matching
boundary convention. core_quorum_bridge confirms that the existing natural-weight
CoreSafety/179 quorum API is the STRICT convention. The weak variant is a separate
model, not a claim that the old API used >=2/3.

Accept/checkHandover check consecutive epoch IDs, source epoch, same decision
height, prevote phase, source configuration interval, positive source weight and
quorum under normalized historical weights. The caller supplies a context, not an
authenticated chain proof. CoreSafety.Vote itself has no height/epoch fields;
the envelope and its provenance must be authenticated externally. A structurally
accepted envelope does not prove cryptographic signatures or historical truth.
The checker does not resolve missing/ambiguous history: supplying the uniquely
resolved authentic Context is an external integration obligation.

## Adoption and first-round agreement

adopt requires acceptance, membership of the new global subject and an empty local
state, or an identical already adopted state. Replaying adoption is idempotent;
a conflicting/later existing state cannot be reset. inherited retains the source
round as provenance and initializes a distinct target lock-round floor to zero.
Old and new epoch round counters are not compared as one clock.

voteAllowed/emit permit the locked value or nil in either phase; nil is abstention
and does not release the lock. They do not implement the entire Tendermint phase
machine or prove that every emitted precommit has a same-round polka.

round_zero_safety_handover assumes: an accepted source polka; an old commit quorum
for the same value/source epoch/decision height; a new round-zero commit quorum
in the target epoch at that same height; normalized target weights; the matching
honest overlap criterion; actual adoption by every honest old-commit signer who
belongs to the new membership; and HonestRoundZero vote discipline. The common
fault set B must cover the faults relevant to both epochs. The theorem proves
that the two commit values coincide. The proof obtains a positive-weight honest
shared signer from module 197, reads its transferred lock, and applies its vote
rule. It does not assume agreement in a history field.

honest_node_lock_propagation proves successful execution of adoption when its
explicit receipt/acceptance/membership premises hold. adoptions_from_execution
constructs the required adoption map. Neither theorem guarantees message delivery
or infers adoption merely from honesty or intersection. Values at different
heights are not required to be equal. The old polka and commit are explicitly
linked by value/context; this module does not derive that pair from a complete
old-epoch execution.

## Later local transitions

MayReplace checks the target epoch, same height, prevote phase, positive target
weight, quorum, positive current round, and

    lockedRound < polka.round < currentRound.

The upper bound rejects future/self-justifying certificates. The strict lower
bound is this contract's explicit replacement policy, not a restatement of every
unlock branch in the older CoreSafety implementation. Source-round provenance
is preserved while the target lock round advances. replaceLock returns rejection
for invalid certificates; execute also rejects backward round advancement.

inductive_lock_change_soundness and changed_value_has_certificate expose the
actual checked witness for each successful change. step_monotone preserves epoch
and height and makes round/lock round nondecreasing. Reachable describes arbitrary
finite sequences of advance/replace actions. reachable_round_zero_value prevents
smuggling a later replacement back into round zero. reachable_changed_value_justified
proves that any changed final value has a checked replacement witness in its history.
These results do NOT establish agreement in all later rounds: proving that no
conflicting higher polka can arise requires a global history/transition invariant.

## Regression and limits

A kernel-checked one-validator counterexample has full honest overlap and valid
old/new weighted commits with different values; the new epoch obeys its own local
lock but does not adopt the old lock. This isolates the missing handover condition.
Concrete tests also exercise real phase records, changed local ID order, both
threshold conventions, source round 17 versus target round zero, valid replacement,
nil, duplicate records, invalid context/phase/value/round, insufficient or zero
weight, inactive recipients, stale/future replacement and adoption/penalty-free
local replay. Reachability witnesses exercise successful transitions.

The finite supplied certificates are not authenticated signatures. Full asynchronous
consensus safety/liveness, phase-machine refinement, network delivery, timeouts,
clock synchronization, activation, higher-polka compatibility, history authentication
and production code remain open. Python, JSON/SHA-256 and SimLab remain open.
Only propext, Classical.choice and Quot.sound are permitted; novelty is not assessed.

Hierarchy: epsilon 198; gamma distributed; delta distributed/tendermint-accountability.
Public Git release v0.7.7 exports private snapshot
7eb0af2ad3ca2804f1de546ff72f66dfe1c3708c. Lake remains 0.7.1. The last full public
beta basis remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).
Private full control 090aed141b831aee5182197e9ea205176f361c0f and scoped evidence
remain separate. Final commands and measurements are recorded in public evidence.

[Module 199](DistributedTendermintHandoverRoundInduction.md) adds conditional all-round agreement under global history rules. Full protocol refinement, delivery and authentication remain open.
