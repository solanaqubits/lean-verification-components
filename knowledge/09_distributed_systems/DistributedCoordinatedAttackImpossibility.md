---
id: DistributedCoordinatedAttackImpossibility
language: en
section: distributed
source: Verification/DistributedCoordinatedAttackImpossibility.lean
source_sha256: 7c62395bf8705b08def1db0b24b6befa9494a7b90ff8279776d432a7deaa7534
novelty: not-assessed
status: reviewed
---

# Coordinated attack: finite-round operational impossibility

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedCoordinatedAttackImpossibility.lean)

## Model and theorem

There are two correct deterministic processes (Fin 2), private binary inputs,
arbitrary message and local-state types, and a fixed finite horizon T. In every
round both messages are computed from the pre-round states. A Boolean schedule
independently delivers or drops each directed message. A process receives an
Option Msg from its peer; it has no direct feedback about its outgoing delivery.
Self-delivery flags are ignored. Execution after T is held constant.

Agreement quantifies over every input and delivery schedule. ValidityZero requires
both processes to retreat for all-zero inputs under every schedule. ReliableSuccess
requires attack for all-one inputs when every message is delivered. The main theorem
proves that no protocol satisfies all three, for every finite T including zero.
This is a synchronous omission model, distinct from asynchronous crash-failure FLP.

## Operational proof

Removing one outgoing delivery leaves the sender's next state unchanged, because
both executions have the same earlier history and incoming message. If there are
no later deliveries, the sender's entire subsequent local-state history remains
equal. These facts are derived from execution recursion. Later outgoing contents
are recomputed by the protocol, not reused from an invalid trace.

Under Agreement, the preserved sender decision forces the common decision to stay
equal. The finite support records actual cross-process deliveries. A maximal round
provides a removable event, erasing it strictly decreases the support cardinality,
and strong induction reduces any schedule to the empty schedule.

With no delivery a local state depends only on that process's private input.
Changing the peer's input, then exchanging the witness process and changing the
other input, preserves the common decision under Agreement. Thus Agreement and
ValidityZero force retreat on every input and every schedule. ReliableSuccess
contradicts this derived result. No no-attack-on-silence or indistinguishability
premise is assumed. Agreement is a specification hypothesis for the impossibility
result, not a property claimed for arbitrary protocols.

## Regressions and counterexample

The always-retreat protocol satisfies Agreement and ValidityZero but fails
ReliableSuccess. Zero rounds are covered. Two delivery erasures commute as schedules;
for two events in the last round Agreement also preserves the original common decision.

An explicit two-round request/acknowledgement protocol succeeds with reliable
communication. Dropping the final ack preserves the ack sender's local state, but
the receiver retreats while the sender attacks: this concrete protocol violates
Agreement. For any protocol satisfying Agreement and ValidityZero, the same lost-ack
schedule instead forces both decisions to retreat. The unsafe example is not used
as a safety assumption.

## Clean Water boundaries

The result concerns deterministic protocols with a fixed finite horizon, ideal
local computation, private inputs and independent message omissions. It does not
claim the extension to eventual termination without a uniform finite bound.
Randomized epsilon-agreement, quantum communication and Byzantine behavior are
outside scope. There is no trusted delivery oracle or sender-visible receipt.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is not
assessed. Only propext, Classical.choice and Quot.sound are permitted.

Proof reference: [Aspnes, indistinguishability and coordinated attack](https://www.cs.yale.edu/homes/aspnes/pinewiki/IndistinguishabilityProofs.html).

## Validation

Base snapshot: 845ef3d56ad066f0b3896d917e3ebf90e9f7367c.
All project and export checks passed; measured results follow.

## Source theorem links

- [execution_congr_before](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L66)
- [erase_before](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L80)
- [local_state_independent_of_undelivered_msg](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L88)
- [last_delivery_removal_indistinguishability](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L101)
- [agreement_at](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L121)
- [last_delivery_preserves_decision](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L128)
- [deliveries_erase](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L143)
- [exists_last_delivery](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L155)
- [empty_deliveries_execution](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L174)
- [schedule_reduction_to_empty](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L186)
- [empty_local_input](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L202)
- [input_flip_indistinguishability](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L211)
- [no_delivery_forces_retreat](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L220)
- [all_schedules_force_retreat](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L225)
- [coordinated_attack_impossibility](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L231)
- [no_correct_protocol](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L240)
- [trivial_retreat_protocol_satisfies_partial](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L252)
- [zero_horizon_impossibility](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L259)
- [erase_deliveries_commute](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L264)
- [cancellation_order_invariance](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L271)
- [last_round_after_erase](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L277)
- [independent_last_round_cancellations](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L283)
- [ack_reliable_success](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L302)
- [ack_last_round](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L306)
- [ack_loss_sender_unchanged](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L312)
- [ack_loss_counterexample](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L318)
- [ack_protocol_not_agreement](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L324)
- [two_round_ack_safe_retreat](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L333)
- [distributed_coordinated_attack_impossibility_master_suite](../../Verification/DistributedCoordinatedAttackImpossibility.lean#L359)

## Private snapshot validation: Coordinated attack impossibility

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 142 |
| Lean sources | 184 under Verification/; 185 including root |
| Strict clean private build | 3732 jobs; no warnings |
| Both full axiom audits | 18279 declarations; no violations |
| Private live tests | 90; no failures or skips; 289.89s |
| Export live tests | 87; no failures or skips; 303.265s |
| Strict clean export build | 3732 jobs; no warnings |

Module verify and audit each covered 852 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 185
exported Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

The theorem rules out Agreement, ValidityZero and ReliableSuccess together for
any fixed finite horizon. Local indistinguishability is derived from execution;
strict induction on actual deliveries reduces every schedule to zero delivery.
A concrete lost-ack protocol demonstrates disagreement, while safe protocols
must retreat. Unbounded eventual termination, randomized epsilon-agreement,
quantum channels and Byzantine behavior are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.40 report](../../docs/release-v0.5.40.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 142 |
| Lean files under Verification/ | 182 top-level + 2 auxiliary = 184 |
| Root-inclusive sources identical to the private snapshot | 185 |
| Clean strict build | 3732 jobs; no warnings |
| Complete verifier audit | 18279 declarations; no violations |
| Pinned independent full audit | 18279 declarations; no violations |
| Public live tests | 87; no failures or skips; 276.094s |
