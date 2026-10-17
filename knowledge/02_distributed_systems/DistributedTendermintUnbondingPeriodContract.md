---
id: DistributedTendermintUnbondingPeriodContract
language: en
section: distributed
source: Verification/DistributedTendermintUnbondingPeriodContract.lean
source_sha256: 32c12ef76c71a91ad0fa1df793b745a38b6cb029dd4c10f32e099f20276e629e
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintUnbondingPeriodContract.lean)

# Evidence deadlines and delayed stake withdrawal

## Model and assumptions

Module 195 adds a finite list of withdrawal tranches to the sequential replay ledger.
The state contains discrete time, an admission/withdrawal phase, active rational
balances, the queue, accumulated confiscation, completed withdrawals per validator,
and finite processed (height, validator) keys. Window has a strictly positive
Nat duration fixed for the execution. Maturity is derived as requested + duration;
there is no independently writable maturity field. WellFormed requires all monetary
components to be nonnegative. Stable Fin n identities and trustworthy initial state
are external premises.

request_unbonding transfers a positive amount bounded by the active balance into
the queue during admission. It creates no value. A queued tranche stops participating
at request time r and is liable only for offences h <= r. This is the chosen abstract
policy, not a conformance claim about deployed Tendermint/Cosmos implementations.
An active balance is currently slashable; historical deposits, redelegation and
changing validator sets are not modeled.

is_timely w h now means h <= now <= h + duration, without truncated subtraction.
slash_unbonding accepts only during admission, at a valid time and rate 0 < alpha <= 1.
It derives the offender set using module 179's attribute_evidence with Config.height,
EvidenceView and an optional complete authenticated reference. Future/expired input,
invalid evidence, a missing reference, closed admission or an invalid rate cannot
change state. For each fresh (height, validator) key it reduces active stake and
eligible queued tranches proportionally. Later offences do not affect an earlier
request's tranche. Even a zero eligible balance consumes its accepted replay key.

## Refinement and proven invariants

ledger_refinement equates the projection of the actual queue/active update with
module 194's applyCertifiedSet on current eligible balances. The confiscation and
processed fields come directly from that operator. replay_idempotence proves that
the checked transition does not charge an accepted key twice. Certificates sharing
keys therefore cannot bypass replay filtering by changing their representation.

request_conservation, checked_conservation and finalize_conservation preserve active
stake + queue value + confiscation + completed withdrawals. Nonnegativity is preserved
by every public operation. batch_conservation, total_value_conservation and
slot_wellFormed cover arbitrary finite certificate batches within a slot.

no_escape_theorem proves now <= maturity for timely evidence and h <= request.
no_early_withdrawal proves that an actual pending entry survives finalization before
maturity; admission_finalize_noop blocks payout throughout certificate admission,
including equality. no_prior_finalization excludes an earlier slot's payout of a
liable tranche while evidence is still timely now. This guarantee does not cover
later offences h > request or already absent/unbacked initial tranches.

timely_slashing_guarantee requires a genuinely accepted offender, admission, timeliness,
a fresh key, a positive current eligible balance, WellFormed state and a positive
valid rate. It proves a strictly increasing confiscation pool. Historical positive
stake alone does not suffice after other penalties.

## Two-phase slots and conditional liveness

processSlot folds the supplied certificate batch, closes admission, finalizes matured
entries using their current reduced amounts, then advances time by exactly one.
No certificates may be accepted in the withdrawal phase. Closing admission assumes
the supplied batch is complete; this finite model cannot ensure network delivery or
inclusion of an unseen certificate. Calling close_admission prematurely is outside
the intended slot scheduler; a regression explicitly shows the lost debit if the
phases are reversed.

deadline_precedence_theorem and checked_deadline_precedence prove that a liable
single tranche maturing at the inclusive evidence deadline pays (1-alpha)*amount
after slashing. With full confiscation the payout is zero. The general conservation
and refinement results apply to arbitrary finite queues.

QueueSafe states that every accepted certificate excludes each queued owner or
concerns an offence after that tranche's request. honest_queue_safe derives this
premise from module 179's honest attribution theorem for a reachable reference.
batch_safe_context preserves the queue under these certificates. safe_batch_payout
pays exactly the original matured queue sums; honest_withdrawal_liveness specializes
this to full payment of a single honest tranche. Fairness is explicit: time must
reach maturity and the slot/finalization transition must actually execute. This is
an enabled scheduled payout theorem, not unconditional eventual progress of a network.

## Regressions, hierarchy and Clean Water

Kernel-checked exact rational examples and separate executable scenarios cover
future, deadline and expired evidence, invalid inputs, half/full penalties, replays,
a mixed queue with different liability cutoffs, overdrawn requests, honest payout,
time progression and a deliberately reversed-phase counterexample. A nonempty
accepted certificate is realized by an executable reachable faulty-vote trace.
Registry examples exercise the integrated master suite.

Hierarchy: epsilon 195; gamma distributed; delta distributed/tendermint-accountability.
Public Git release v0.7.4 exports private snapshot
52174d5a9ef0065506e2dfc3d10e9a267fc6a623. Lake remains 0.7.1. The last full public
control remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); private evidence
is separate. Final command results and counts are recorded in external evidence
rather than inferred from the theorem count.

Only propext, Classical.choice and Quot.sound are allowed. Network delays, clock
synchronization/authentication, concurrent mempools, durable databases, chain reorgs,
epoch identity mapping, changing the window during execution and production-code
refinement remain external obligations. Python equivalence, JSON/SHA-256 and SimLab
remain open. Novelty is not assessed.

[Module 196](DistributedTendermintEpochIdentityContract.md) adds injective epoch identity maps and checked historical attribution into global liability keys. Quorum handover and history authentication remain external.
