---
id: DistributedTendermintEpochIdentityContract
language: en
section: distributed
source: Verification/DistributedTendermintEpochIdentityContract.lean
source_sha256: 129820de582f08ba5c8afa7147251af058458cced07a15eba22c65597a930610
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintEpochIdentityContract.lean)

# Stable validator identities and cross-epoch liabilities

## Model and checked boundary

Module 196 separates an epoch's local Fin n indices from stable global IDs V.
EpochConfig contains an injective toGlobal map, natural consensus weights, a Byzantine
set and an inclusive height interval. stakeMap derives a nonnegative rational map
supported on activeIds from those weights; it is not an independent arbitrary
rational quorum model. Actual balances and withdrawal tranches remain rational.
The existing module 179 Config API uses natural voting units. Historical weights
are not overwritten from current balances when validating old evidence.

HistoryRegistry stores candidate configurations per height. resolveHistory returns
an Option only for a singleton candidate whose interval contains that height.
Missing, conflicting and duplicate candidates fail closed, including duplicate
identical configurations. unique_resolution proves deterministic resolution;
unambiguous_history_requirement relates failure to the explicit UnambiguousAt
predicate. This is resolution relative to supplied trusted history, not a proof
that a singleton configuration is authentic or that arbitrary intervals globally
partition the chain.

Packet supplies a local dimension, EvidenceView and optional complete reference,
never an identity map or weights. checkPacket rejects dimension mismatches and
calls module 179's actual attribute_evidence in the resolved historical Config.
Only its accepted offender set is mapped through globalBlame. Wrong-height evidence
and missing references are rejected by that API. Reachability/authentication of
complete references remain external assumptions. historical_honest_unaccused uses
module 179's honest-attribution theorem with an explicitly reachable reference.

## Global state and proven properties

EpochState pairs the current configuration and history with module 195's generic
UnbondingState V. Balances, queue owners, completed payouts and processed (height,V)
keys therefore refer to stable subjects. epoch_transition changes only current;
it preserves the entire ledger and history, including every amount, request time,
maturity derived from the fixed window, confiscation and processed key. It does not
rebalance stake, add deposits, register keys or implement consensus activation.

applyHistorical checks admission phase, h <= now <= h + duration and 0 < alpha <= 1,
resolves/checks historical evidence, then applies slashSet. That is the actual
queue transition refined to module 194's applyCertifiedSet by module 195.
rejected_noop, missing_or_ambiguous_noop and invalid_time_noop preserve the full
state on failure. historical_wellFormed and historical_conservation preserve
nonnegativity and active + queued + confiscated + completed value.

transition_commutes proves that selecting any next membership cannot alter an old
certificate's debit. inter_epoch_replay preserves idempotence after that selection.
new_validator_reused_index_safety protects active funds, owned queue entries and
completed withdrawals for a subject outside the entire historical membership.
singleton_reused_index_safety needs only inequality with the one accused old owner.
The general sufficient condition is u_new not in the entire certified historical
B_global; unaccused_funds then preserves that subject's active funds, queue and
completed payouts. Being outside the historical membership is a stronger sufficient
condition used by the checked wrapper theorem. Inequality with one culprit alone
is insufficient if another historical culprit is the same subject: a regression
explicitly records this distinction. This is not an iff characterization of an
unchanged balance: an already processed key or zero liable funds can also give
no new debit for an accused subject.

reindex transports identity maps, weights and Byzantine membership along a local
permutation. permutation_globalBlame, identity_permutation_invariance and
permutation_stakeMap prove equal global certified sets, debits and stake maps.
This generic result operates on correspondingly transported certified offender sets;
it is not a separate proof of full checker equivariance for arbitrary wire formats.
A concrete permutation regression runs both real checkers successfully.

unbonding_slashing_cross_epoch_soundness proves strict confiscation for a resolved,
accepted historical offender with a fresh global key and positive current liable
funds, under WellFormed and timing/rate guards, regardless of next membership.
historical_deadline_precedence connects historical validation to the exact reduced
payout of a single liable tranche maturing on the inclusive deadline. Liability is
limited to h <= request time. The certificate must actually enter admission before
it closes; delivery of unseen evidence is not guaranteed.

## Regressions and Clean Water

Kernel-checked examples and independent executable observations cover an actual
reachable equivocation trace, index permutation, replacement of a departed owner,
changing local dimension, historical half/full slashing of queued funds, deadline
payout, replay after epoch change, missing/ambiguous/duplicate/out-of-range history,
bad dimension/envelope/reference, timing/rate/phase rejection and conserved totals.
Registry fixtures exercise the master integration.

Hierarchy: epsilon 196, gamma distributed, delta distributed/tendermint-accountability.
Public Git release v0.7.5 exports private snapshot
f6dfd6a47914d804b8fb248baf7ea1159912db89. Lake remains 0.7.1. Last full public
control remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1). Private evidence
is separate. Final commands and measurements are recorded in external public
evidence. Only propext, Classical.choice and Quot.sound are permitted.

Quorum overlap, lock handover, consensus safety/liveness during membership changes,
activation delays, authentication of history and stable IDs, deposits/redelegation,
clock authentication, network inclusion, concurrent execution, storage and reorgs
remain outside this contract. Python equivalence, JSON/SHA-256 and SimLab obligations
remain open. Mathematical novelty is not assessed.
