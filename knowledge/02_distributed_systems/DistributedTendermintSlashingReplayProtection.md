---
id: DistributedTendermintSlashingReplayProtection
language: en
section: distributed
source: Verification/DistributedTendermintSlashingReplayProtection.lean
source_sha256: 4471567e628d1fb6bfa558fafaee04171776c34efb4eb9aafc9b077b33eef307
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintSlashingReplayProtection.lean)

# Sequential slashing replay protection

## Proven model

Module 194 extends module 192 with SlashingLedgerState: rational balances,
a cumulative confiscated pool and a finite set of (Nat height, validator) keys.
WellFormed means nonnegative balances and pool. Nonnegativity is an invariant,
not an assumption silently built into subtraction. Fin n keeps validator identities
stable throughout a request sequence.

freshOffenders filters the certified set against processed keys. applyCertifiedSet
is the internal algebraic update: module 192's stakeSlashing on fresh validators,
addition of the exact confiscated amount, and union with only the fresh keys.
If there are no fresh keys, the entire state is unchanged. This internal function
assumes its set has already been certified; it is not a replacement for validation.

applySlashingCertificate is the checked boundary. It calls module 179's
attribute_evidence with Config, an optional authenticated complete reference and
EvidenceView. It never accepts an arbitrary caller-supplied offender set. The key
uses Config.height, the same height checked against signed evidence envelopes.
Invalid evidence, missing/insufficient reference and rates outside 0 < alpha <= 1
leave all three state fields unchanged. Zero rate is rejected to avoid consuming
keys without applying the configured penalty. The intended policy fixes the rate;
a later different valid rate cannot re-charge an already processed key.

## Theorems

- replay_idempotence: repeating the checked certificate leaves the resulting state unchanged.
- checked_same_offenders_noop: different accepting certificates with the same offender set at the same height also leave the whole resulting state unchanged.
- overlapping_certificates_no_double_slash and checked_overlap: a validator in the first certified set retains its post-first balance during a second certificate at the same height. This also covers already processed initial keys; a positive debit is not guaranteed for zero balances.
- invalid_certificate_noop and invalid_rate_noop: rejected input cannot poison the key ledger or change its pool.
- balances_nonnegative and checked_wellFormed: nonnegative balances and pool are preserved under their stated rate assumptions; the checked wrapper enforces them.
- total_stake_conservation and checked_conservation: total balances plus the cumulative pool are invariant. The pure identity itself does not require positivity.
- matches_stateless_penalty and checked_first_step: initially empty processed keys give exactly module 192's operator on current balances.
- checked_honest_balance: actual honest validators are protected when the reference is a reachable history, using module 179's attribution theorem.
- processed_after describes exactly which keys are inserted; processed_monotone and run_processed_monotone show no keys are forgotten.
- run_conservation and run_wellFormed lift accounting and nonnegativity to every finite sequential list of checked requests.

## Policy boundaries

The policy is at most one application per (height, validator), not per certificate
hash, transaction ID, round or offence category. A second distinct offence by the
same validator at the same height is deliberately included in that one-penalty
policy. A different height permits another penalty. Zero-balance validators still
consume their keys on accepted evidence. Pre-existing processed keys are trusted
state; this model does not prove that they encode an authentic past history.

Height/configuration authenticity, complete-reference acquisition and stable
validator identity are external obligations. Numeric indices must not be reused
for another validator without a separately proved identity/epoch mapping.
Atomicity here is one pure state transition, not a theorem about concurrent
transactions, locks, database durability, crash recovery, chain reorganizations,
unbonding, deadlines or deployed Tendermint/CometBFT code. The module does not
remove keys or distribute the confiscated pool. Replay-filtered sets need not
retain module 192's original > one-third confiscation bound; a complete replay
correctly confiscates zero.

## Regressions and verification

Independent exact rational expectations cover repeated and distinct certificates,
partially overlapping blame, empty blame, partial/full confiscation, invalid rates,
wrong heights, unavailable/incomplete references and forged messages. Accepted
blame is computed by the actual module 179 checker. An executable reachable trace
realizes a nonempty accepted set. A mixed request sequence exercises preservation;
the old stateless operator is exhibited charging twice as a contrast witness.
Kernel proofs and executable scenarios are reported separately in external evidence.

Hierarchy: epsilon 194, gamma distributed, batch distributed/tendermint-accountability.
Private parent f2d792cb7b4ebbe6f4e1cb973e8a7e4d4b51cbbe; historical beta 7 and the
last full private control 090aed141b831aee5182197e9ea205176f361c0f remain unchanged.
Public checks are separate from private evidence; the last full public basis
remains v0.7.1. The public planner selects actual verification scope.
Only propext, Classical.choice and Quot.sound are permitted. Python equivalence,
JSON/SHA-256 and SimLab remain open. Novelty is not assessed.
