---
id: DistributedTendermintSlashingPenaltyContract
language: en
section: distributed
source: Verification/DistributedTendermintSlashingPenaltyContract.lean
source_sha256: 3d933dfd6ee791b4dc0aac29baa8007aa55bfdeb130e57df97543d874269644b
novelty: not-assessed
status: reviewed
---

# Deterministic slashing from a certified Tendermint offender set

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintSlashingPenaltyContract.lean)

## Model

Module 192 uses a finite validator type, nonnegative rational stake w and a finite
certified set B. The uniform rate satisfies 0 < alpha <= 1. For v in B, the new
stake is (1-alpha)*w(v); other balances are unchanged. Rational arithmetic is exact:
there is no integer rounding or minimum currency unit. Algebraic identities hold
more generally; each theorem states exactly which rate/positivity bounds it needs.
A zero residual balance is permitted and required by full confiscation.

The actual local dependency is module 179, DistributedTendermintAccountableSafety,
which imports module 165, DistributedTendermintCoreSafety. There is no local
DistributedTendermintForkAccountability module. The stable catalog direction ID
is `distributed`; this work does not rename that direction.

## Proven statements

- `non_faulty_stake_invariant`: a validator outside B retains its balance.
- `slashing_nonnegative`, `slashing_le_initial`: nonnegative and nonincreasing
  balances under the corresponding rate bounds.
- `confiscated_eq`: the exact confiscation is alpha * mass(B).
- `slashing_conservation`: remaining total plus confiscation equals initial total.
  This is accounting, not an allocation mechanism for a treasury or auction.
- `faulty_mass_strict_decrease`: positive culprit mass and positive rate imply
  strictly decreasing culprit mass. Nonempty B alone is insufficient.
- `slashing_lower_bound`: mass(B) > W/3 gives confiscation > alpha*(W/3).
- `relative_honest_dominance_increase`: positive complementary mass and positive
  confiscation give a strictly larger complementary share. Both denominators are
  proved positive; zero-total division is not given an economic interpretation.
- `honest_quorum_preserved`: a strict complementary two-thirds quorum remains
  strict. A quorum > 2W/3 and complementary culprit mass > W/3 cannot hold together;
  `threshold_and_honest_quorum_incompatible` makes that boundary explicit.
- `protected_share_strict_increase`: the same increase holds for any positive
  protected subset disjoint from B, including the actual honest validators.

`honestWeight` denotes the complement of B, not proof that every unaccused
validator is honest. `certified_honest_stake_invariant` and
`certified_honest_share_increase` instead use Reachable and the actual
Config.byzantine complement, via module 179's checked no-framing theorem.

`stakeOfConfig` embeds natural voting weights into rationals exactly.
`checked_slashing_lower_bound` takes a successful `attribute_evidence` result
and two conflicting commits in that evidence view; it derives the strict
confiscation bound using module 179, rather than assuming a threshold certificate
unrelated to the attribution algorithm. `slashEvidence` propagates rejection for
missing references, incomplete coverage or invalid evidence. It accepts a raw
rate parameter; rate safety is a theorem precondition, not a runtime rate check.

## Regression coverage

Kernel examples cover half-rate and full confiscation, exact conservation,
unchanged unaccused balances, rational fractions 2/5 to 4/7, an independent honest
supermajority case 4/5 to 8/9, empty B, zero weights, and the exact one-third
boundary. Counterexamples expose invalid rates, missing honest mass, zero loss
and repeated partial application. A concrete executed reachable trace has
conflicting commits and successfully checked B={0}; the certificate bridge and
actual honest-share theorem are applied to it. Four registry projections and
14 executable Boolean scenarios supplement the examples. Execution is not a
substitute for the kernel proofs. The test runner checks the entire output list.

## Clean Water and limits

This is one deterministic penalty application at a fixed height, conditional on
module 179's authenticated complete reference and checked relative coverage.
It does not implement digital signatures, obtaining the reference, dynamic
unbonding, evidence deadlines, slashing transactions or pool distribution.
Finite sets deduplicate identities within one application. Applying a partial
penalty twice is NOT idempotent; a persistent per-height replay ledger remains
an explicit separate obligation. No liveness, economic incentives or deployed
Tendermint/CometBFT equivalence is claimed. Python equivalence, JSON/SHA-256 and
SimLab obligations remain open. Novelty is not assessed.

## Verification scope

Epsilon 192 in `distributed/tendermint-accountability`. The public v0.7.1
synchronization includes trusted verification-tool changes, so its acceptance
requires one full beta control on the final public tree. This is separate from
the prior private scoped module evidence. Historical beta 7 / v0.7.0 is immutable.
See [release scope](../../docs/release-v0.7.1.en.md) for the distinction between
change rank and executed validation scope. Lake cache is retained.

[Module 194](DistributedTendermintSlashingReplayProtection.md) adds a sequential per-height replay ledger; durable storage, authenticated height context and concurrent execution remain separate obligations.
