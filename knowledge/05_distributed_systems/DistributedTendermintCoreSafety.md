---
id: DistributedTendermintCoreSafety
language: en
section: distributed
source: Verification/DistributedTendermintCoreSafety.lean
source_sha256: 433f4006936e2ac5f5027de2261879a9249fe57956c683e6a798ef1e1ed45d95
novelty: not-assessed
status: reviewed
---

# Weighted Tendermint core safety

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintCoreSafety.lean)

## Model and exact scope

The model is a fixed-height, fixed-validator-set safety abstraction of Algorithm 1
in Buchman, Kwon and Milosevic, *The latest gossip on BFT consensus*, arXiv:1807.04938v3.
Values are natural-number block identifiers. `Config` contains the height, natural
validator weights and a fixed Byzantine set. A block identifier is an abstract
value; no hash collision resistance or application validity is proved.

`State` contains the immutable-history set of sent votes and local states with
monotonically advancing rounds, paired lock and valid (round,value) data, delivered
votes and delivered proposals. The paired representation prevents mismatched
round/value options; lockedRound, lockedValue, validRound and validValue are
projections. The sent-vote set is also the local voting-history source for checks.
It is ghost/global history for the safety model, not a required shared-memory service.

`Step` permits arbitrary proposal delivery, vote delivery from previously sent
messages, round advancement, honest votes and arbitrary Byzantine votes under
the Byzantine sender's identity. It permits omissions, duplicate deliveries and
arbitrary delivery order. Correct messages cannot be forged. This is an explicit
ideal authentication boundary, not a cryptographic signature proof.

Proposal selection, proposer rotation, timeout enabling conditions and application
validity are overapproximated. Nil voting and round advancement are nondeterministic.
`valid` is updated together with `lock` on a block precommit; the paper's separate
late validValue updates used for progress are omitted. No refinement equivalence
to the complete Algorithm 1 or a production Tendermint implementation is claimed.
The safety result holds for every execution of this more permissive safety model.

## Guards and executable correspondence

`proposalValid` checks the proposal round. A proposal without validRound requires
no lock or a lock on the same value. A proposal with validRound requires an actual
delivered prevote quorum at that round, strictly before the current round, and
no lock, a sufficiently recent certificate, or the same locked value. A stale
certificate for a conflicting value is rejected; an old certificate for the same
locked value can be accepted, as specified by the disjunction in Algorithm 1.

An honest signer emits at most one vote per (round,phase), including nil. A block
precommit requires an earlier own prevote in the current round and a delivered
prevote quorum for that block; it sets both lock and valid data. The own prevote
need not have voted for that block. Nil precommits leave the lock unchanged.
Byzantine senders may equivocate. Quorum weight is computed over a Finset of unique
signers, so copies of a message cannot increase voting power.

`execute` is computable. `execute_sound` and `execute_complete` connect it in both
directions to Step. Successful `run` traces are reachable. `executeAtHeight`
checks the external message height; a wrong height is rejected. Inside a Step/run
instance, messages are already scoped to the fixed Config height. Callers must
use the height guard when admitting external envelopes; cross-height reconfiguration
and untrusted configuration storage are not modeled.

## Theorems and proof structure

For W=sum weights, a quorum Q satisfies 2*W < 3*mass(Q). No quotient or rounded
threshold is used. `quorum_total_positive` excludes quorum formation at W=0.
`quorum_honest_intersection` proves a positive-weight honest member of the
intersection when 3*mass(Byzantine)<=W; the strict-bound specialization is provided.
The non-strict fault bound is deliberate: strict >2/3 quorums still intersect
honestly at exactly one-third Byzantine weight. A counterexample at equality
would therefore be false for these definitions. The regression instead constructs
a reachable conflict above the threshold.

`reachable_invariant` is proved by induction over Step. It derives honest vote
uniqueness, certified precommits, local round bounds, lock certificates, dominance
of every prior precommit round by the current lock round, and the key fact:
a later honest block prevote after a precommit at r0 is justified by a polka in
some round t with r0<=t<r. Neither State nor Step assumes agreement.

`same_round_polka_unique` and `same_round_commit_unique` use honest intersection
and vote uniqueness. `later_polka_unique` uses strong induction on the later round:
an intersecting honest signer provides an earlier certificate; induction or
same-round uniqueness rules out the conflicting value. `tendermint_core_safety`
therefore equates the values of any two commit certificates in a reachable state,
including different rounds. `locked_quorum_preservation` additionally proves that
honest signers of a commit retain its value at a lock round no smaller than the
commit round. Vote history is monotone along Step. `execution_safety` applies to
all admitted delivery orders; it does not assert identical outputs for different
nondeterministic executions.

`accountable_safety_contrapositive` says conflicting commits in a reachable state
require W<3*mass(Byzantine). This is not an extractor of signed fault evidence,
an identification algorithm or a slashing theorem. The imported earlier PBFT
arithmetic module is not used as an assumed cross-round safety theorem.

## Nonvacuity and validation

`nonvacuous_commit` contains an explicit reachable honest commit with positive
total weight and the strict fault bound. The regression file adds 42 examples and
seven named lemmas, plus 29 compiled scenarios: unequal/zero weights, exact
one-third boundary, strict quorum thresholds, one- and two-round commits, nil
lock retention, Byzantine equivocation, unauthenticated votes, stale/future/bare
certificates, wrong height, duplicate delivery, reordered delivery and rejection
of a conflicting later proposal. A second reachable trace commits values 7 and 8
in different rounds when two of four equal-weight signers are Byzantine.
Synthetic local certificate examples test guards; they are not all asserted
reachable. All proof examples are kernel checked without native_decide.

Measured project results are recorded in tools/validation_snapshot.json.
Source baseline: dde32ddfddd35b3093481ee95a6627383ee1a9c2.
Only propext, Classical.choice and Quot.sound are permitted.

## Open obligations

No liveness/GST/fairness, dynamic validator membership, signature implementation,
network stack, application validity, economic slashing or evidence extraction is
proved. Bulletproofs knowledge extraction, binding, HVZK and Fiat-Shamir/ROM,
and Python, JSON/SHA-256 and SimLab correspondence remain open. Novelty is not assessed.

References: [Algorithm 1 and safety argument](https://arxiv.org/pdf/1807.04938v3),
[separate classic and accountable safety proofs](https://docs.tendermint.com/master/spec/ivy-proofs/).
