---
id: DistributedTendermintHandoverRoundInduction
language: en
section: distributed
source: Verification/DistributedTendermintHandoverRoundInduction.lean
source_sha256: fb596bc61caac49c863a43829740f3f96bf5d2d5740f39a69cce0d038d121cfc
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintHandoverRoundInduction.lean)

# Conditional agreement in every target round after handover

Module 199 proves conditional agreement for every natural-number round of one
fixed target epoch at the same decision height as the source commit. It imports
module 198, reusing its certificates, epoch identity, quorum convention, adoption
and local transition API, and the weighted intersection theorem from module 197.
It does not assume agreement as a field of an admissible history.

## Finite history and honest anchor

Transcript contains a target epoch, height and finite set of CoreSafety.Vote
records. Observed checks the envelope and a quorum of signers filtered by phase,
round and value through the actual epoch injection. Polka uses prevote; Commit
uses precommit. Duplicate records do not increase weight. Nil is not a vote for a
concrete value. Chain identity and the provenance of the envelope are external.
The theorem quantifies over all natural rounds for any such finite history;
it does not require a preselected bound on the last round.

inheritedSigners filters the historical commit signers to non-Byzantine global
subjects whose state equals the actual inherited lock. Hits requires that EVERY
possible target quorum contains an anchor member. inherited_signers_hit_every_quorum
derives this universal property from normalized weights, a checked source polka,
an old commit quorum, module 197's overlap criterion and module 198's Adoptions.
The latter is actual receipt/adoption, not an automatic consequence of honesty.
Only one honest witness per candidate quorum is needed, not a quorum-sized honest
intersection. Empty anchors fail Hits for a genuine nonempty quorum.

Threshold.weak remains >=2/3, requiring common honest mass >2/3; Threshold.strict
remains >2/3, permitting common honest mass >=2/3. The old CoreSafety API uses the
strict convention. Target weights/configuration are fixed throughout the history.
The fault set must cover the relevant faults in both epochs; identity stability
alone does not justify assumptions about future honest behavior.

## Rules and induction

HonestPrevotes applies to anchor signers: a non-nil vote for x different from the
inherited value v must have a Polka(t,x) with t < the vote round in this SAME
transcript/context. EarlierPolka uses the finite range of strictly earlier rounds.
HonestPrecommits requires a same-round Polka for every non-nil anchor precommit.
It is an implication only: a Polka does not force execution of a precommit.

no_conflicting_polka_by_well_founded_induction uses strong induction on the round.
A hypothetical conflicting Polka has an anchor signer by Hits. Its vote requires
an earlier conflicting Polka, contradicting the induction hypothesis. At zero
there is no earlier natural round. precommit_requires_polka_lemma obtains an
anchor precommitter with the SAME universal intersection property; its honest
rule supplies the same-round Polka. all_rounds_agreement follows.

cross_epoch_arbitrary_round_safety links this result to an accepted source polka
and source commit at the source epoch and same decision height, with identical
source values. It concludes that any target commit equals that source commit.
It does not derive the old polka/commit pair from a complete old execution.
round_zero_specialization recovers round-zero agreement under the stronger global
history rules; module 198's round-zero theorem remains valid under its own weaker
local premises and is not claimed to have an equivalent hypothesis set.

## Bridge to local executions

Registered checks the certificate's epoch/height against the transcript and that
its actual vote records are included. registered_replacement_polka proves that a
MayReplace certificate registered this way supplies a real transcript Polka:
nonnegative weights make quorum membership monotone under inclusion of votes.

RecordedReachable refines module 198's finite advance/replace execution by requiring
Registered for every replacement. recorded_reachable_refines proves the refinement.
recorded_value_origin proves by induction that the current value is the initial
one or has a transcript Polka strictly before the current round. The proof uses
monotone round advancement and the strict upper bound on replacements.
recorded_prevote_rule combines this result with the actual emit guard to derive
the required earlier-Polka rule for a changed non-nil prevote.

This is a per-vote bridge. To apply the global theorem to a production execution,
each relevant vote must be linked to such a local run starting with the adopted
lock, and honest precommit certification must separately hold. Module 198's emit
guard alone does not establish precommit certification. This module does not
silently treat an externally supplied certificate as a member of the transcript.

## Non-vacuity and counterexamples

Regression fixtures contain a concrete adopted lock, a finite honest history with
Polka/commit at rounds 0, 1 and 3, nil at round 2, genuine local advance/replacement
traces and applications of both threshold conventions and the cross-epoch theorem.
They reject foreign epoch/height, absent certificate records, empty anchors and
same/future-round replacement witnesses, and check repeated vote-set invariance.

uncertified_precommit_counterexample has a full honest anchor and no conflicting
prevotes, but a commit for 9 instead of the inherited 7 with no corresponding Polka.
It violates only the required precommit-certification condition in that example.
nonstrict_round_counterexample has a conflicting Polka/commit in round 1 and
satisfies the weakened t<=r prevote rule by self-justification; the strict rule fails.
A locally valid alternative replacement using that transcript is also exhibited:
local success is not confused with a globally admissible history.

## Clean Water and validation

The result is conditional safety for one fixed target epoch/height, not liveness,
full asynchronous protocol refinement or secure delivery. Signatures, authenticated
chain/configuration history, physical clocks, timeouts, leader rotation, activation,
changing weights inside an epoch and production code remain open. Every extended
history needs the rules again; mere transcript extension does not preserve them.
Python, JSON/SHA-256 and SimLab obligations remain open. Only propext,
Classical.choice and Quot.sound are permitted. Novelty is not assessed.

Hierarchy: epsilon 199; gamma distributed; delta distributed/tendermint-accountability.
Public Git release v0.7.8 exports private snapshot
22b05f8b488cefef74da97a60474f74260bd63c4. Lake remains 0.7.1. The last full public
beta basis remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).
Private full control 090aed141b831aee5182197e9ea205176f361c0f and scoped evidence
remain separate. Final commands and measurements are recorded in public evidence.

[Module DistributedTendermintEpochTransitionSafetyMasterContract](DistributedTendermintEpochTransitionSafetyMasterContract.md) composes this result under explicit additional premises; no unconditional authentication or collection guarantee is added.
