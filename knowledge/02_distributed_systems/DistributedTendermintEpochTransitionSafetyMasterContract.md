---
id: DistributedTendermintEpochTransitionSafetyMasterContract
language: en
section: distributed
source: Verification/DistributedTendermintEpochTransitionSafetyMasterContract.lean
source_sha256: f904ef453c8e2103aaa77b9db5a785b31e3ca17f5d8cda7aea1f71f1d80926c2
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintEpochTransitionSafetyMasterContract.lean)

# Composite epoch-transition safety and accountable collection

Module 200 composes the checked components 179, 192, 194–199. Its direct import is
DistributedTendermintHandoverRoundInduction (199); the existing dependencies provide
historical attribution, stable IDs, quorum intersection, lock adoption and unbonding.
The result is a conditional composition, not unconditional safety or inevitable
physical punishment for every cross-epoch disagreement.

## Unified context and actual execution

EpochTransitionMasterContext contains the old/new identity-bearing configurations,
threshold mode, fault set, source polka/commit, adopted local states, target vote
transcript, history registry, unbonding ledger, window and rate. Consensus weights
and current slashable balances are distinct: a historical weight does not prove
that funds still exist. Historical resolution must select this exact old config.

initialState fixes the current config to the old epoch. debit performs the real
epoch_transition to the next config and applyHistorical using the source height
and actual Payload. pipeline then closes admission and finalizes matured withdrawals.
It does not advance the clock. Closing admission asserts completeness of the supplied
slot input; it does not deliver unseen certificates. The payload supplies neither
the historical identity map nor a caller-selected guilty set.

## Conditional safety

SafetyConditions lists the actual premises of module 199: accepted source polka,
linked source commit at the same height/value, old quorum, normalized new weights,
the matching honest-overlap bound, actual adoption, and honest prevote/precommit
history rules. cross_epoch_master_safety_branch proves Agreement for every target
round. Both strict >2/3 and non-strict >=2/3 semantics remain those of modules 197–199.
The result cannot be combined with a conflicting commit while retaining all these
premises. Failure of a premise is not automatically a slashable offence.

## Checked collection

AcceptedEvidence requires unique historical resolution and successful module-179
attribute_evidence on the actual reference/evidence. CollectionReady additionally
requires an open admission phase, h<=now<=h+window, 0<rate<=1, a nonnegative ledger,
and at least one certified local subject whose global (height,ID) key is fresh and
whose current liable holdings are positive. available includes active balance and
held queue tranches with h<=requested; exited or already paid funds are not assumed
available. Merely positive historical stake is insufficient.

cross_epoch_accountable_slashing_branch proves that the certified global set is
nonempty and the final confiscation pool strictly increases after the whole pipeline.
The current membership may exclude the offender entirely. master_deadline_payout
proves the exact reduced payout of a singleton liable tranche at the inclusive
deadline: completed + (1-rate)*amount. All statements execute the existing checked
historical path, not a raw externally chosen set of alleged offenders.

historical_fork_global_blame also connects actual conflicting commits in ONE
historical configuration, with EvidenceSufficiency, to the module-179 checker and
a nonempty global blame set. It does not apply that same-configuration theorem to
two different epoch weight systems. The complete reference and authentication are
external premises already exposed by module 179.

## Protection and conservation

cross_epoch_innocent_index_reuse_protection assumes absence from the ENTIRE accepted
global set. It preserves active stake and total subjectValue (active + owned queue
+ completed withdrawals) through the pipeline. Queue bytes and completed totals
may change because an honest withdrawal is paid; this is not a loss. Distinctness
from only one previous index owner does not establish innocence.

pipeline_conservation preserves total active stake + queue + confiscation + completed
withdrawals. pipeline_wellFormed preserves nonnegativity. Duplicate certificate
submission before settlement gives the same settled result by replay protection;
after settlement the closed admission phase rejects it. The combined theorem is
cross_epoch_master_value_conservation_and_idempotence. It does not claim that a
clock-advancing multi-slot execution is idempotent.

## Exact status of the safety-or-collection theorem

ConflictCovered is an explicit additional integration obligation: for each conflicting
target commit, a payload/set satisfying CollectionReady is supplied at this snapshot.
cross_epoch_safety_or_slashing_dichotomy proves Agreement OR existence of that
checked collectible certificate and strictly positive pipeline confiscation.
This OR is inclusive: safety and collection for another certified offence can coexist.

The theorem does NOT derive ConflictCovered, extract a cross-epoch offence from an
arbitrary disagreement, prove that a supplied historical offence caused that particular
conflict, establish receipt before the deadline, or guarantee retained funds. Those
are not consequences of modules 179 or 197–199. The explicit premise prevents a
vacuous claim of unconditional accountable safety. uncovered_expired_conflict proves
that a conflicting history with an expired window cannot satisfy ConflictCovered;
expired_debit_noop and expired_collection_impossible expose the boundary directly.

## Concrete witnesses and checks

Tests exercise a safe transition with nonzero total variation 1/4 and common honest
mass 3/4; round-zero and later commits; real historical equivocation; an offender
who leaves the new set and queues 8 units; half-slashing at the deadline (4 collected,
4 paid); full confiscation; a replacement index owner retaining 12 units; honest
queued funds paid intact; duplicate certificates before and after settlement; late,
future, closed-phase, stale-key, zero-holding, missing/ambiguous-history, wrong-height
and missing-reference cases. A pre-request tranche is not charged for a later offence.
A same-configuration fork exercises the attribution bridge. A concrete conflicting
history with timely evidence supplies the second branch; the late variant proves
coverage unavailable instead of pretending collection still follows.

Delivery, asynchronous network/clock behavior, signatures, authenticated configuration
history, complete reference provenance, liveness, production refinement, Python,
JSON/SHA-256 and SimLab remain open. Novelty is not assessed. Allowed axioms are only
propext, Classical.choice and Quot.sound.

Hierarchy: epsilon 200; gamma distributed; delta distributed/tendermint-accountability.
Public release v0.7.9 exports private snapshot
831248e509744e9a7900fa0cc7f01a88ee957b2f. Lake remains 0.7.1. Public-tree verification
is recorded separately from private checks. The full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); private full control remains
090aed141b831aee5182197e9ea205176f361c0f. See [release notes](../../docs/release-v0.7.9.en.md).

[ε202: checked header chains provide historical resolution under explicit trust and commit-consistency premises; signature authenticity and complete offence references remain external.](DistributedTendermintHeaderChainEpochAuthContract.md)
