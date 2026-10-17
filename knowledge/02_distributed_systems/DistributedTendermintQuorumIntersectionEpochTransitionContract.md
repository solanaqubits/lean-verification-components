---
id: DistributedTendermintQuorumIntersectionEpochTransitionContract
language: en
section: distributed
source: Verification/DistributedTendermintQuorumIntersectionEpochTransitionContract.lean
source_sha256: 86f58e695f3e481689ad5bdae7ec1e87ca43eef57c342753beee5cd79b9d9ef7
novelty: not-assessed
status: reviewed
---

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTendermintQuorumIntersectionEpochTransitionContract.lean)

# Weighted honest quorum intersection across epochs

## Model and exact criterion

Module 197 concerns finite global validator identities, rational weights and finite
sets. V has Fintype and DecidableEq; a finite set of global IDs can be represented
by its subtype. Normalized w means pointwise nonnegativity and total mass 1.
The two epochs may have different weights, totals before normalization, membership
sizes and zero-weight subjects. isQuorum w q Q uses the non-strict condition
q <= mass w Q. The algebraic lemmas hold for arbitrary rational thresholds; meaningful
applications use 0 < q <= 1. B is a supplied common fault set; being outside B is
what “honest” means here. With separate fault sets use their union to require
honesty in both epochs. The model does not discover or authenticate actual faults.

Let mu(v)=min(w(v),z(v)), H=sum over v outside B of mu(v), and
I=(Q intersect R) minus B. complement_cover bounds H by mu(I) plus the w-mass
outside Q and the z-mass outside R. Complements need not be disjoint.
quorum_intersection_weight_bound proves:

    mu(I) >= H + q + r - 2.

honest_node_in_intersection therefore needs H > 2-q-r for non-strict quorums.
It supplies a shared ID outside B with strictly positive weight in BOTH epochs,
not merely a zero-weight ID included in both sets.

## Variation, directed loss and threshold distinctions

variation w z is exactly one half of the sum of absolute pointwise differences.
common_variation_identity proves total common mass = 1 - variation.
honest_common_identity proves H = 1 - variation - mu(B). Thus the sharper criterion is

    variation + mu(B) < q+r-1.

variation_weight_bound states the corresponding quantitative bound; variation_sufficient
proves existence. two_fault_masses_sufficient also proves the originally proposed
stronger criterion w(B)+z(B)+variation < q+r-1, using mu(B)<=w(B) and z(B)>=0.
This sufficient condition is conservative: it double-counts potential fault mass
and does not specialize to the optimal static one-third bound.

honestLoss w z B is explicitly sum over v outside B of max(w(v)-z(v),0).
honest_loss_identity proves H = 1 - w(B) - honestLoss. Hence

    w(B) + honestLoss < q+r-1

is an equivalent form of the sharp common-mass sufficient condition. For q=r=2/3
it becomes w(B)+honestLoss < 1/3. This directed loss is not an unspecified shift
and is not automatically equal to total variation; it is restricted to honest IDs.

static_epoch_equivalence proves variation w w=0 and H=1-w(B).
static_epoch_specialization gives honest intersection for non-strict 2/3 quorums
and w(B)<1/3. strict_tendermint_intersection instead assumes each quorum's weight
is strictly greater than 2/3 and permits H>=2/3, including equality. These two
boundary conventions are deliberately not conflated.

## Normalization and integration with existing modules

normalize divides by total mass. normalize_normalized requires nonnegative raw
weights and a strictly positive total; division-by-zero in the field is not a
valid probability model. normalization_scale_invariant proves invariance under
positive scaling. Global epochWeights normalizes module 196's stakeMap, retaining
its historical natural consensus units and rational normalized output.
epoch_reindex_invariance inherits exact global stake-map invariance under local
permutations. epoch_quorum_intersection handles two epoch configurations of
possibly different local dimensions; epoch_shared_subject additionally proves
that the witness belongs to both active ID sets. There is no hidden requirement
that balances or total voting units remain constant between epochs.

legacy_quorum_equivalence proves that normalized weight >2/3 is exactly module
179's inherited Config.quorum predicate 2*total < 3*mass, when total is positive.
static_legacy_specialization derives the existing natural-weight honest-intersection
conclusion from the NEW normalized theorem, with 3*faultMass <= total. It does not
assume the old intersection conclusion as an axiom or substitute it for the proof.

## Counterexamples and regression scope

insufficient_overlap_counterexample gives normalized distributions on four IDs
with TV=1/3, no faults and disjoint non-strict 2/3 quorums. strict_overlap_counterexample
gives TV=2/5 and disjoint strict quorums of weight 7/10, again with no faults.
Kernel-checked examples also show the static fault-bound equality failure for
non-strict quorums, a valid strict equality case, zero total and negative-weight
rejection, independent rescaling, a real legacy Config, changing epoch dimension,
and ID reindexing. A separate example shows the sufficient overlap criterion is
not necessary for every distribution: lower common mass can still force a shared
heavy subject. Executable observations use exact rationals, not floating point.

Hierarchy: epsilon 197; gamma distributed; delta distributed/tendermint-accountability.
Public Git release v0.7.6 exports private snapshot
137f851a246a72e6a7d9c621e0f016ddc9bdb3cb. Lake remains 0.7.1. The last full public
beta basis remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1). Private
full control 090aed141b831aee5182197e9ea205176f361c0f and private scoped evidence
remain separate. Final commands and measurements are recorded in external public evidence.

Only propext, Classical.choice and Quot.sound are allowed. This proves weighted
set intersection, not agreement of the witness's votes or protocol safety across
epochs. Lock transfer, round synchronization, polling/commit semantics, authentication
of headers/configurations/identities, fault-set truth, activation, network behavior,
production implementation, Python equivalence, JSON/SHA-256 and SimLab remain
external obligations. Mathematical novelty is not assessed.
