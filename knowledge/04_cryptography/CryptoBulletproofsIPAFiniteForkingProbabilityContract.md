---
id: CryptoBulletproofsIPAFiniteForkingProbabilityContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAFiniteForkingProbabilityContract.lean
source_sha256: 8b412930f9c4112d1c545dc3e8f92925c923a615630346381bfeaf88e39510c2
novelty: not-assessed
status: reviewed
---

# Finite probability of an IPA fork

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAFiniteForkingProbabilityContract.lean)

## Question and model

The preceding module proves existence of four distinct-square accepting challenges
from seven distinct nonzero accepting challenges. This module quantifies a different
experiment: fix the prover state and common prefix, then sample four independent
uniform challenges with replacement from a finite nonempty set C. A subset A of C
records accepting responses. N = |C| and m = |A| count distinct elements, not calls.
`remaining` removes the entire square class of the last draw. `successes A n`
enumerates ordered lists of n accepted draws with pairwise distinct squares.
`mem_successes` proves this characterization. `samples` enumerates all ordered
outcomes, and `card_samples` proves its cardinality N^n. Thus dividing the success
count by N^4 is precisely the specified finite uniform experiment.

The counting lemmas work over any field, even if A contains zero. For protocol
composition, `replySet` reuses the prior module's `acceptedChallenges`, removing
zero and absent replies. A ⊆ C and nonempty C are needed to interpret the ratio as
a probability in [0,1]; `probability_le_one` records this explicitly.

## Counting and probability

Each square class removes at most two elements, by the existing square-fiber lemma.
Disjoint first-element extensions give a recurrence for the count. Induction proves
`success_count_lower`; at depth four `four_count_lower` yields
m(m−2)(m−4)(m−6), with natural truncated subtraction. `lowerCount_mono`
justifies replacing each remaining set by its guaranteed minimum size.

For m ≥ 6, `fixed_prefix_probability_lower` explicitly transports the natural
bound into rational subtraction and divides by N^4. `seven_probability_positive`
proves strict positivity for m ≥ 7. This is a lower bound, not an exact count:
{±1,±2,±3,4} over Q has 192 successes, while the lower count is 105.
The six-element set {±1,±2,±3} has zero successes.

## Averaging over prefixes

For a finite nonempty uniform set S of fixed prefixes, let p_s = |A_s|/N and
pbar = average p_s. For θ < 1, `heavy_prefix_fraction_lower` proves
Pr[p_s ≥ θ] ≥ (pbar−θ)/(1−θ). It bounds each heavy row by 1 and each other row by θ.
The general lemma only requires row upper bounds; actual acceptance rates also
satisfy nonnegativity. The lower bound may be negative and then gives no positivity.

Let f_N(t)=t(t−2/N)(t−4/N)(t−6/N). On t ≥ 6/N it is nonnegative and monotone.
`average_forking_probability_lower` gives the lower bound
((pbar−θ)/(1−θ)) f_N(θ) for the two-stage experiment, provided 6/N ≤ θ < 1.
`average_forking_probability_positive` makes it strictly positive under
6/N < θ < pbar and θ < 1. `average_probability_eq_count` identifies this average
with the joint ordered-outcome count divided by |S|N^4. There is no guarantee
for every prefix from its mean alone: one empty and one fully accepting row
already provide a counterexample.

## Extraction interface and limits

`sampled_success_isFork` converts an actual successful four-draw outcome to the
existing IsFork predicate. `sampled_fork_extracts` constructs the existing tree
using these exact sampled challenges and the common statement/message. Every
counted child response must be a completed ValidAcceptingTree for its independently
computed child statement. `positive_probability_extracts` and
`finite_probability_dichotomy` then reuse the existing extractor: a valid witness
OR an explicit nonzero generator relation. This is not necessarily recovery of
the prover's original private input, nor an independent external dot(a,b)=c claim.

The proof is a finite, conditional counting result. One-node success does not
establish recursive descendant availability or a whole-tree success probability.
Authentic rewind execution, adaptive oracle queries, the general probabilistic
Forking Lemma, Fiat–Shamir/ROM security, expected polynomial extraction time,
computational binding, Pedersen blinding and zero knowledge remain outside scope.
No new HCTK model, numerical experiment or physical claim is introduced.

## Evidence

The Suite is integrated into CryptoFullSuite and audited through MasterSuite.
Kernel regression examples and executable cases distinguish six/seven challenges,
repeated/opposite challenges, absent/zero replies, heavy-prefix averages and the
valid-child bridge. Public-tree validation is recorded separately in the annotated
v0.7.11 tag and release evidence. Only propext, Classical.choice and Quot.sound
are allowed. The private source snapshot is
8886170c4e32df5bb9bd0df700fdff4a029a4c91. Novelty is not assessed.
See [release notes](../../docs/release-v0.7.11.en.md).
