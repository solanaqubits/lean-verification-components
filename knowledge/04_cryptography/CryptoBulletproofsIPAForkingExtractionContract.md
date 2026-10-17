---
id: CryptoBulletproofsIPAForkingExtractionContract
language: en
section: cryptography
source: Verification/CryptoBulletproofsIPAForkingExtractionContract.lean
source_sha256: c78ac695644168d667ab85724bedc05dfe004ca933405c09de51cff10b65ba87
novelty: not-assessed
status: reviewed
---

# Finite shared-prefix IPA fork acquisition

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsIPAForkingExtractionContract.lean)

## Exact scope

This module constructs four distinct-square accepting branches from a finite
collection of responses to challenges at a fixed IPA prefix. It reuses
`CryptoBulletproofsTreeExtraction` for the algebraic witness-or-relation result;
it does not introduce another folding protocol or repeat its recursive proof.

Over a field, any square has at most two roots. For a finite set A of distinct
nonzero accepting challenges, |A| ≤ 2 |square(A)|. Thus |A| ≥ 7 guarantees at
least four distinct squares. The direct condition |square(A)| ≥ 4 also suffices.
Counting repeated queries is insufficient: the bound counts distinct challenges.
Zero is removed before applying the threshold. In characteristic two the same
upper bound remains valid, although it need not be sharp.

The prefix contains the expected statement and shared L,R message. Children
are checked against the statement computed by folding these exact generators
and updating this exact target for the selected challenge. Independent completed
proofs with unrelated prefixes cannot be combined using this contract.

## Checked API

`square_fiber_card_le_two` and `card_le_twice_square_classes` establish the
finite counting argument; `four_square_classes_iff_fork` gives the exact class
criterion. `selectFork` enumerates quadruples from a finite list and selects the
first injective square map. This helper concerns distinct squares only; the
protocol wrapper `acceptedChallenges` also excludes zero and failed replies.
`selectFork_success_iff` connects the executable selection to the class count.

`FiniteOracleTree` contains raw scalar leaves or nodes with a shared message,
finite call list and challenge-indexed children. `acquire` validates contexts
and descendants before selecting branches. `OracleReady` is an independently
recursive coverage check; `acquire_success_iff` proves its equivalence to
successful acquisition. `sevenReady_implies_ready` proves the sufficient
seven-distinct-nonzero-challenge condition recursively at every counted node.
`acquire_sound` supplies the existing `ValidAcceptingTree` predicate, and
`checked_forking_extract` calls the existing checked extractor.
`finite_forking_dichotomy` states the returned witness-or-relation alternative.
The exhaustive selector and recursive validation have no asserted efficient
rewinding or expected-time bound.

## Recursive composition

The finite response tree supplies possible child responses at every node.
The coverage condition must hold recursively: enough successful top-level
challenges alone does not guarantee enough descendants. Leaves satisfy the
existing scalar equation. Selection constructs the existing four-ary transcript
tree, after which the existing extractor returns either vectors a,b satisfying
P = MSM(a,G) + MSM(b,H) + dot(a,b) U, or an explicit nonzero coefficient tuple
whose combination of the original G,H,U is zero.

The first alternative is a valid witness, not a claim that an arbitrary prover's
private input has been recovered. Equality with an original witness needs an
honest-generation premise. The relation alternative remains valid even when
another witness also exists.

## Boundary and limitations

Over ZMod 101, the six nonzero challenges ±1, ±2, ±3 have only three square
classes. They cannot furnish four distinct squares. Seven is a sharp uniform
cardinality threshold in fields admitting this example; smaller fields can lack
enough nonzero square classes altogether.

Availability of the finite responses and preservation of the prover's common
pre-challenge state are explicit model inputs. No physical rewind mechanism,
Heavy Rows success probability, general Bellare–Neven forking lemma, expected
polynomial running time, Fiat–Shamir random-oracle security, computational
binding, discrete-log hardness or zero knowledge is proved. Pedersen blinding
and an independently supplied dot(a,b)=c are outside this IPA interface.

Novelty is not assessed. Only propext, Classical.choice and Quot.sound are permitted.

Public release v0.7.10 synchronizes private snapshot
5779d30ff6419ee91f787d04f45f3d3b5d483e55. Lake remains 0.7.1. Public validation
is recorded separately; the full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).
See [release notes](../../docs/release-v0.7.10.en.md).
