# v0.7.8 — Conditional all-round Tendermint handover agreement

Public release in solanaqubits/leanbook, synchronizing epsilon module 199 from
leanbook-private snapshot `22b05f8b488cefef74da97a60474f74260bd63c4`.
All 243 project Lean sources, including Verification.lean, match that snapshot.
MasterSuite contains 199 direct imports. Integration, selected tests, declarative
batch metadata and English documentation are included. Epsilon 200 remains free.

## Verification and version identity

Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`, delta
`distributed/tendermint-accountability`, epsilon 199. Git v0.7.8 is a publication
serial, not a new full checkpoint. Lake remains 0.7.1. The executable verification
tools and build configuration are unchanged; the public planner determines scope.

The full public beta basis remains `2419489245019fb16e32ffac641b9f88eea94126`
(v0.7.1); the last full private control remains
`090aed141b831aee5182197e9ea205176f361c0f`. Public and private evidence remain separate.
Historical tags are unchanged. Public validation uses one transitive audit of the
maximal required scope, strict compilation and selected live tests with cache retained.
Exact commands, measured results and evidence digest accompany the annotated tag
and external report after validation.

## Proven result

A finite Transcript supplies actual CoreSafety.Vote records within a fixed target
epoch/height envelope. Polka is a prevote quorum, Commit a precommit quorum. Signers
are computed through the stable epoch identity map; duplicate records add no weight.
The inherited honest anchor meets every possible target quorum by the weighted
criterion of module 197 and actual lock adoption from module 198. One honest shared
signer per candidate quorum is enough. Both strict and non-strict quorum conventions
retain their respective honest-overlap boundaries.

An honest anchor prevote for a value different from the inherited value requires
a strictly earlier Polka for that value in the same transcript and context.
Strong induction excludes a first conflicting Polka. Honest precommit implies a
same-round Polka; the converse is neither required nor assumed. Thus every target
commit in every natural-number round agrees with the linked source commit at the
same decision height, under the explicit history and handover premises.

Registered checks certificate context and inclusion of its actual votes in the
transcript. RecordedReachable refines module 198's finite advance/replace steps.
The origin invariant and emission lemma derive the earlier-Polka rule for an
individual changed prevote. Applying the global theorem to an implementation still
requires linking every relevant vote to such a local execution and enforcing
precommit certification separately. The local emit guard alone does not do this.

New fixtures contain 51 Lean examples, five helper theorems and 20 executable
scenarios. They include honest decisions in rounds 0, 1 and 3, nil, genuine local
executions, context rejection and counterexamples with uncertified precommit or
self-justifying Polka when strict round order is weakened.

## Clean Water boundaries

This is conditional safety for one fixed target epoch and decision height, with
fixed weights and explicit adoption/history rules. It is not full protocol safety
for arbitrary epoch transitions. Every extended history must satisfy the rules;
simple extension does not establish their preservation. Chain identity, envelope
provenance, signature authentication, network delivery, asynchronous timeouts,
liveness, leader rotation, activation and production refinement remain open.
Python, JSON/SHA-256 and SimLab obligations remain open. Allowed axioms are only
propext, Classical.choice and Quot.sound; mathematical novelty is not assessed.

## Publication boundary

Only selected tracked public files are exported. Russian cards, simulations/,
chats-export/, untracked work material and private Git history are excluded.
The publisher verifies accepted fingerprints and exact committed bytes, then pushes
main followed by the annotated v0.7.8 tag without force. Hash identity alone does
not authenticate provenance.

See the [module card](../knowledge/02_distributed_systems/DistributedTendermintHandoverRoundInduction.md),
[versioning](../VERSIONING.md) and [scope policy](verification-scope-policy.en.md).
