# v0.7.6 — Tendermint quorum intersection during epoch transitions

Public repository: [solanaqubits/leanbook](https://github.com/solanaqubits/leanbook).
The private source repository is now named leanbook-private. Historical repository
names in older release records remain unchanged.

This release adds epsilon module 197,
`DistributedTendermintQuorumIntersectionEpochTransitionContract`, integration,
regressions, declarative metadata and English documentation. All 241 root-inclusive
Lean sources match private snapshot `137f851a246a72e6a7d9c621e0f016ddc9bdb3cb`
byte for byte; MasterSuite has 197 direct imports.

## Version and control scope

Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`, delta
`distributed/tendermint-accountability`, epsilon 197. Git tag v0.7.6 is a serial
publication marker, not a new beta claim. Lake stays 0.7.1; executable checking
policy and build configuration are unchanged. The unchanged public planner
computes the required scope; no escalation rule is relaxed.

The last full public beta basis remains v0.7.1 at
`2419489245019fb16e32ffac641b9f88eea94126`. The last full private control remains
`090aed141b831aee5182197e9ea205176f361c0f`; private and public evidence are separate.
Historical tags are immutable. Epsilon 198 remains unallocated.

## Proven mathematical contract

On finite stable validator IDs, two nonnegative rational weight distributions
are normalized to total 1. Let mu(v)=min(w1(v),w2(v)), H=mu(V minus B), and
I=(Q1 intersect Q2) minus B. For non-strict quorums of weights at least q1 and q2:

    mu(I) >= H + q1 + q2 - 2.

Thus H > 2-q1-q2 guarantees a shared ID outside the supplied fault set B with
positive weight in both epochs. Total variation delta is half the sum of absolute
weight differences. H=1-delta-mu(B), so delta+mu(B)<q1+q2-1 is sufficient.
The alternative w1(B)+w2(B)+delta criterion is conservative and does not reduce
to the sharp static one-third bound. Directed honest loss is explicitly
L=sum outside B of max(w1(v)-w2(v),0); H=1-w1(B)-L.

For non-strict 2/3 quorums the sufficient criterion is w1(B)+L<1/3. Strict >2/3
quorums instead permit H>=2/3, including equality. Static specialization and a
bridge to module 179's actual strict natural-weight Config.quorum API are proved.
Normalization requires positive total weight. Module 196's global stake maps
support unequal local dimensions, ID permutations and positive independent scaling.

Explicit counterexamples show disjoint non-strict 2/3 quorums at delta=1/3 and
disjoint strict 7/10 quorums at delta=2/5, with no faulty validators. A separate
example demonstrates that the sufficient common-mass criterion is not necessary
for every pair of distributions.

## Clean Water boundaries

These are weighted set-theoretic conditions for an honest shared validator.
They do not prove that this validator votes consistently across epochs. Lock
transfer, round synchronization, polling/commit semantics, full transition safety,
activation, authenticated historical configurations and the truth of the supplied
fault set remain external obligations. With separate fault sets, their union is
needed for honesty in both epochs. Network behavior, implementation refinement,
Python equivalence, JSON/SHA-256 and SimLab remain open. Only propext,
Classical.choice and Quot.sound are permitted; novelty is not assessed.

## Validation and publication

The public scoped runner retains Lake cache, builds the affected batch and
integration consumers, verifies one maximal transitive audit root (including
strict AxiomAudit compilation), runs selected live unittest, and checks metadata,
knowledge and diff formatting. Nested audit closures are not repeated or summed.
New coverage: 63 Lean examples, two normalization helper theorems and 20 executable
scenarios. Commands, measured results and accepted evidence digest are recorded
externally and in the annotated tag after successful validation.

The publisher verifies exact committed bytes against accepted public evidence,
then pushes main followed by the annotated tag. Hash consistency alone is not
provenance authentication. No private Git history, Russian cards, chats-export,
simulations or untracked working material is exported.

See the [module card](../knowledge/02_distributed_systems/DistributedTendermintQuorumIntersectionEpochTransitionContract.md),
[versioning](../VERSIONING.md) and [scope policy](verification-scope-policy.en.md).
