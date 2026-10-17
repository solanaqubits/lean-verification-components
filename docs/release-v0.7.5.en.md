# v0.7.5 — Tendermint epoch identity and slashing accountability

This public synchronization adds epsilon module 196,
`DistributedTendermintEpochIdentityContract`, registry integration, regression
tests, declarative batch metadata and English documentation. All 240 root-inclusive
Lean sources match private snapshot `f6dfd6a47914d804b8fb248baf7ea1159912db89`
byte for byte. MasterSuite has 196 direct imports.

## Version and verification identity

- Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`,
  delta `distributed/tendermint-accountability`, epsilon 196.
- Git publication serial v0.7.5 is not a new full-verification claim.
- Lake package version stays 0.7.1. Select Git tag v0.7.5 or its commit to obtain
  this module. Build configuration and executable verification policy are unchanged.
- The unchanged public planner determines the checking scope. No escalation rule
  is relaxed; only proofs, integration, tests, declarative data and docs change.
- Last full public beta basis remains v0.7.1 at
  `2419489245019fb16e32ffac641b9f88eea94126`.
- Last full private control remains `090aed141b831aee5182197e9ea205176f361c0f`.
  Private scoped evidence does not certify the public tree.
- Historical tags stay immutable. Epsilon 197 remains unallocated.

## Proven scope and Clean Water limits

Injective maps connect each epoch's local Fin n indices to stable global IDs.
Natural consensus weights retain module 179's API; stakeMap embeds those units
into a nonnegative rational map supported on the active IDs. Ledger amounts remain
rational. This is not an arbitrary fractional quorum model.

Historical resolution requires exactly one configuration whose interval contains
the offence height. Missing, conflicting and duplicate entries fail closed.
The packet supplies its dimension and evidence, not an identity map. The actual
module 179 checker validates it against the resolved historical configuration.
Accepted local offenders map to global IDs; current index reuse cannot redirect
the historical certificate's blame. Supplied historical records and complete
reference histories require external authentication.

The epoch transition changes current membership metadata while preserving the
entire global ledger and history: active balances, queued amounts and request
times, derived maturities, confiscation, completed payouts and (height, ID) keys.
It does not implement deposits, stake redistribution or consensus activation.
Theorems prove commuting historical debits and epoch changes, cross-epoch replay
invariance, conserved total value and preserved nonnegativity. A fresh accepted
key with positive current liable funds under valid timing, phase and rate guards
causes strictly positive confiscation even after the owner leaves membership.
Historical evidence admitted at the inclusive deadline reduces a liable matured
tranche before payout. Liability is limited to h <= request; unknown evidence is
not guaranteed to arrive before admission closes.

The general sufficient protection condition is u_new not in the entire certified
historical B_global. Under it, the subject's active balance, owned queue and
completed payouts remain unchanged by that penalty. Being outside the whole
historical membership is a stronger sufficient condition in the checked wrapper.
For a singleton offender set, inequality with that former owner suffices. With
multiple offenders, inequality with only one former owner does not suffice.
This is not an iff claim: processed replay keys, zero liable stake or rejection
can also prevent a new debit for an accused subject.

Local reindexing preserves global stake maps and penalties for correspondingly
transported certified offender sets. This generic theorem is not full wire-level
checker equivariance; a concrete regression additionally checks both relabeled
transcripts through the real attribution API.

History/ID authentication, quorum overlap, lock handover, consensus safety or
liveness during membership change, activation delays, deposits/redelegation,
clock authentication, network inclusion, concurrent execution, storage, reorgs
and production-code refinement remain outside scope. Python equivalence,
JSON/SHA-256 and SimLab remain open. Only propext, Classical.choice and Quot.sound
are permitted. Mathematical novelty is not assessed.

## Acceptance and publication

The scoped runner retains Lake cache, builds the batch and integration consumers,
verifies one maximal transitive audit root and runs selected live unittest,
metadata, knowledge and diff checks. Verification strictly compiles AxiomAudit.lean
with warningAsError=true. Nested audit closures are neither rerun nor summed.
Public evidence is bound to the final public tree.

New coverage: 63 Lean examples, two helper reachability theorems and 20 executable
scenarios. These cover a reachable equivocation trace, permutation, departing
owners, reused indices, changed dimensions, deadline payout, partial/full penalties,
replays, missing/ambiguous/duplicate/out-of-bounds history, malformed dimensions,
envelope/reference rejection, timing/rate/phase guards and conserved totals.

Actual commands, measured counts and accepted evidence digest are recorded externally
and in the annotated tag after successful checks. Exact committed bytes are checked
against accepted evidence, then main and tag are pushed sequentially without force.
Hash consistency alone is not authentication. No private Git history, Russian cards,
chats-export, simulations or untracked working materials are exported.

See [versioning](../VERSIONING.md), [scope policy](verification-scope-policy.en.md)
and the [module contract](../knowledge/02_distributed_systems/DistributedTendermintEpochIdentityContract.md).
