# v0.7.4 — Tendermint unbonding period and evidence window

This public synchronization adds epsilon module 195,
`DistributedTendermintUnbondingPeriodContract`, its registry integration, tests,
declarative batch metadata and English documentation. All 239 root-inclusive
Lean sources match private snapshot `52174d5a9ef0065506e2dfc3d10e9a267fc6a623`
byte for byte. MasterSuite has 195 direct imports.

## Version and verification identity

- Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`,
  delta `distributed/tendermint-accountability`, epsilon 195.
- Git publication serial v0.7.4 is not a new full-verification claim.
- Lake package version remains 0.7.1. Select Git tag v0.7.4 or its commit for this
  module. Build configuration and executable verification policy are unchanged.
- The unchanged public planner assigns the actual checking scope; no escalation
  rule is relaxed. The candidate changes proofs/integration, tests, declarative
  metadata and documentation only.
- Last full public beta control remains v0.7.1 at
  `2419489245019fb16e32ffac641b9f88eea94126`.
- Last full private control remains `090aed141b831aee5182197e9ea205176f361c0f`;
  private scoped evidence does not certify this public tree.
- Historical tags stay immutable. Epsilon 196 remains unallocated.

## Proven scope and Clean Water limits

The discrete sequential state contains active rational balances, a finite queue
of withdrawal requests, accumulated confiscation, completed withdrawals and
processed (height, validator) keys. A strictly positive window is fixed during
execution. A tranche matures at request time plus this window and is liable
only for offence heights h <= request time. It stops active participation at
the request. This is an abstract policy, not deployed Tendermint/Cosmos conformance.

The checked transition validates certificates through module 179 and rejects
future or expired evidence, missing/invalid references, closed admission and
invalid rates. Module 194 supplies the replay-safe eligible-balance ledger.
Refinement equates that ledger with the actual active/queue update. Theorems
preserve nonnegativity and active + queued + confiscated + completed value.
Positive confiscation requires accepted blame, a fresh key, positive current
eligible stake and a positive valid penalty rate.

Each scheduled slot processes its supplied certificate batch before closing
admission and finalizing withdrawals. At the inclusive deadline, a liable
matured tranche is reduced before its remaining value is paid. No-Escape applies
only to funds liable for the offence height (h <= request) and certificates
actually included before admission closes. Physical delivery or inclusion of
an unknown certificate is not guaranteed. Closing admission prematurely is
outside the prescribed scheduler, and a reversed-order regression exhibits the
lost debit. Later offences do not extend an earlier tranche's liability.

Honest withdrawal liveness is conditional: time reaches maturity and finalization
is actually executed. Accepted evidence must exclude the tranche or concern a
later offence; module 179 supplies this exclusion for honest owners and reachable
reference histories. The model does not prove unconditional network progress.

Network delays, NTP/BFT clock synchronization or authentication, concurrent
mempools, durable databases, chain reorganizations, epoch identity mapping and
production-code refinement remain external. Python equivalence, JSON/SHA-256
and SimLab remain open obligations. Only propext, Classical.choice and Quot.sound
are permitted; mathematical novelty is not assessed.

## Acceptance and publication

The scoped runner preserves Lake cache, builds the batch and integration
consumers, verifies one maximal transitive audit root and runs selected live
unittest, metadata, catalog and diff checks. The verifier strictly compiles
AxiomAudit.lean with warningAsError=true. Nested audit closures are not rerun
or summed; public evidence is bound to the final public tree.

New coverage comprises 61 Lean examples, two helper reachability theorems and
20 executable scenarios: future/deadline/expired certificates, replay, different
heights, invalid rates/evidence, mixed-liability queues, partial/full penalties,
honest payout, overdrawn requests, time progression and reversed-phase mutation.
A reachable faulty-vote trace gives a nonempty accepted certificate.

Measured commands, results and accepted evidence digest are recorded externally
and in the annotated tag after successful checks. The publisher separately pins
accepted evidence, checks exact committed bytes, then pushes main followed by
the tag without force. Hash consistency alone is not authentication.
No private Git history, Russian cards, chats-export, simulations or untracked
working materials are exported. Original working trees remain unchanged.

See [versioning](../VERSIONING.md), [scope policy](verification-scope-policy.en.md)
and the [module contract](../knowledge/02_distributed_systems/DistributedTendermintUnbondingPeriodContract.md).
