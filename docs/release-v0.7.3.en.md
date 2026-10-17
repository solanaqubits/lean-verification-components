# v0.7.3 — Tendermint slashing replay protection

This public synchronization adds epsilon module 194,
`DistributedTendermintSlashingReplayProtection`, registry integration, tests,
declarative batch data and English documentation. All 238 root-inclusive Lean
sources are byte-identical to private snapshot
`b675ae94367564b5d9858254b57467b05d9b338c`; MasterSuite has 194 direct imports.

## Version and verification identity

- Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`,
  delta `distributed/tendermint-accountability`, epsilon 194.
- Git publication serial: v0.7.3. The patch number is not a coverage claim.
- Lake package version remains 0.7.1. Select Git tag v0.7.3 or its commit to use
  this module. Build configuration and verification mechanisms are unchanged.
- Actual acceptance scope is assigned by the unchanged public planner; no
  escalation rules are weakened. Only module/integration files, tests,
  declarative metadata and documentation change.
- Last full public beta control remains v0.7.1 at
  `2419489245019fb16e32ffac641b9f88eea94126`; this is a scoped publication.
- Private full control remains `090aed141b831aee5182197e9ea205176f361c0f`;
  the private module snapshot has separate scoped evidence.
- Historical tags stay immutable. Epsilon 195 remains unallocated.

## Verified scope and boundaries

The ledger contains rational balances, an accumulated confiscation pool and a
finite set of processed (height, validator) keys. Fresh certified offenders alone
are charged. The checked transition obtains its offender set through module 179's
attribute_evidence and takes height from Config.height. Invalid certificates,
missing/incomplete references and rates outside 0 < alpha <= 1 change no state.
A zero rate is rejected instead of consuming keys without applying a penalty.

Repeating a certificate, or presenting another accepted certificate for the same
set at the same height, leaves the resulting state unchanged. Intersecting sets
cannot charge their common validators again. Nonnegative balances and pool,
conservation of balances plus pool, and first-step agreement with module 192 are
proved. Actual honest-validator protection uses a reachable reference history.
Processed keys are never forgotten; accounting and nonnegativity extend to every
finite sequential request list.

The policy permits one application per (height, validator), including distinct
offences at the same height. A new authenticated height permits another charge;
zero balances still consume accepted keys. Stable validator identities, authentic
configuration/height, complete reference acquisition and initial processed state
are external assumptions. The model does not prove database durability, atomic
concurrent transactions, crash recovery, chain reorganizations, unbonding,
evidence deadlines or deployed Tendermint/CometBFT equivalence. Replay filtering
does not preserve an unconditional original > one-third confiscation bound:
a complete replay confiscates zero. Python, JSON/SHA-256 and SimLab remain open.

## Acceptance and publication

The standard scoped runner preserves Lake cache, builds the selected batch and
integration consumers, verifies one maximal transitive audit root, runs selected
live unittest and checks metadata, knowledge links and diffs. AxiomAudit is
compiled with warningAsError=true inside verify. Nested audit scopes are not
repeated or summed. Only propext, Classical.choice and Quot.sound are allowed.

New fixtures contain 40 Lean examples, two helper theorems and ten executable
scenarios. Independent expected balances cover repeated/alternative certificates,
partial overlap, invalid inputs, full/partial confiscation and a new height.
The actual evidence checker accepts nonempty blame from an executable reachable
trace. A finite mixed request sequence tests conservation and replay retention.

Commands, measured results and accepted evidence digest are recorded externally
and in the annotated tag after checks succeed. Evidence binds the public final
tree; private checks do not substitute for it. Hashes alone are not authentication.
The publisher pins accepted evidence separately and compares committed bytes,
then pushes main followed by the annotated tag without force.
No private Git history, Russian cards, chats-export, simulations or untracked
working materials are exported. Source working environments remain unchanged.

See [versioning](../VERSIONING.md), [scope policy](verification-scope-policy.en.md)
and the [module contract](../knowledge/02_distributed_systems/DistributedTendermintSlashingReplayProtection.md).
