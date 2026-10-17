# v0.7.7 — Tendermint lock handover contract

This release in solanaqubits/leanbook synchronizes epsilon module 198 from
leanbook-private snapshot `7eb0af2ad3ca2804f1de546ff72f66dfe1c3708c`.
All 242 Lean sources including Verification.lean match that snapshot byte for byte.
MasterSuite has 198 direct imports. Integration, tests, declarative metadata and
English documentation are included; private Git history is not exported.

## Version and verification identity

Hierarchy: alpha 0, historical beta generation 7, gamma `distributed`, delta
`distributed/tendermint-accountability`, epsilon 198. v0.7.7 is a Git publication
serial, not a new full-verification checkpoint. Lake remains 0.7.1. Executable
checking tools and build configuration are unchanged. The public planner determines
the required scope without relaxation of escalation rules.

The last full public beta basis remains v0.7.1 at
`2419489245019fb16e32ffac641b9f88eea94126`; the last full private control remains
`090aed141b831aee5182197e9ea205176f361c0f`. Public and private evidence remain separate.
Historical tags are immutable. Epsilon 199 remains unallocated.

## Proven contract

Polka denotes prevote quorum, commit denotes precommit quorum. The weak >=2/3
mode requires common honest mass >2/3; strict >2/3 permits common honest mass
>=2/3. The existing natural-weight CoreSafety/179 API uses the strict convention.
Module 197 provides the honest shared signer; module 196 supplies stable identities.

A certificate contains finite CoreSafety.Vote records with an epoch/height envelope.
Signer sets are computed from the correct phase, round and value, then mapped into
global identities. Duplicate records do not add weight. checkHandover checks
consecutive epochs, the source context, prevote phase, the historical interval,
positive total weight and the historical quorum. adopt is restricted to new members
with empty or identical state; replay is idempotent and cannot reset a later lock.
Source rounds remain provenance; target lock rounds start at zero.

The round-zero theorem assumes an accepted source polka, a source commit for the
same value/context, a target round-zero commit at the same decision height,
normalization, the appropriate overlap bound, actual adoption by honest source
commit signers in the target membership, and honest target vote discipline.
It proves equal commit values, not equality of decisions at different heights.
Receipt and adoption are explicit premises; intersection does not deliver evidence.
Nil votes are abstentions and do not release a lock.

Successful later replacements require the target epoch and same height, a prevote
quorum, positive weight, and lockedRound < polka.round < currentRound.
Backward round advancement is rejected. Finite local execution theorems preserve
epoch/height, make round counters nondecreasing, preserve the value in reachable
round zero, and exhibit a checked replacement witness for a changed final value.
A one-validator counterexample shows that full honest overlap without adoption
can coexist with conflicting old/new commits.

## Clean Water boundaries

The local replacement rule does not establish agreement for every later round:
a global invariant excluding the first conflicting higher polka is still needed.
The vote-value guard is not the entire Tendermint phase machine. It does not itself
prove that each precommit has a same-round polka. Strict replacement is this
contract's policy, not equivalence to every unlock branch of the older core model.

Epoch/height provenance, signature authentication and uniquely resolved historical
configuration are external assumptions; the finite checker is not a cryptographic
verifier. Full asynchronous transition safety/liveness, network delivery, timeouts,
clock synchronization, activation, production refinement, Python, JSON/SHA-256 and
SimLab remain open. Only propext, Classical.choice and Quot.sound are allowed.
Mathematical novelty is not assessed.

## Validation and publication

The scoped runner retains Lake cache and checks the affected batch, integration,
selected live unittest, metadata, knowledge and diff formatting. One maximal
AxiomAudit verification includes strict compilation with warningAsError=true and
the transitive declaration audit; nested closures are neither repeated nor summed.
New fixtures contain 61 Lean examples, four helper theorems and 22 executable
scenarios. Exact commands, measured metrics and the accepted evidence digest are
recorded externally and in the annotated tag after successful validation.

The publisher matches committed bytes to accepted public evidence and checks the
expected remote parent, then pushes main followed by the annotated tag without
force. Hash identity does not itself authenticate provenance. Russian cards,
chats-export, simulations and untracked work materials are excluded from export.

See the [module card](../knowledge/02_distributed_systems/DistributedTendermintLockHandoverContract.md),
[versioning](../VERSIONING.md) and [scope policy](verification-scope-policy.en.md).
