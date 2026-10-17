# v0.7.1 — scope policy and certified Tendermint slashing

This public synchronization includes the infrastructure batch
`verification-scope-policy` and mathematical epsilon module 192,
`DistributedTendermintSlashingPenaltyContract`. It has 192 direct MasterSuite
imports and 236 root-inclusive Lean sources, byte-identical to private snapshot
`92193b9a12359197dd9f0ac5c5d573f90bbc11a5`.

## Identity and evidence boundaries

- Alpha generation 0; historical beta generation 7 / v0.7.0 remains immutable.
- Package publication serial: v0.7.1, as explicitly selected for this release.
  The patch number does not encode a direction or proof-coverage level.
- Mathematical change: gamma `distributed`, delta
  `distributed/tendermint-accountability`, epsilon 192.
- Infrastructure change: batch `verification-scope-policy`.
- Actual acceptance scope: full beta control of the final public tree, required
  by changes to trusted verification mechanisms and Lake configuration.
- The new public full-control basis is the release commit identified by the
  annotated v0.7.1 tag. This does not allocate beta generation 8 or change the
  historical v0.7.0 tag. Epsilon 193 remains unallocated.

The preceding public full-control commit is
`3f16ce864d4b18ae63c2d3732f99689081d3469f`.
Private evidence remains separate: the last private full control is
`090aed141b831aee5182197e9ea205176f361c0f`, the private scoped module commit is
`92193b9a12359197dd9f0ac5c5d573f90bbc11a5`, and historical private beta 7 is
`60208b5dd27a78a4d303cc70fa6dd37060191120`.
Public acceptance does not re-certify a differently packaged private tree.

## Verified mathematical scope

Slashing applies an exact rational rate to a certified finite offender set.
The proofs cover nonnegative residual balances, unchanged protected balances,
remaining-plus-confiscated accounting, strict loss of positive offending stake,
and confiscation greater than alpha times W/3 when the certified weight exceeds
W/3. Actual honest-validator protection uses reachable histories and module 179's
checked attribution. Strict share growth requires positive protected mass and
positive confiscation; positive denominators are proved. Full confiscation may
leave zero balances. A complementary honest supermajority and offender weight
above one third are separate, incompatible scenarios for the same partition.

The model is one deterministic penalty application. Repeated partial penalties
are not idempotent: a persistent replay ledger is a separate obligation.
Dynamic unbonding, evidence delivery delays, obtaining authenticated references,
digital signatures, rounding and allocation of confiscated funds are outside
scope. Python equivalence, JSON/SHA-256 and SimLab obligations remain open.
No deployed Tendermint/CometBFT implementation equivalence is claimed.

## Verification infrastructure

Validated declarative batch and integration metadata are separate from the
executable planner. Scope follows actual imports, reverse consumers and affected
integration points; changes to trusted mechanisms require full control. Evidence
reuse requires matching bound inputs, dependencies, tools, configuration and
runtime, plus an independently accepted report digest. Hashes alone are not
signatures and do not protect against an actor controlling both the checker and
the acceptance step. The policy adds 29 regression tests.

## Acceptance procedure

The version is set before final checks. Preserve the Lake build cache and run one
full public beta workflow, with no additional module/MasterSuite audit or scoped
unit-test run over the same unchanged inputs:

```sh
python3 tools/release_evidence.py run-beta --output /absolute/external/evidence --auditor /absolute/path/to/pinned/axiom-audit
python3 tools/release_evidence.py check --evidence /absolute/external/evidence --expected-digest ACCEPTED_DIGEST
```

The workflow performs strict root build, complete verify-all, strict AxiomAudit,
the distinct pinned axiom auditor, all live unittest, knowledge/catalog, scope
and diff checks. Only propext, Classical.choice and Quot.sound are permitted.
Independent normative conformance is registered for Simon and the qutrit decoder;
it is not semantic validation of every module. The second auditor is not a
second proof kernel. Intersecting audit declarations are never summed.

Actual counts, commands and accepted evidence digest are recorded externally and
in the annotated release tag after successful validation. Exact committed bytes
must match the accepted tree. Publish main first, then the annotated tag, without
force. No private history, chats-export, simulations or untracked working material
is exported. Existing source checkouts and historical tags remain unchanged.

See [scope policy](verification-scope-policy.en.md),
[version policy](../VERSIONING.md) and
[slashing contract](../knowledge/02_distributed_systems/DistributedTendermintSlashingPenaltyContract.md).
