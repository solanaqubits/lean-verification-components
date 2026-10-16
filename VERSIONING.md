# Release versions and verification scope

Status: approved by the project owner. This policy replaces the requirement to
run the full project gate before every main integration or release. It is a
project-specific X.Y.Z scheme, not a claim of Semantic Versioning compliance.
Existing published tags and their evidence remain immutable.

| Part | Meaning | Required validation |
| --- | --- | --- |
| X | Substantial architectural change or incompatible change to key proof contracts | Full gate |
| Y | Full-validation checkpoint, including updates requiring broad revalidation | Full gate |
| Z | Bounded module, fix, documentation or tooling update | Checks covering the affected scope |

Incrementing X resets Y and Z; incrementing Y resets Z. A Z release may contain
a new module, several related changes, or no module. A commit is not automatically
a release. Allocate the release version at integration, not separately in every
parallel branch. No existing package version is changed by adopting this policy.

## Selecting scope

For changed Lean code, use module verification (including its imported axiom
closure), affected reverse dependents and relevant live regressions. Verify final
registry/root integration as well. A chosen target can import much of the library;
Z is not a promise that exactly one file is processed. Preserve valid Lake caches.
For documentation-only changes, use documentation/link/catalog checks.

Lean/Mathlib upgrades, changes to shared foundations, verification mechanisms
affecting trust, and unclear dependency impact require broad validation and Y,
unless their architectural significance warrants X. Bounded tooling changes may
remain Z when the affected behavior and necessary tests can be identified.
Choose scope based on semantic impact, not the number of changed lines.

The full gate is run once on the final integrated source for X/Y:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py'
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

Run the project's required pinned independent axiom auditor as well. Its binary,
version, command and results must be recorded. Allowed axioms remain strictly
`propext`, `Classical.choice`, `Quot.sound`. `audit` immediately after successful
`verify` on identical inputs duplicates work and is not an independent audit.

Full validation is not the same as a clean rebuild: retain valid caches, letting
Lake rebuild stale dependencies. A clean rebuild is reserved for an explicit
reproducibility requirement or cache/toolchain diagnosis. If a check fails, fix
the issue and rerun the invalidated checks; "once" never forbids necessary reruns.

## Evidence and integration

Each release records its source commit, last successful full-validation commit,
changed scope since that baseline, current checked scope, commands, results,
source/configuration hashes and toolchain/dependency identities. Record intervening
Z evidence so the entire delta is covered; a baseline alone does not certify it.
Record uncommitted input hashes during checking and bind them to the final commit.

Reusing a result requires unchanged inputs within its scope. A merge or rebase can
invalidate results: assess the combined diff and check the final integrated tree.
Unclear combined impact requires Y. Private-tree evidence does not automatically
certify a different public tree. Never describe targeted checks as a new full
audit or cached build target counts as freshly rechecked proof counts.

This is an agent/release policy. The current CLI does not automatically classify
versions, select reverse dependencies or enforce evidence coverage. Do not claim
such automation until it is implemented and tested.

Simulation runs and research-note updates alone do not require a Lean release.
If they change Lean contracts, fixtures or integration interfaces, classify and
validate that Lean change under this policy. Independent components can be pinned
together in an integration manifest without forcing synchronized version numbers.
