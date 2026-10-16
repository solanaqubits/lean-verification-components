# Lean 4 formal verifier

[Home](../README.md)

`tools/verifier_skill.py` provides a standard-library Python CLI and API for this
trusted local Lean project. It is not an MCP server or a sandbox for hostile code.

These are available commands, not a sequence to run after every edit:

```bash
python3 tools/verifier_skill.py verify Verification/CryptoPedersenCommitment.lean
python3 tools/verifier_skill.py audit Verification/CryptoPedersenCommitment.lean
python3 tools/verifier_skill.py verify-all
python3 tools/verifier_skill.py card Verification.CryptoPedersenCommitment
python3 tools/verifier_skill.py integrate Verification.CryptoPedersenCommitment CryptoPedersenFormalSuite
```

Reports use JSON. Check `ok`, errors, `audit`, and source hashes. Module verification
includes strict compilation, an incremental Lake build against current sources, and a transitive axiom audit of
project declarations in the imported environment. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Audit also rebuilds before checking;
it does not trust an old compiled artifact after source changes.

`integrate` previews a diff using a recipe in
[integration_targets.json](../tools/integration_targets.json). Add `--apply` to
write the change, verify it, and build. Failure restores the registry and root
source files; it does not restore build caches. Existing guarantees and universes
must be preserved when adding recipes.

`card` returns an English draft without overwriting existing cards. Review the Lean
statements and add precise scope before saving a card.
`scaffold DOMAIN --spec-file FILE` attempts a small explicit Lean proposition;
it does not turn arbitrary prose into a verified specification. Run `--help` for
available commands and arguments.

Agents can follow the local
[SKILL.md](../.agents/skills/lean4-formal-verifier/SKILL.md) and invoke the CLI in
the repository root. [skill.json](../tools/skill.json) describes the local tool;
it is not a universal client installation manifest. For Python usage, import
`Verifier` from `tools.verifier_skill` and pass the project directory.

```python
from tools.verifier_skill import Verifier
report = Verifier(".").verify_module("Verification/CryptoPedersenCommitment.lean")
assert report["ok"], report
```

## Registry integration after the component split

Domain recipes select `Verification.MasterSuiteComponents` using `parent_module`.
The default parent remains `Verification.MasterSuite` for central integration.
The selected parent must resolve to a Lean source inside `Verification/`.
Integration edits the parent suite and constructor, the central direct import, and
the root import; a failed verification restores every changed source file. Existing
recipes are idempotent. The milestone type carries explicit universe arguments.

## Verification scope

During development, run `verify` on the changed module and only its relevant live
regressions (`LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p
'test_MODULE.py'`, replacing the pattern with an existing test file). Confirm a
nonzero expected test count and no skips. `verify` already audits axioms; a second
`audit` on unchanged inputs repeats it and is not an independent auditor. `card`
also verifies, so use it when a generated draft is needed.

Preserve Lake's incremental cache. A build checks target freshness; it need not
recompile unchanged modules. When an existing API changes, also build affected
importing modules and run their regressions: module verification follows imports,
not reverse dependencies. Expand checks when the impact is unclear. Documentation
edits need link/catalog checks rather than Lean rechecking.

The approved [X/Y/Z policy](../VERSIONING.md) replaces the former full gate before
every main/release. Z permits targeted validation of a bounded change, including
affected reverse dependents and registry integration; it need not add a module.
X/Y require the full gate once on the final integrated source: `lake build
--wfail`, `verify-all`, the entire live test suite, required registry and independent
axiom audits, and `python3 scripts/check_knowledge.py`. Keep valid incremental
cache. Changes requiring broad revalidation belong to Y unless they warrant X.

Record commands, outcomes, source/configuration identities, toolchain, dependencies
and the last fully validated commit. Reuse results only within their unchanged
scope. Private-tree evidence does not certify a different public tree. Report
partial/full verification and cached/fresh compilation accurately. Scope selection
and release classification are agent responsibilities, not newly implemented CLI
features. See VERSIONING.md for the full-gate commands.
