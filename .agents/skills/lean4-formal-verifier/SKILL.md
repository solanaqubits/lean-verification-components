---
name: lean4-formal-verifier
description: Formalize mathematical specifications in this Lean project, verify modules and axiom dependencies with the local CLI, integrate reviewed suites, and draft English knowledge cards.
---

Use the project root containing `tools/verifier_skill.py`. Read
`knowledge/CONTRIBUTING.en.md` and the relevant section's existing cards before
adding a module. The CLI operates on trusted local Lean projects; it is not a
sandbox for hostile Lean metaprograms or Lake configuration.

## Specification to checked result

Translate the user's specification into explicit types, definitions, hypotheses,
and conclusions. Show the correspondence between the requested property and the
Lean statement. A defined predicate is not a proved transition invariant.
Preserve distinctions between a scalar model, a protocol, and its implementation.

Use `python3 tools/verifier_skill.py verify Verification/Module.lean` after
writing code. A successful report requires strict compilation, a Lake build against current sources,
and a transitive axiom audit of all declarations in imported Verification modules.
`python3 tools/verifier_skill.py audit Verification/Module.lean` also rebuilds
and verifies before auditing, so stale artifacts cannot certify changed source.
Read the report's `ok`, `audit`, source hashes and errors, not just process output.
Allowed axioms are `propext`, `Classical.choice`, `Quot.sound`. No `sorry`, `admit`,
custom axioms or native-decide shortcuts. Do not disable checks to make a report pass.

`scaffold` can attempt a small explicit Lean proposition using `omega`, `ring`,
or `nlinarith`. It does not translate prose, generate arbitrary data models, or
certify that a proposition matches the user's intent. On failure, review and
improve the proof; never replace the intended conclusion with `True` or assume it.

## Verification scope and resource use

During proof development, verify the changed module and run its targeted live
regressions. `verify` already includes the transitive axiom audit: do not follow a
successful `verify` with `audit` for the same unchanged inputs. `audit` is an
alternative entry point, not an independent second auditor. `card` also verifies;
use it when a generated draft is needed, not as another routine check.

Keep Lake's incremental cache. Do not delete `.lake/build` or request clean
rebuilds on every edit. Checking one module follows its imports, not its reverse
dependents: when changing an existing API, also build affected importing modules
and run their relevant regressions. Expand the scope if dependencies are unclear.
Documentation-only edits need documentation/catalog checks, not Lean rechecking.

Follow [VERSIONING.md](../../../VERSIONING.md): alpha (α, formerly X) is a major architectural or
key-contract compatibility change; beta (β, formerly Y) is a full-validation checkpoint; gamma (γ, formerly Z) is a
bounded change with targeted validation, with or without a new module. For gamma,
verify changed proofs and their imported axiom closure, affected reverse
dependents, registry integration and relevant live tests. Documentation-only
changes need documentation checks. Do not run a full gate solely for a gamma release.

For alpha/beta, run the full project gate once on the final integrated source:
`lake build --wfail`, `verify-all`, all live tests with
`LEAN_VERIFIER_LIVE_TESTS=1`, required independent/registry axiom audits, and
`python3 scripts/check_knowledge.py`. Toolchain/dependency changes, shared
foundations, verifier changes affecting trust, or unclear impact require beta
unless the architectural/compatibility change warrants alpha. A bounded tooling
change can remain gamma when targeted checks justify its scope. Retain valid cache;
full verification does not imply a clean rebuild.

Delta (δ) identifies a local iteration in a named parallel stream; epsilon and
lower ranks may identify nested work with explicit parents. Record the base SHA,
stream ID, local counter, current SHA and checked scope. These ranks do not reduce
validation requirements. Allocate a common alpha/beta/gamma release only at
integration and check the combined changes. Existing numeric tags stay unchanged.

Record the last full-validation commit and subsequent scoped evidence. Reuse
results only for their recorded scope and unchanged source, configuration,
toolchain and dependencies; private-tree evidence does not certify a different
public tree. After changes rerun affected checks for the final integrated code.
Report cached build targets separately from freshly compiled modules and never
report a targeted run as a fresh whole-library check. Existing CLI commands do
not automatically select reverse dependents or enforce this release policy.

## Integration and cards

`integrate MODULE SUITE` returns a diff. `--apply` updates the recipe-selected
parent module and the central/root imports. Existing domain packages live in
`Verification.MasterSuiteComponents`; recipes select it with `parent_module`.
It uses an explicit recipe in `tools/integration_targets.json`, then verifies and
builds; failure restores those source files. Add a reviewed recipe for a new
suite rather than guessing universes or overwriting the registry. Preserve inherited
fields, integral results and existing public APIs. Source rollback does not
restore build caches; rebuild before using them after failure.

`card MODULE` returns an English draft after verification. Read theorem types,
add the actual assumptions and limitations, then save it in the appropriate
knowledge section. Do not overwrite an existing reviewed card with the generic
draft. Update catalog imports, section navigation and source-line links, and run
`python3 scripts/check_knowledge.py`. Keep novelty `not-assessed` absent a documented
comparison with earlier proofs/formalizations.

Use `verify-all` for the complete project audit and module checks. Counts refer
to declarations, not independent theorems. Report actual checks and unresolved
scope. Publication, licensing and public releases are separate from verification.

For CLI examples, report semantics, API calls and external-assistant connection,
read [the tool guide](../../../docs/verifier-skill.en.md) in this repository.
