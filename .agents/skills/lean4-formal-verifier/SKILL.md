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
writing code. A successful report requires strict compilation, a fresh Lake build,
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

## Integration and cards

`integrate MODULE SUITE` returns a diff. `--apply` updates only the registry/root
using an explicit recipe in `tools/integration_targets.json`, then verifies and
builds; failure restores those source files. Add a reviewed recipe for a new
suite rather than guessing universes or overwriting the registry. Preserve inherited
fields, integral results and existing public APIs. Source rollback does not
restore build caches; rebuild before using them after failure.

`card MODULE` returns a English draft after verification. Read theorem types,
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
