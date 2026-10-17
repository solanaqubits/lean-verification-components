# Hierarchical versions and verification scope

Owner-approved policy, effective from the beta 0.6 checkpoint. Historical tags
and their evidence are immutable. This replaces the former alpha/beta/gamma
change-size convention; old "gamma release" records retain their old meaning.

| Level | Meaning | Minimum checked scope |
| --- | --- | --- |
| Alpha (α) | Global release or system architecture change | Whole system; compatibility and migration review |
| Beta (β) | Full verification checkpoint | All proof sources, integration, registered conformance contracts, all tests and audits |
| Gamma (γ) | A subject direction in the shared base | All modules in that catalog direction and affected external dependents |
| Delta (δ) | A named batch/block inside a direction | Every batch member, their imported closure and affected dependents |
| Epsilon (ε) | A module inside a batch | Module proofs plus affected batch/direction/integration checks |
| Zeta (ζ) | A correction or section inside a module | Changed obligations and their impact; at least strict module checking for proof changes |

Lower levels may be introduced only with a named parent and a concrete need.
A batch can contain one module. New directions receive stable catalog IDs.
A level identifies an object's place, not permission to omit required checks.
Shared definitions, cross-direction changes, trust-tooling changes or uncertain
impact escalate verification. Trust mechanisms/toolchains require beta; global
incompatible architecture changes require alpha. Documentation-only changes
require documentation checks unless they change verification/trust policy.

## Names and counters

A full checkpoint uses tag vA.B.0 (this migration: v0.6.0). Retain the current
alpha counter unless there is a global system release. A/B identify the common
system and beta generation; direction/batch/module are stable named identities,
not interchangeable global decimal counters. Scoped work records:

    beta: v0.6.0
    direction: quantum-physics
    batch: qutrit-secret-sharing
    module: QuantumQutritSecretSharingExplicitDecoder
    revision: 1
    integration_sequence: allocated when accepted on main
    base_sha: <actual parent>
    result_sha: <actual commit>

Versions of different directions are not ordered by comparing their local
revision counters. The single main commit history defines integration order.
Package patch releases may use vA.B.N as serial publication numbers; N is not a
direction ID or proof-coverage claim. Every scoped release states its actual
rank and hierarchy path. No retrospective renumbering of modules 1–190 or tags.

## Sequential integration

Parallel development may use isolated branches/worktrees. Integrate one batch
at a time on current main. Before each integration, compare the actual remote
main with the expected parent, rebase/merge the candidate onto that parent, and
rerun checks invalidated by the combined change. Allocate the integration
sequence centrally at acceptance. A stale base fails integration. Never force
push main or reuse a tag. In shared automation use a single publisher/queue;
a process-local lock alone does not serialize multiple machines.

## Checks and evidence

Use tools/verification_plan.py to inventory local imports and reverse dependents.
Gamma selects the complete direction. Delta uses tools/verification_batches.json.
Epsilon/zeta select named modules. Cross-direction effects expand the plan;
registry dependents are always built. Explicit reviewed test selection is still
required for scoped runs; the planner does not infer test coverage from names.
It does not infer whether arbitrary natural-language requirements are correct.

Beta runs on the final tree, preserving .lake/build:

```bash
python3 tools/release_evidence.py run-beta --output /absolute/external/evidence \
  --auditor /absolute/path/to/pinned/axiom-audit
```

This runs strict root build, verify-all, registry audit, the pinned independent
axiom auditor over every Verification source, all unittest with live checks,
knowledge checks, import-graph/scope checks and diff checks. Errors, incomplete
reports, unexpected skips or changed inputs reject the checkpoint. The full
unittest includes the registered Simon and qutrit statement-conformance checks.
Full proof checking is not universal independent specification checking: record
which modules have normative conformance contracts and which do not.

Only propext, Classical.choice and Quot.sound are allowed. No sorry, admit,
user axioms or native-decide bypasses. Do not duplicate an audit immediately
after verify on unchanged inputs. A separate pinned auditor is a distinct
implementation, not a second independent proof kernel.

Evidence binds source/configuration/test hashes, commands, logs, tool identities
and results. A trusted publisher pins its accepted evidence digest and checks
that committed bytes match before publication. Hash consistency is not report
authentication. The checker, manifest, specifications and publisher need review
independent of a candidate; agents may not silently relax these controls.

A checkpoint is promoted to "last successful beta" only after all required
checks and publication succeed. Until then retain the previous successful beta.
Private and public trees each require their own checks. Fresh compilation counts,
Lake task counts, unittest counts, Lean assertion counts and audit declaration
counts are separate. Record overlapping audit closures without summing them.

## Declarative scope and accepted reuse

See [verification scope policy](docs/verification-scope-policy.en.md). Batch,
catalog and integration JSON data are validated separately from executable rules.
Use `verification_plan.py --base <accepted-main-sha>` to compare metadata and both
old/new dependency graphs. Description-only data edits do not run Lean. Changed
relations select old/new members and integration consumers. Unknown impact and
changes to verification/trust mechanisms still require beta.

`scope_evidence.py` reuses scoped command results only with an externally accepted
report digest and unchanged inputs, closure, tools, configuration, runtime and
commands. It reports invalidation reasons and never downgrades a beta plan.
The change rank and performed verification level are distinct. Infrastructure
batches do not increment the mathematical module counter. Historical checkpoint
tags stay immutable even when subsequent commits undergo full control.
