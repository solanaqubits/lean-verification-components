# Verification scope policy

Infrastructure batch: `verification-scope-policy`. Change level: delta. Actual
control required for this implementation: beta, because planner, evidence and
integration validation code change. Historical beta 7 / v0.7.0 stays immutable.
The infrastructure batch itself allocates no mathematical module. This public
synchronization also includes epsilon module 192,
`DistributedTendermintSlashingPenaltyContract`, in the existing `distributed`
direction. The combined tree has 192 direct imports and 236 Lean sources.

## Data and mechanisms

`tools/verification_batches.json`, `tools/integration_targets.json` and
`knowledge/catalog.json` are declarative data, despite residing below tools.
`verification_metadata.py` validates them with explicit field/type/reference
rules. Unknown batch fields, duplicate JSON keys, missing members and invalid
integration references are rejected. Recipes permit qualified names, universe
arguments and the legacy `by exact <reference>` wrapper; arbitrary Lean tactics,
proof bodies and shell commands are not accepted. The integration API applies
the same recipe validator before modifying Lean sources.

Batch descriptions never choose commands or waive checks. Infrastructure batch
entries are descriptions only; they do not allocate mathematical module numbers.
Catalog import lists do not define the proof graph: real Lean imports do.
Knowledge/catalog checks validate the remaining documentation relationships.

## Impact analysis

```bash
python3 tools/verification_plan.py --base <accepted-main-sha> \
  --rank delta --batch quantum-physics/qutrit-secret-sharing
```

The base must be a Git commit. Changes include staged, unstaged, untracked,
deleted and both sides of renamed paths. The planner compares old/new metadata
and uses both old/new import graphs to retain consumers of removed edges.
A description-only edit requires metadata validation, knowledge checks and diff
checks, with no Lean commands. A membership or recipe edit selects old and new
members and affected integration registries. A proof edit selects its reverse
consumers and imported axiom closure. Cross-direction effects expand to complete
affected directions to a fixed point. Invalid graphs fail closed.

Without a baseline, changed metadata selects all referenced members rather than
assuming a description-only edit. Tooling, normative contracts, policy, Lake
configuration, test changes without explicit reviewed selection, and unclassified files
conservatively require beta. This is not a claim of semantic minimum work for
arbitrary programs. The computed minimum follows the explicit conservative policy.

Explicitly selected batch unittest files and Lean regression fixtures with resolved
local imports remain scoped. Changes to verifier/admission/conformance tests still
require beta even if listed in the selected tests. Selection is reviewed coverage,
not a claim that arbitrary Python test imports can be inferred statically.

The JSON report keeps `requested_rank`, `effective_rank`, `verification_level`,
per-file rules/seeds, commands, imported closure and reverse consumers separate.
Registry build targets can pull in a large import closure; this does not turn a
scoped run into full beta. Maximal importing roots avoid auditing every node
individually. Distinct maximal roots may have overlapping imported closures.

## Accepted evidence reuse

```bash
python3 tools/scope_evidence.py --base <accepted-main-sha> \
  --rank delta --batch quantum-physics/qutrit-secret-sharing \
  --test tests.test_qutrit_circuit --output /external/new-evidence \
  --reuse /external/previous-evidence --accepted-digest <publisher-pinned-sha256>
```

Omit `--reuse` and `--accepted-digest` on the first run. Scoped proof work needs
an explicit reviewed unittest selection (including the affected batch tests).
The tool does not infer adequate test coverage from test names. A beta plan is
refused by this runner and must use `release_evidence.py run-beta`.

Every check binds a tagged canonical JSON tuple, hashed with SHA-256: exact input
bytes, imported source bytes, checker sources, configuration, runtime/dependency
fingerprints, command arguments and relevant environment. This is not XOR.
Tests and metadata checks bind their broader data inventory. The diff check also
binds Git working/index diffs. Configuration changes or a single changed
transitive dependency invalidate the relevant cache entry. Logs and success
conditions are checked; failures, skipped tests and changed inputs cannot produce
a passed record. Inputs/runtime are checked again at the end. A new report lists
which checks were reused and the changed components for each rejected cache entry.
No beta report is silently converted into a scoped record.

The accepted report digest must come from an independently controlled acceptance
step. A digest supplied by the report's author is not authentication. Hashes do
not defeat an attacker controlling both the checker and the acceptance pin.
Use an isolated trusted publisher; this patch does not implement OS isolation,
remote attestation, a compiler proof or a multi-host publication queue.

Only the CLI constructs the plan directly from the checkout. Python APIs are
trusted caller interfaces, not a sandbox for supplied plan objects. Run on an
isolated, quiescent tree and verify accepted bytes again before publication.
The full beta evidence mechanism remains authoritative for whole-tree checks.

## Regression coverage and workflow

The small synthetic Git repositories in `tests/test_verification_scope.py`
exercise description edits, new/removed members, removed imports, transitive
consumers, malformed data, recipe injection, mandatory trust escalation, changed
hash groups, accepted-log/report tampering and actual command reuse. Mocked
command tests check orchestration, not Lean proof validity; the required full
beta run separately exercises the real proof toolchain and all live tests.

The infrastructure-only batch does not change mathematical sources. The public
v0.7.1 synchronization additionally includes module 192 and the package version
change. Historical beta 7 tags remain immutable; record this new public full
control separately from all private evidence. Publish only after comparing remote main to the expected
parent. Preserve source worktrees and caches. `chats-export/` is excluded from
publication; its unprocessed contents must never enter commits or public exports
without separate explicit user authorization.
