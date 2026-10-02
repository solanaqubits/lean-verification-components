---
id: DistributedRaftTraceMatching
language: en
section: distributed
source: Verification/DistributedRaftTraceMatching.lean
source_sha256: c2d10bb90f7718f171ffd6654d7dcee5224d862eccfe9f04778e37667a5e93b7
novelty: not-assessed
status: reviewed
---

# DistributedRaftTraceMatching

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftTraceMatching.lean)

## Log Matching across execution time

The module extends the existing ghost archive along actual paths of the unchanged `Step` relation. It preserves all previously archived snapshots even when current follower logs replace conflicting suffixes.

## Proved statements

- `reachable_after_path`, `term_path_monotone`, and `elected_path_monotone` transport reachability, term bounds, and election records along finite transition paths.
- `elected_same_term_log_prefix`: an elected node's earlier log remains a prefix of its later log while its final current term still equals that election term.
- `archive_step_mono` and `archive_path_mono` retain old archive members in a suitable successor archive.
- `historical_log_matching`: any server log in a reachable state satisfies `LogMatching` with any server log in a later state on the same path.

## Boundaries

Historical Log Matching relates prefixes ending at equal index/term entries; it does not mean every earlier entry persists in every later log. The append-only result requires historical election evidence and the same-term endpoint condition, and does not apply to arbitrary followers or after term changes. These are support lemmas; commitment, quorum voting, and Leader Completeness require additional arguments. The underlying cluster remains static.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
