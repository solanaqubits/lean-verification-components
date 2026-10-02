---
id: DistributedRaftCandidateHistory
language: en
section: distributed
source: Verification/DistributedRaftCandidateHistory.lean
source_sha256: 748ce51a2954159537cc924f7c43922275d6880c2f49270b98a14e19eb85c66d
novelty: not-assessed
status: reviewed
---

# DistributedRaftCandidateHistory

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftCandidateHistory.lean)

## The campaign snapshot remains exact

The module connects a historical RequestVote payload to the candidate's current campaign log through the original operational transitions.

## Proved statements

- `candidate_step_backwards`: if a step ends with a node as candidate and does not change its term, that node was already candidate and its log is unchanged.
- `candidate_path_log_eq`: the same conclusion holds across a finite path with equal endpoint terms and a candidate endpoint.
- `request_candidate_snapshot`: for an actual `RequestWitness` on an execution prefix, if the sender remains candidate in that request's term, the advertised last index and last term equal those of its current log.

The argument uses term monotonicity. A timeout increases the term, while successful AppendEntries changes the recipient to follower; neither can silently mutate a continuing same-term candidate's campaign log.

## Boundaries

A stale RequestVote need not describe a node after a term change or loss of candidacy. The snapshot theorem therefore requires both the candidate role and equality with the request term. It establishes payload correspondence, not that an up-to-date comparison alone implies committed-prefix preservation. The same fixed-cluster operational model is used without extra transition guards.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
