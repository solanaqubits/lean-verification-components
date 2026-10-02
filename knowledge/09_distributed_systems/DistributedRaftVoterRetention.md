---
id: DistributedRaftVoterRetention
language: en
section: distributed
source: Verification/DistributedRaftVoterRetention.lean
source_sha256: e3fe959cfabda5303609b33f932ecf3abaf9f2dcc18ab1e7784f858cdfba449c
novelty: not-assessed
status: reviewed
---

# DistributedRaftVoterRetention

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaftVoterRetention.lean)

## Scope

This auxiliary module proves retention of a protected log prefix along an interval of one finite operational execution. It uses the unchanged `Step` relation and the conflict-sensitive partial-batch merge algorithm.

## Proved statements

`ComparableSourcesAt run i v p` is an explicit local proof premise. For every in-flight AppendEntries message addressed to `v` with the recipient's current term, it requires a source snapshot in the same execution, with the matching leader role, term, predecessor and contiguous batch. The source log must either be a prefix of `p` or extend `p`.

`voter_prefix_step` proves that one actual transition preserves `p` in the recipient log when `p` was present before the transition and `ComparableSourcesAt` holds. Leader appends extend the old log. Successful follower deliveries use `comparable_prefix_retained`; messages ending before the protected prefix do not erase a matching local suffix. Other transitions leave the log unchanged.

`voter_prefix_retained` lifts the step lemma to every interval `a ≤ b ≤ run.length`, assuming the protected prefix is present at `a` and the source-comparability premise holds at each step in `[a, b)`.

`winning_voter_snapshot` reconstructs a voter snapshot from a ballot counted for a candidate. The snapshot belongs to the same execution no later than the election state; its term equals the candidate’s term, and its log satisfies the actual Up-to-Date comparison against the candidate’s election log. Self-votes and remote votes are handled separately using campaign-log immutability.

## Preconditions and boundaries

Source comparability is a premise of these helper theorems, not an operational guard or an axiom. This module does not itself prove that all reachable deliveries meet that premise, nor that a prefix has been committed. The complete bridge must discharge the premise from the election-term induction and historical message evidence before obtaining unconditional Leader Completeness.

No whole-log replacement is assumed. These results do not model dynamic membership, crash recovery, Byzantine message injection, or liveness.

## Validation

Strict compilation, the full CLI audit, independent axiom auditing, and regression tests passed. See the [validation record](../VERIFICATION.en.md). Mathematical novelty is not assessed.
