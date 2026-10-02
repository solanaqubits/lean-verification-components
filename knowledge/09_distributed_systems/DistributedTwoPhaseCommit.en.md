---
id: DistributedTwoPhaseCommit
language: en
section: distributed
source: Verification/DistributedTwoPhaseCommit.lean
source_sha256: 9144db157ea7ce2ce777539d70f9302adada81443260bb6f16921adf4ef9763f
novelty: not-assessed
status: reviewed
---

# DistributedTwoPhaseCommit

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTwoPhaseCommit.lean)

## Verified result

The existing two-vote decision table is preserved. Responses adds explicit votes/timeouts, resolves timeout to abort, and commits exactly when both resolved votes are commit. An abort from either response yields global abort. Applying the single computed decision yields committed only with both commit votes. The duplicated local-state expressions agree and are either both committed or both aborted.

## Assumptions and limitations

Timeout is a supplied constructor, not a network event, elapsed-time property or failure detector. This is a decision rule for collected prepare responses. Agreement is reflexivity on the same expression; atomicity classifies that expression into two cases. There are no independent cohort states, execution effects, delivery steps, durable decisions or traces. No all-or-nothing execution, crash tolerance or safe participant timeout after prepare is proved.

Coordinator blocking, WAL recovery, 3PC, message loss and clusters above two cohorts are not modeled. Old types and functions retain their signatures; the new incompatible signatures live under DistributedTwoPhaseCommit.Responses. The old suite includes h_responses, which manual constructors must provide. The master alias and DistributedSystemsFullSuite.two_phase_commit reuse the existing two_pc component. No new import is added. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DistributedTwoPhaseCommit.distributed_two_phase_commit_master_suite`.
