---
id: DistributedTwoPhaseCommit
language: en
section: distributed
source: Verification/DistributedTwoPhaseCommit.lean
source_sha256: a86cf14e428e9a7d1982466cd21b4ec2ee86f77ddebe5b3b63335d5531306c29
novelty: not-assessed
status: reviewed
---

# DistributedTwoPhaseCommit

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTwoPhaseCommit.lean)

## Verified result

The coordinator's supplied two-vote decision table returns commit exactly when both votes are yes, and abort exactly when at least one vote is no. Separate lemmas cover a no vote from either participant. The supplied agreement statement is a reflexive equality of applyDecision d with itself; applyDecision is the identity function.

## Assumptions and limitations

Both votes are already available. The finite types contain no pending vote or undecided outcome. There are no distinct participant states, coordinator state machine, prepare/commit phases, transaction effects, message delivery or execution histories. The theorem named global_agreement_invariant therefore does not prove agreement between distributed participants. Abort is a decision label, not a verified rollback of data.

Neither atomicity across actual executions, termination, blocking behavior, lost or delayed messages, timeouts, coordinator crash recovery and WAL, nor three-phase commit is formalized. The model is a two-input decision table, not a complete verification of 2PC.

## Value and novelty

A small, reusable unanimity decision rule with exhaustive finite-case proofs. The reflexive agreement lemma adds no distributed safety guarantee. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DistributedTwoPhaseCommit.distributed_two_phase_commit_master_verification_suite`.
