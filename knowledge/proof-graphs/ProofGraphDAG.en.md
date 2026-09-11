---
id: ProofGraphDAG
language: en
section: proof-graphs
source: Verification/ProofGraphDAG.lean
source_sha256: d53b6d72e3b9b9f68d42b459063f38636da18138af4af94efc0fab798aaa8eac
novelty: not-assessed
---

# ProofGraphDAG

[Section](README.md) · [Lean source](../../Verification/ProofGraphDAG.lean)

## Verified result

A computable checker for certificate trees and conditional soundness of accepted conclusions.

## Assumptions and scope

Soundness retains the assumptions on rule validity and certificate interpretation. This is not a blockchain consensus or distributed execution proof.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`proof_soundness`](../../Verification/ProofGraphDAG.lean#L56)
- [`verifyBatch_iff`](../../Verification/ProofGraphDAG.lean#L107)
- [`batch_verification_sound`](../../Verification/ProofGraphDAG.lean#L130)
- [`proof_dag_master_verification_suite`](../../Verification/ProofGraphDAG.lean#L148)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
