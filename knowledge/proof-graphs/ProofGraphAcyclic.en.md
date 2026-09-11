---
id: ProofGraphAcyclic
language: en
section: proof-graphs
source: Verification/ProofGraphAcyclic.lean
source_sha256: 5be8c9caac69f24459f872661c829b87f785bec0df795ac51a574e51e9a0f54a
novelty: not-assessed
---

# ProofGraphAcyclic

[Section](README.md) · [Lean source](../../Verification/ProofGraphAcyclic.lean)

## Verified result

References to strictly smaller indices exclude cycles; conditional soundness of sequential DAG evaluation.

## Assumptions and scope

Soundness retains the assumptions on rule validity and certificate interpretation. This is not a blockchain consensus or distributed execution proof.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`direct_edge_strict_lt`](../../Verification/ProofGraphAcyclic.lean#L33)
- [`no_self_loop`](../../Verification/ProofGraphAcyclic.lean#L39)
- [`dependency_path_strict_lt`](../../Verification/ProofGraphAcyclic.lean#L49)
- [`proof_graph_acyclic_master_verification_suite`](../../Verification/ProofGraphAcyclic.lean#L166)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
