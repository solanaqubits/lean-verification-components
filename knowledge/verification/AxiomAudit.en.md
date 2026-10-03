---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: 54c107bad4c7a6371f616f27f1ea5342d1c6a7fc77e8bfa268d1c42bfd30859f
novelty: not-assessed
---

# AxiomAudit

[Section](README.md) · [Lean source](../../Verification/AxiomAudit.lean)

## Verified result

The #audit_axioms command rejects disallowed transitive axioms of a selected declaration, including sorryAx.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

[Read the declarations](../../Verification/AxiomAudit.lean)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
