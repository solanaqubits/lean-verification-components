---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: 21c9757143b45e798c4e78b75cb253dd912b1650b4c4968cc32833bdf01d7004
novelty: not-assessed
status: reviewed
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
