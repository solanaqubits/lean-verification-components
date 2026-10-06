---
id: AxiomAudit
language: en
section: verification
source: Verification/AxiomAudit.lean
source_sha256: ffc9106fb0f92359822deee95967632ca0fc2c52b576162e07e36b2801372b15
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
