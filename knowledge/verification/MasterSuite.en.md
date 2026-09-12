---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 443e860f31194a7b6c8dec5d50a317f7168ada507b5b9740952264e22b5677bc
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Ten suites of selected theorems with 42 direct imports. The registry does not contain every declaration in the project.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L116)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L128)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L140)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L159)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L178)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L211)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L237)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L247)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L257)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L276)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L300)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L313)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L332)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
