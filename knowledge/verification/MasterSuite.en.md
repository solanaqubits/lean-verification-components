---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: d872627dc53b97144b317ff83e14811199d711657483d84ba552cd08635f1004
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Ten suites of selected theorems with 41 direct imports. The registry does not contain every declaration in the project.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L77)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L89)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L101)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L120)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L135)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L157)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L176)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L186)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L196)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L210)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L226)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L236)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L255)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
