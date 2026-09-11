---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 02f55b6e01f7d282fad1f49b37bade27b1575059dce3325b0ac100586a793a3d
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

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L98)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L110)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L122)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L141)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L158)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L186)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L209)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L219)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L229)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L246)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L266)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L277)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L296)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
