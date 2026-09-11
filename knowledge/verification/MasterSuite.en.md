---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: b8164a0556e33b72ee3b816d213fa3598901eff16754f106297637d0c54ce4c6
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

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L82)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L94)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L106)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L125)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L140)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L163)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L183)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L193)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L203)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L218)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L235)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L245)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L264)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
