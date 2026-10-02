---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 082f9293fb43bfad753167c196f5102741c4a4a8e5b7689963f24770d3f1c866
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 86 direct imports. The registry does not contain every declaration in the project. Operational Raft election safety is included; global reachable-state Log Matching remains an open obligation.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L164)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L176)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L188)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L207)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L233)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L294)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L326)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L336)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L346)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L384)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L431)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L461)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L493)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L471)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
