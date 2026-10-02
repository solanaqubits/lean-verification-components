---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 1f3cc826c9eefecbe17d79804e5cc291ba83da9369cc3bb9b73cd28ec170a7fb
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 84 direct imports. The registry does not contain every declaration in the project.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L159)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L171)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L183)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L202)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L228)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L289)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L321)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L331)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L341)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L379)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L424)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L450)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L482)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L460)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.
