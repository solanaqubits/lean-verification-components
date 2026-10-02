---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 03ae1cf8402486e65154fc535918430d65c4a81fbd59f4111cd7d80c9eef0286
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 90 direct imports. The registry does not contain every declaration in the project. Operational Raft election safety is included; global reachable-state Log Matching remains an open obligation.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L172)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L184)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L196)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L215)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L242)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L305)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L339)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L349)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L359)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L397)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L444)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L474)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L510)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L486)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

`CryptoFullSuite.feldman_vss` includes scalar consistency and reconstruction against fixed coefficient commitments; no cryptographic secrecy is claimed.

`PhotonicsInterposerFullSuite.chip_layout` adds translation invariance and exact rational bounds checking. No simulation manifest or external digest binding is certified.

`QuantumPhysicsFullSuite.optomechanical_coupling` adds normalized scalar energy, force derivatives, dispersion, and a prescribed damping model. Full quantum dynamics and cooling are not proved.
