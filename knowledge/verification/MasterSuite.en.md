---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 78dd7f03591d9245efeb133fd43b9b1936bd082a309f43dd45b0aa61819960fd
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 92 direct imports. The registry does not contain every declaration in the project. The Raft package includes reachable-state election safety, global Log Matching, operational Leader Completeness for actual commit events, and preservation of committed prefixes. The new bridge proves the operational conclusion directly; it does not instantiate the earlier whole-log VoterEvolution abstraction.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L176)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L188)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L200)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L219)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L246)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L309)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L343)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L353)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L363)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L401)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L450)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L484)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L520)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L496)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

`CryptoFullSuite.feldman_vss` includes scalar consistency and reconstruction against fixed coefficient commitments; no cryptographic secrecy is claimed.

`PhotonicsInterposerFullSuite.chip_layout` adds translation invariance and exact rational bounds checking. The separate `chip_placement_certificate` field certifies the exact stored 256-node placement. External digest binding remains outside the Lean proof.

`QuantumPhysicsFullSuite.optomechanical_coupling` adds normalized scalar energy, force derivatives, dispersion, and a prescribed damping model. Full quantum dynamics and cooling are not proved.
