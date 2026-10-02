---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 33a01743b5705116a6944d3e3ad15f8fab1aa3833d203f5ef7f2fbbc9ef74547
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 94 direct imports. The registry does not contain every declaration in the project. The Raft package includes reachable-state election safety, global Log Matching, operational Leader Completeness for actual commit events, and preservation of committed prefixes. The new bridge proves the operational conclusion directly; it does not instantiate the earlier whole-log VoterEvolution abstraction.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L180)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L192)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L204)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L223)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L251)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L315)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L349)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L359)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L369)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L407)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L456)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L490)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L528)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L503)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

`CryptoFullSuite.feldman_vss` includes scalar consistency and reconstruction against fixed coefficient commitments; no cryptographic secrecy is claimed.

`PhotonicsInterposerFullSuite.chip_layout` adds translation invariance and exact rational bounds checking. The separate `chip_placement_certificate` field certifies the exact stored 256-node placement. External digest binding remains outside the Lean proof.

`QuantumPhysicsFullSuite.optomechanical_coupling` adds normalized scalar energy, force derivatives, dispersion, and a prescribed damping model. Full quantum dynamics and cooling are not proved.

`CryptoFullSuite.musig2_aggregation` includes scalar two-nonce signature completeness and a restricted cancellation barrier. Hash-based rogue-key resistance and the BIP 327 protocol are not proved.

`PhotonicsInterposerFullSuite.mithraic_collapse` includes scalar visibility bounds, exact zero/unit contrast criteria, fixed-maximum monotonicity and threshold validity. Quantum decoherence and automatic physical dump-port routing are not proved.
