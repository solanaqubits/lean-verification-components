---
id: MasterSuite
language: en
section: verification
source: Verification/MasterSuite.lean
source_sha256: 7701a637edfeccbf5f1a93e8c96374906833d07f4cca1b796f4971658c7675ec
novelty: not-assessed
---

# MasterSuite

[Section](README.md) · [Lean source](../../Verification/MasterSuite.lean)

## Verified result

Eleven suites of selected theorems with 96 direct imports. The registry does not contain every declaration in the project. The Raft package includes reachable-state election safety, global Log Matching, operational Leader Completeness for actual commit events, and preservation of committed prefixes. The new bridge proves the operational conclusion directly; it does not instantiate the earlier whole-log VoterEvolution abstraction.

## Assumptions and scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

The Lean theorem types are authoritative for exact quantifiers and hypotheses.
Scientific priority and first-formalization claims have not been established.

## Proof entry points

- [`finsler_master_verification_suite`](../../Verification/MasterSuite.lean#L186)
- [`finsler_full_master_verification_suite`](../../Verification/MasterSuite.lean#L198)
- [`lamzouri_full_master_verification_suite`](../../Verification/MasterSuite.lean#L210)
- [`collatz_full_master_suite`](../../Verification/MasterSuite.lean#L229)
- [`crypto_full_master_suite`](../../Verification/MasterSuite.lean#L258)
- [`quantum_physics_full_master_suite`](../../Verification/MasterSuite.lean#L324)
- [`hopf_full_master_suite`](../../Verification/MasterSuite.lean#L359)
- [`proof_dag_full_master_suite`](../../Verification/MasterSuite.lean#L369)
- [`finance_defi_full_master_suite`](../../Verification/MasterSuite.lean#L379)
- [`finance_risk_full_master_suite`](../../Verification/MasterSuite.lean#L417)
- [`distributed_systems_full_master_suite`](../../Verification/MasterSuite.lean#L466)
- [`riemann_full_master_suite`](../../Verification/MasterSuite.lean#L500)
- [`verification_master_registry`](../../Verification/MasterSuite.lean#L538)

- [`photonics_interposer_master_suite`](../../Verification/MasterSuite.lean#L513)

## Verification

See the [validation record](../VERIFICATION.en.md) for the audited source snapshot.

`CryptoFullSuite.feldman_vss` includes scalar consistency and reconstruction against fixed coefficient commitments; no cryptographic secrecy is claimed.

`PhotonicsInterposerFullSuite.chip_layout` adds translation invariance and exact rational bounds checking. The separate `chip_placement_certificate` field certifies the exact stored 256-node placement. External digest binding remains outside the Lean proof.

`QuantumPhysicsFullSuite.optomechanical_coupling` adds normalized scalar energy, force derivatives, dispersion, and a prescribed damping model. Full quantum dynamics and cooling are not proved.

`CryptoFullSuite.musig2_aggregation` includes scalar two-nonce signature completeness and a restricted cancellation barrier. Hash-based rogue-key resistance and the BIP 327 protocol are not proved.

`PhotonicsInterposerFullSuite.mithraic_collapse` includes scalar visibility bounds, exact zero/unit contrast criteria, fixed-maximum monotonicity and threshold validity. Quantum decoherence and automatic physical dump-port routing are not proved.

`CryptoFullSuite.schnorr_batch` includes exact prime-field acceptance counts and fractions 1/q and (1/q)^k for fixed nonzero residuals under uniform independent coefficient sampling. These are finite counting ratios, not an implemented random sampler or a security theorem for Schnorr signatures.

`QuantumPhysicsFullSuite.standard_quantum_limit` proves the exact minimum and unique positive optimizer of A/I + B*I, balanced contributions, and a conditional standard-deviation bound. Calibration and omission of cross correlations are external modeling assumptions; quantum uncertainty and spectral detector dynamics are not derived.
