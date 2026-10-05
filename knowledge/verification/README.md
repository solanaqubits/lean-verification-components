# Registry and axiom audit

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [MasterSuite](MasterSuite.en.md) | Eleven existing domain suites, four numerical certificate suites, and the historical milestone aggregate with 107 direct imports. The registry does not contain every declaration in the project. |
| [AxiomAudit](AxiomAudit.en.md) | The #audit_axioms command rejects disallowed transitive axioms of a selected declaration, including sorryAx. |

## Scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)

- [MasterSuiteComponents](MasterSuiteComponents.en.md): shared packages with preserved names and hypotheses.

- [MasterHundredRegistry](../11_meta_registry/MasterHundredRegistry.md): milestone aggregation without circular imports or stronger domain claims.

The central registry now has 107 direct imports and the separate `rounding_certificates`, `sql_intervals`, `digest_bridge` and `sql_gap_bounds` fields. The historical MasterHundredRegistry source and manifest remain unchanged; its distributed package inherits the new chandy_lamport field. See [NumericRoundingCertificates](../12_numeric_certificates/NumericRoundingCertificates.md).

The quantum package also inherits `phase_estimation`: exact two-bit phase recovery under a supplied normalized eigenstate promise. See [QuantumPhaseEstimation](../03_quantum_physics_and_optics/QuantumPhaseEstimation.md).

The quantum package also inherits `grover_multiple_targets`: exact N=4 subset dynamics and proper-subset plane invariance. See [QuantumGroverMultipleTargets](../03_quantum_physics_and_optics/QuantumGroverMultipleTargets.md).
