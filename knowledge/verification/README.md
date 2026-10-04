# Registry and axiom audit

[All sections](../README.md)

## Modules

| Module | Verified result |
|---|---|
| [MasterSuite](MasterSuite.en.md) | Eleven existing domain suites, three numerical certificate suites, and the historical milestone aggregate with 103 direct imports. The registry does not contain every declaration in the project. |
| [AxiomAudit](AxiomAudit.en.md) | The #audit_axioms command rejects disallowed transitive axioms of a selected declaration, including sorryAx. |

## Scope

Axiom auditing checks dependencies of formal declarations, not whether the model faithfully represents its intended application. Allowed standard axioms are not custom assumptions.

[Contributing](../CONTRIBUTING.en.md) · [Validation](../VERIFICATION.en.md)

- [MasterSuiteComponents](MasterSuiteComponents.en.md): shared packages with preserved names and hypotheses.

- [MasterHundredRegistry](../11_meta_registry/MasterHundredRegistry.md): milestone aggregation without circular imports or stronger domain claims.

The central registry now has 103 direct imports and the separate `rounding_certificates`, `sql_intervals` and `digest_bridge` fields. The historical MasterHundredRegistry remains unchanged. See [NumericRoundingCertificates](../12_numeric_certificates/NumericRoundingCertificates.md).
