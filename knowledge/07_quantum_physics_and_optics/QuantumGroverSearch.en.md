---
id: QuantumGroverSearch
language: en
section: quantum-physics
source: Verification/QuantumGroverSearch.lean
source_sha256: 5cbc65cf91941fbf9c483045f1afcdbb963f2e6f4502bd7d0fdca18635978faf
novelty: not-assessed
status: reviewed
---

# QuantumGroverSearch

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumGroverSearch.lean)

## Verified result

The existing real-vector reflection model, four exact search results and squared-overlap theorem are preserved. TargetItem provides four target labels; phaseOracle flips the corresponding coordinate. A bridge theorem equates this oracle with the existing reflection at the basis target. Another theorem expresses the existing diffusion as inversion about the coordinate mean. One defined composition from uniformSuperposition equals targetToBasis for every target, has overlap one, and the initial vector has norm squared one.

## Assumptions and limitations

This is an exact four-dimensional real-vector calculation for one marked basis target. No database, gate circuit, oracle query-cost model, measurement process or noise channel is encoded. Unit overlap is an amplitude; the older squared-overlap result is retained. The equality (pi/4)*sqrt(4)=1 is false: that expression equals pi/2. The one-iteration result is established directly by the operators, not by that asymptotic estimate.

The original QState4 fields x0..x3 remain; x00..x11 are accessors, not new record fields. Old definitions and suite fields are preserved; new target-interface fields extend the suite. QuantumPhysicsFullSuite.grover_search accesses the existing grover field. No direct import is added. Larger search spaces, general iteration analysis, complex gates, physical measurement and depolarizing noise are outside this model. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumGroverSearch.quantum_grover_master_verification_suite`.
