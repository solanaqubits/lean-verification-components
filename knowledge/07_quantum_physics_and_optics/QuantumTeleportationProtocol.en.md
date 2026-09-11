---
id: QuantumTeleportationProtocol
language: en
section: quantum-physics
source: Verification/QuantumTeleportationProtocol.lean
source_sha256: bcc448fb6700e5c25859f93495dbc2b5893e6f74ca03cc2934f302f711cf78fa
novelty: not-assessed
status: reviewed
---

# QuantumTeleportationProtocol

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumTeleportationProtocol.lean)

## Verified result

Four explicitly prescribed complex amplitude pairs are restored by the corresponding I, Z, X or ZX matrix. The universal theorem proves exact structural equality with the input pair for every branch label. For psiMinus the received pair is (-beta, alpha), and ZX maps it to (alpha, beta); this fixes the sign convention. A separate arithmetic theorem proves that four constants 1/4 sum to one.

## Assumptions and limitations

QubitState is an arbitrary element of complex two-dimensional coordinate space, with no normalization condition. BellMeasurement is a four-constructor label type. Received states and corrections are defined by tables, not derived from a Bell-pair preparation, circuit or measurement. Selecting one of four outcomes requires two classical bits.

Bell basis vectors, orthogonality, measurement projectors and Born-rule probabilities are not defined. The sum-of-quarters theorem does not establish that these branches occur with probability 1/4. The matrices are explicit, but an adjoint-based unitarity theorem is not included. The eight-dimensional three-qubit tensor space, entanglement with an external system, physical transmission, quantum noise and memory are outside this model. The theorem name fidelity_exact denotes state equality; no fidelity function is defined.

## Value and novelty

Reusable correction identities for a future derivation of the branch table from a complete state-space model. Mathematical novelty and first-formalization status have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumTeleportationProtocol.quantum_teleportation_master_verification_suite`.

- [`teleportation_fidelity_exact`](../../Verification/QuantumTeleportationProtocol.lean#L73)
- [`branch_probabilities_sum`](../../Verification/QuantumTeleportationProtocol.lean#L82)
