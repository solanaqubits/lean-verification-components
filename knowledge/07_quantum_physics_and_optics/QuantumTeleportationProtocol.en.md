---
id: QuantumTeleportationProtocol
language: en
section: quantum-physics
source: Verification/QuantumTeleportationProtocol.lean
source_sha256: 80fcb2ce6b0901d37c2fcffc473cf070df52b856c1adb221f3e67353fa7935f1
novelty: not-assessed
status: reviewed
---

# QuantumTeleportationProtocol

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumTeleportationProtocol.lean)

## Verified result

The existing complex QubitState interface and its four exact recovery theorems remain available. A real QState2 interface adds I, X, Z and ZX corrections, AliceOutcome labels, prescribed branch states and exact recovery for all four branches. Recovery holds for arbitrary amplitude pairs, without normalization. Under alpha²+beta²=1, the assigned scalar weight (alpha²+beta²)/4 equals 1/4. The original sum-of-four-quarters identity is retained.

## Assumptions and limitations

Branch states are prescribed directly. No entangled three-qubit preparation, CNOT/H evolution, measurement projectors, Born-rule distribution or quantum channel is defined. The scalar weight theorem has no outcome argument and does not derive measurement probabilities. No operator-unitarity theorem is added. Complex two-amplitude recovery was already formalized; a full complex eight-dimensional teleportation circuit, decoherence and tomography are not.

The old API and MasterSuite.teleportation field are retained. QuantumPhysicsFullSuite.quantum_teleportation is an alternate accessor. The formal suite has additional real-interface fields, so manual constructors need to supply them. This extends an existing module and adds no direct import. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumTeleportationProtocol.quantum_teleportation_master_verification_suite`.
