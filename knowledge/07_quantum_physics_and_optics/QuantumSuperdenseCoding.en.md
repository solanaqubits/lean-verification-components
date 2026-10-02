---
id: QuantumSuperdenseCoding
language: en
section: quantum-physics
source: Verification/QuantumSuperdenseCoding.lean
source_sha256: b97f0289f7d571fb6aa827d37289b89f337261168d723460a98aac7df1a8a2ea
novelty: not-assessed
status: reviewed
---

# QuantumSuperdenseCoding

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumSuperdenseCoding.lean)

## Verified result

The explicit decoder applies CNOT followed by a scaled Hadamard on the first coordinate bit. For every ClassicalMsg it maps the prescribed Bell vector exactly to the corresponding computational basis vector. All four Bell vectors have norm one and every distinct pair has inner product zero.

## Assumptions and limitations

BellPairSetup assumes 2*s*s = 1 and uses the same s in the Bell vector and Hadamard map. Both signs are allowed; positive s selects the conventional Hadamard representative. These are exact identities over real four-vectors. Alice's encoder prescribes Bell vectors rather than deriving local Pauli operations. A measurement distribution, transmission process and communication-resource count are not defined. Channel noise, mixed Bell/Werner states, complex phases, qudit coding and the Holevo bound are not formalized.

The original encode/decode API remains available. Its coordinate/sign classifier requires positive s and is not a quantum measurement. The existing suite gains h_circuit; manual constructors must supply it. QuantumPhysicsFullSuite.superdense_coding accesses this component without adding an import. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumSuperdenseCoding.quantum_superdense_coding_master_suite`.
