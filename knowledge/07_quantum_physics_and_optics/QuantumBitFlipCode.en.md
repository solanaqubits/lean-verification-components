---
id: QuantumBitFlipCode
language: en
section: quantum-physics
source: Verification/QuantumBitFlipCode.lean
source_sha256: 5f7ede0e203a2c532c6d35ce2fd3dce13af63a9a265914a14cd71a6e9d3d9717
novelty: not-assessed
status: reviewed
---

# QuantumBitFlipCode

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBitFlipCode.lean)

## Verified result

The encoding places real amplitudes alpha and beta at coordinates 000 and 111. For any nonzero pair of amplitudes and each of no error, flip1, flip2 and flip3, the supplied classifier followed by its coordinate permutation recovers the encoded vector exactly. Under alpha²+beta² = 1, the encoded vector has dot product one with itself.

## Assumptions and limitations

This is a three-qubit repetition-code model for bit flips X, not phase flips or the full nine-qubit Shor code. QState8 is a real coordinate record without a normalization constraint. The recovery assumption alpha ≠ 0 or beta ≠ 0 means nonzero input, not unit norm; the normalization theorem has a separate hypothesis. The flip3 proof does not need the nonzero-input hypothesis retained in its interface.

measureSyndrome inspects exact nonzero coordinates and returns an error label, not a pair of Boolean parity outcomes. It is not defined by Z1Z2/Z2Z3 projectors, and no orthogonality or Born-rule measurement theorem is supplied. On an arbitrary vector with support in multiple branches it selects the first matching branch. Recovery is proved only for the specified single-error images of the encoding; there is no physical implementation of this nonlinear classifier or general channel-correction theorem.

Complex amplitudes, phase errors Z, Kraus noise channels, density matrices, the full Shor code and fault-tolerance thresholds are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumBitFlipCode.quantum_bit_flip_code_master_verification_suite`.
