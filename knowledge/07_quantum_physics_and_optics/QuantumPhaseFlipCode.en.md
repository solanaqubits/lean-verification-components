---
id: QuantumPhaseFlipCode
language: en
section: quantum-physics
source: Verification/QuantumPhaseFlipCode.lean
source_sha256: ab51edfd12f9f597bacead9e09e1e350b652b0ba2c3aff934abaa29d1d860a67
novelty: not-assessed
---

# QuantumPhaseFlipCode

[Section](../quantum-physics/README.md) · [Lean source](../../Verification/QuantumPhaseFlipCode.lean)

## Verified result

Explicit real matrices satisfy HZH = X under a² = 1/2 and Z² = I. The prescribed syndrome table for none, z1, z2, z3 is injective, and decoding its output recovers the original error label.

## Assumptions and scope

The Hadamard matrix uses a scalar normalization hypothesis, rather than a constructed value of 1/√2. Syndromes are defined by a table, not derived from stabilizer measurements. Unsupported natural-number syndrome pairs default to none; the inverse property concerns only the table's image.

Logical codewords, their orthogonality, the three-qubit state space, stabilizer commutation, and preservation of the code subspace are not defined or proved. `error_correction_identity` recovers a label, not an arbitrary quantum state. A continuous noise channel and general N-qubit stabilizer theory are also outside this model. Scientific priority is not established.

## Proof entry points

- [`hadamard_conjugation_Z_to_X`](../../Verification/QuantumPhaseFlipCode.lean#L36)
- [`decode_syndrome_correct`](../../Verification/QuantumPhaseFlipCode.lean#L65)
- [`syndrome_measure_injective`](../../Verification/QuantumPhaseFlipCode.lean#L69)
- [`pauliZ_involutive`](../../Verification/QuantumPhaseFlipCode.lean#L78)
- [`error_correction_identity`](../../Verification/QuantumPhaseFlipCode.lean#L82)
- [`quantum_phase_flip_master_verification_suite`](../../Verification/QuantumPhaseFlipCode.lean#L94)

## Value and validation

These matrix and decoding lemmas can support a future state-space model. The next step is to derive the syndrome table from operators and prove actual state recovery. See the [validation record](../VERIFICATION.en.md).
