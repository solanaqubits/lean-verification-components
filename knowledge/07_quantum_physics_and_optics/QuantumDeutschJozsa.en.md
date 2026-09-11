---
id: QuantumDeutschJozsa
language: en
section: quantum-physics
source: Verification/QuantumDeutschJozsa.lean
source_sha256: 93cce3bdf53d1809912de5ee8906a2b204d89ef72409034bf4ac2df7302ccdb7
novelty: not-assessed
status: reviewed
---

# QuantumDeutschJozsa

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumDeutschJozsa.lean)

## Verified result

Every function Bool → Bool is exactly one of constant or balanced, using equality or inequality of its two values. The prescribed real amplitudes have sum of squares one. Constant functions yield squared amplitudes (1,0), balanced functions yield (0,1), and both converse criteria are proved.

## Assumptions and limitations

The results cover all four one-bit truth tables. phaseSign assigns ±1 and amp0/amp1 are defined by closed-form expressions using f false and f true. No circuit, state preparation, phase-kickback derivation, query-count semantics or classical lower bound is defined. Therefore the module does not prove execution with one oracle query or a quantum query advantage. It verifies the resulting amplitude formulas.

The sum-of-squares identity normalizes those two numbers; it is not a theorem of operator unitarity. The physical unitary U_f, ancillary qubit, Born-rule measurement model, n > 1 registers, tensor Hadamard transform and noisy implementations are not formalized.

## Value and novelty

Checked finite classification and amplitude identities that can support a later circuit-level model. Mathematical novelty and first-formalization claims have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumDeutschJozsa.quantum_deutsch_jozsa_master_verification_suite`.

- [`constant_iff_amp0_sq_one`](../../Verification/QuantumDeutschJozsa.lean#L39)
- [`balanced_iff_amp1_sq_one`](../../Verification/QuantumDeutschJozsa.lean#L43)
