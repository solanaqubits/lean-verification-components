---
id: QuantumBernsteinVazirani
language: en
section: quantum-physics
source: Verification/QuantumBernsteinVazirani.lean
source_sha256: 166a4c7294a1b07cc939bb05eb077fea05df9e50acdb432094d9af5832ea6243
novelty: not-assessed
status: reviewed
---

# QuantumBernsteinVazirani

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBernsteinVazirani.lean)

## Verified result

For each of the four masks, the explicit composition hadamard2 (oracle s (hadamard2 basis00)) equals maskToBasis s. The real inner product of the output with the target basis vector is exactly one. Four case theorems are combined into a universal reconstruction theorem.

## Assumptions and limitations

The model uses four real amplitudes and a prescribed Hadamard transform and phase-sign table. The state type does not require normalization. No separate Boolean dot-product function or proof relating it to the phase table is supplied. The composition contains one oracle application syntactically, but query-cost semantics and a classical query lower bound are not formalized.

The unit-overlap theorem is an algebraic identity, not a Born-rule measurement theorem; there are no projectors or probability distributions. A physical oracle circuit, ancilla, general tensor-product construction, operator unitarity proof, masks longer than two bits, complex amplitudes, gate errors and depolarizing noise are not formalized.

## Value and novelty

A checked finite-dimensional reconstruction identity for the specified ideal operators. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumBernsteinVazirani.quantum_bernstein_vazirani_master_verification_suite`.
