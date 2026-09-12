---
id: QuantumNoCloningTheorem
language: en
section: quantum-physics
source: Verification/QuantumNoCloningTheorem.lean
source_sha256: 069c749182aaa5998a132f1698ae3dddbfaba1ddc6a644b6fd316be6399ebce1
novelty: not-assessed
status: reviewed
---

# QuantumNoCloningTheorem

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumNoCloningTheorem.lean)

## Verified result

For a real scalar x, the assumed equation x = x^2 implies x = 0 or x = 1. Consequently x cannot equal x^2 when 0 < x < 1. The endpoint values zero and one each satisfy the equation.

## Assumptions and limitations

The overlap equation is an explicit hypothesis, not a consequence derived from unitarity. There are no quantum states, ancillary state, inner product, tensor product, normalization condition or cloning operator in the model. The root theorem applies to all real scalars; the impossibility theorem is restricted to the positive interval (0,1), not all possible real or complex overlaps.

This supplies an algebraic step usable in a no-cloning proof, not a complete proof of the quantum no-cloning theorem. The endpoint lemmas establish only scalar equalities; they do not construct a cloner for orthogonal or identical states. Arbitrary-dimensional Hilbert spaces, complex unitary geometry, global-phase equivalence, approximate/probabilistic cloning and optimal-fidelity bounds are not formalized.

## Value and novelty

A reusable quadratic obstruction with explicit premises. The connection from quantum dynamics to the scalar equation remains a separate proof obligation. Scientific priority and first formalization have not been assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `QuantumNoCloningTheorem.quantum_no_cloning_master_verification_suite`.
