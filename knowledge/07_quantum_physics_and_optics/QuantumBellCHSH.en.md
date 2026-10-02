---
id: QuantumBellCHSH
language: en
section: quantum-physics
source: Verification/QuantumBellCHSH.lean
source_sha256: e78a250199ec126ecfc0646eef7e9e254eb54ba6d08fb6b726fb0d8d7dc956d5
novelty: not-assessed
status: reviewed
---

# QuantumBellCHSH

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBellCHSH.lean)

## Verified result

The real CHSH expression factors as a0*(b0+b1)+a1*(b0-b1). For four jointly assigned outcomes in {-1,1}, its value is exactly -2 or 2, hence its absolute value is 2 and its value is at most 2. A convex combination of two scalars c1,c2 ≤ 2 is also at most 2 when both weights are nonnegative and sum to one.

The defined scalar tsirelsonBound = 2*sqrt(2) is strictly greater than 2 and than the exact rational 14/5; its square is 8, compared with the classical threshold's square 4. Key entry points are chsh_classical_deterministic_values, chsh_classical_bound, chsh_convex_ensemble_bound, quantum_violates_classical_bound, tsirelson_bound_squared and quantum_advantage_numerical_lower_bound.

## Assumptions and limitations

The classical assignment prescribes all four signs jointly; there is no physical measurement or hidden-variable probability space. Absolute equality to 2 applies to a deterministic assignment, not to its average. The ensemble theorem is only a two-component upper bound with assumed c1,c2 ≤ 2, not a general finite sum, an absolute-value bound from those assumptions alone, or an integral.

The name tsirelsonBound labels a number. No quantum state or observables produce it in this model, and no universal quantum upper bound or maximality is proved. The comparisons are scalar arithmetic, not a formalization of quantum violation or the operator Tsirelson theorem. Complex density matrices, Tr(ρ A ⊗ B), probability-measure integration over hidden variables, detection/locality loopholes, and multipartite GHZ/Mermin–Klyshko extensions are not formalized. Scientific novelty and first-formalization claims have not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `QuantumBellCHSH.quantum_bell_chsh_master_verification_suite`.
