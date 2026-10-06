---
id: QuantumGroverArbitraryPhase
language: en
section: quantum-physics
source: Verification/QuantumGroverArbitraryPhase.lean
source_sha256: 4afc3210de96950872b34e861b483e5a29bd0e50fb11364e48bfefd18c8eb59f
novelty: not-assessed
status: reviewed
---

# QuantumGroverArbitraryPhase

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumGroverArbitraryPhase.lean)

## Model and conventions

The state space is Fin 4 → ℂ with one marked coordinate ω. The uniform state has
four amplitudes 1/2. For z=exp(iφ), the oracle multiplies only the marked coordinate
by z. Diffusion acts on every coordinate as vᵢ+(exp(iψ)-1)(∑ⱼvⱼ)/4. The step applies
the oracle first. Neither the state type nor the norm-preservation theorem assumes
normalization. successWeight is the squared modulus of the marked amplitude; its
interpretation as a probability uses normalization and the Born rule.

## Unitarity and the complex plane

oracle_linear and diffusion_linear prove complex linearity. oracle_adjoint and
diffusion_adjoint identify their adjoints explicitly by conjugating the phase.
phase_operators_unitary proves both inverse orders. arbitrary_grover_adjoint and
arbitrary_grover_unitary establish the adjoint and the two identities G†G=GG†=I
for the composite. arbitrary_grover_inner_preservation preserves the full
Hermitian product, and arbitrary_grover_l2_preservation gives ∑‖Gvᵢ‖²=∑‖vᵢ‖².
These are coordinate operator identities, not assumptions about a matrix.

A twoLevel state has marked amplitude a and common unmarked amplitude b. The
actual operators imply the recurrence, with z=exp(iφ), w=exp(iψ):

    a' = z*a + (w-1)*(z*a+3*b)/4
    b' = b + (w-1)*(z*a+3*b)/4.

InPlane is exactly the complex span of the marked basis vector and the normalized
uniform vector on the other three coordinates. plane_orthonormal proves unit
lengths and orthogonality; plane_coordinates_unique proves independent coordinates;
plane_linear_closed proves closure under complex linear combinations.
step_twoLevel derives the recurrence from the four-coordinate operators.
arbitrary_grover_plane_invariant requires no equality of phases. The matched-phase
theorem is a specialization. unequal_phases_still_invariant explicitly refutes the
claim that unequal phases must cause leakage out of this complex plane.
stateAt_normalized and stateAt_in_plane hold for every natural iteration count
and every pair of real phases. No real-plane rotation or full Høyer phase-matching
criterion is inferred from complex-plane invariance.

## Exact one-step probability

Starting at uniform and setting φ=ψ gives

    marked amplitude   = (z²+6*z-3)/8
    unmarked amplitude = (z+1)²/8
    P(φ) = 1 - 3*(1+cos φ)²/16.

arbitrary_grover_success_formula proves this identity for every real φ;
arbitrary_grover_success_continuous proves continuity. arbitrary_grover_success_iff
proves P(φ)=1 iff cos φ=-1. arbitrary_grover_zero_overshoot_exact supplies φ=π.
Thus this one-target, four-state example already succeeds with the canonical phase;
it does not demonstrate a noncanonical fractional improvement. Regression values
are P(0)=1/4, P(π/2)=13/16 and P(π)=1.

## Compatibility and the global sign

phase_oracle_pi agrees with the existing singleton oracle on every embedded real
state. Our phase_diffusion_pi is the negative of the existing diffusion, so
arbitrary_grover_reduction_to_canonical proves G(π,π)=-G_canonical, not equality.
arbitrary_grover_reduction_to_legacy establishes the same bridge to the original
QState4 and TargetItem API for arbitrary real inputs. canonical_measurement_weights
proves equality of all squared outcome amplitudes. canonical_uniform_signed gives
the negative of the target vector, while canonical_sign_not_literal proves these two signed
vectors are unequal. Existing real proofs and interfaces are unchanged.

## Evidence, references and limits

See the [design contract](../../docs/grover-arbitrary-phase-design.en.md) and
[verification report](../../docs/grover-arbitrary-phase-verification.en.md).
Primary references are Høyer, [On Arbitrary Phases in Quantum Amplitude Amplification](https://arxiv.org/abs/quant-ph/0006031)
and Long, [Grover Algorithm with zero theoretical failure rate](https://arxiv.org/abs/quant-ph/0106071).
The new formalization does not claim their general phase-matching or scheduling
results. It covers one target, dimension four and exact complex algebra. Arbitrary
N, multiple targets with arbitrary phases, circuit synthesis, query complexity,
noise, physical phase shifters and measurement implementations are outside scope.
Python, JSON/SHA-256, SimLab procedures and binding external inputs to bytes remain
separate obligations. Scientific novelty is not assessed.
