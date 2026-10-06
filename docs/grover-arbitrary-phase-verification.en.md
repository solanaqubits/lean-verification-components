# Arbitrary phase Grover verification record

Baseline: `ac3e2363e6711b981f31e1cc782ec1b51cf69b35`.

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

See the [design contract](grover-arbitrary-phase-design.en.md) and
this verification record.
Primary references are Høyer, [On Arbitrary Phases in Quantum Amplitude Amplification](https://arxiv.org/abs/quant-ph/0006031)
and Long, [Grover Algorithm with zero theoretical failure rate](https://arxiv.org/abs/quant-ph/0106071).
The new formalization does not claim their general phase-matching or scheduling
results. It covers one target, dimension four and exact complex algebra. Arbitrary
N, multiple targets with arbitrary phases, circuit synthesis, query complexity,
noise, physical phase shifters and measurement implementations are outside scope.
Python, JSON/SHA-256, SimLab procedures and binding external inputs to bytes remain
separate obligations. Scientific novelty is not assessed.

## Validation

- **113 direct imports**, **153 Lean files** in Verification/.
- Fresh project `lake build --wfail`: **3535 jobs**, no warnings. The isolated project build directory was moved aside before compiling. Pinned dependency caches were retained; Mathlib was not rebuilt entirely from source.
- Module verify and audit: **422 declarations** in the transitive audited closure, clean.
- Full verify-all and independent pinned audit: **11475 declarations**, only propext, Classical.choice, Quot.sound.
- **51 private live tests**, **93.733 seconds**, no errors, failures or skips.
- AxiomAudit registry hook, catalog, source hashes and integration idempotence pass.
- Export covers all **154 Lean sources**, including the root, byte for byte, plus the new regressions and English documentation. Only English cards are exported; simulations are excluded.
- Original HEAD and **406** tracked-file hashes remain intact. This task wrote nothing in simulations; concurrent SimLab activity is not reverted or interpreted as immutable.

```bash
python3 tools/verifier_skill.py verify Verification/QuantumGroverArbitraryPhase.lean
python3 tools/verifier_skill.py audit Verification/QuantumGroverArbitraryPhase.lean
python3 tools/verifier_skill.py integrate Verification.QuantumGroverArbitraryPhase QuantumGroverArbitraryPhaseSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

Independent audit: leanprover-community/axiom-audit v0.1.2, pinned commit
`46024e005996495c65ef609368e11ab39c4222e3`, root Verification and allowlist
`propext,Classical.choice,Quot.sound`. The AxiomAudit registry hook is an additional check.
Only private main is published by this task; no public release is created.
