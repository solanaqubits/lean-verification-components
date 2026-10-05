---
id: QuantumGroverMultipleTargets
language: en
section: quantum-physics
source: Verification/QuantumGroverMultipleTargets.lean
source_sha256: 7dbcf830bde6e8469b45f30b449da35c3806f2a2aa5b19a183b92e3820390f6b
novelty: not-assessed
status: reviewed
---

# QuantumGroverMultipleTargets

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumGroverMultipleTargets.lean)

## Operators and compatibility

The state is Fin 4 → ℝ; normalization is not built into the type. A finite target set T defines the diagonal phase oracle: each marked coordinate is negated and every other coordinate is retained. Diffusion is inversion about the coordinate mean. groverStep composes these actual coordinate operators. stateAt starts with four amplitudes 1/2 and iterates the step. successWeight is the sum of squared marked amplitudes; it lies between zero and normSquared and is a probability only on normalized states under the Born interpretation.

Both oracle and diffusion are involutions and preserve norm on arbitrary real states. The composed step preserves norm; every stateAt is normalized. toLegacy/fromLegacy give inverse coordinate conversions to the existing QState4 record and preserve its inner product. legacy_diffusion identifies the original diffusion. singleton_step_legacy equates the new singleton step with the original basis-target operation on every input, and singleton_exact_legacy reuses the existing exact-search theorem. QuantumGroverSearch and its old suite interfaces are unchanged.

## Derived dynamics for every subset

For a state whose marked coordinates are a and unmarked coordinates b, put m=|T|. The coordinate operators imply

    a' = (1-m/2)*a + (4-m)/2*b
    b' = -m/2*a + (1-m/2)*b.

This recurrence is derived, not assumed as an operator definition. stateAt_twoLevel proves its correspondence with the actual k-fold execution for every natural k. The initial pair is (1/2,1/2), and success_recurrence gives m*a_k². One step gives marked amplitude (3-m)/2 and unmarked amplitude (1-m)/2.

| Number of targets | Exact success weight after k steps |
|---|---|
| 0 | 0; the initial uniform state stays fixed |
| 1 | 1 when k mod 3 = 1, otherwise 1/4 |
| 2 | 1/2 for every natural k |
| 3 | 0 when k mod 3 = 1, otherwise 3/4 |
| 4 | 1; the state is (-1)^k times the uniform state |

For three targets the first step is zero on all targets and -1 on the only unmarked coordinate. Its unmarked success weight is 1. For two targets no integer number of these standard iterations from uniform reaches success 1. Empty targets do not make the whole step the identity on arbitrary inputs: diffusion still acts; the fixed-state theorem concerns uniform.

## The invariant plane and a corrected reflection claim

For 0 < |T| < 4, marked and unmarked are normalized uniform vectors on the two disjoint supports. plane_orthonormal proves their two unit inner products and zero mutual inner product. plane_coordinates_unique proves uniqueness of the two coefficients. plane_linear_closed establishes closure under real linear combinations; plane_invariant and stateAt_in_plane establish invariance under the step and inclusion of the iterates. No claim is made that these two vectors span all of ℝ⁴. The name unmarked denotes one vector in the orthogonal complement, not the full three-dimensional complement of the marked line. Topological closedness is not a separate theorem here.

In ordered coordinates (marked, unmarked), plane_step gives the matrix [[c,s],[-s,c]], where c=1-m/2 and s=√m*√(4-m)/2. rotation_unit proves c²+s²=1. This specifies orientation algebraically; no trigonometric angle or general sin²((2k+1)θ) theorem is claimed. The endpoint target sets use direct coordinate theorems rather than a degenerate normalized basis.

The full oracle reflects the entire marked coordinate subspace, not just the marked uniform line. plane_rankOne_agrees proves agreement with rank-one reflection for states in the symmetric plane. rankOne_not_general refutes agreement on arbitrary inputs using T={0,1}, v=(1,-1,0,0). Conversely rankOne_agrees_outside_plane exhibits T={0}, v=(0,1,-1,0), where agreement holds outside the plane. Thus plane membership is sufficient, not necessary.

## Evidence and limits

Compiler regressions check legacy compatibility on arbitrary states, nonadjacent pairs, symbolic iteration counts, signed three-target outputs, repeated iterations, empty/full sets, nonnormalized states, unique plane coordinates, both reflection counterexamples and degenerate endpoint vectors. Counts and audits are recorded in the [verification report](../../docs/grover-multiple-verification.en.md).

This is exact four-dimensional real-amplitude algebra. Arbitrary N, query complexity, oracle construction cost, unknown-count scheduling, fractional phase reflections, complex gate circuits, measurement implementations, noise and hardware are outside scope. New probability statements retain the normalization and Born interpretation; no physical experiment is certified. Scientific novelty is not assessed.
