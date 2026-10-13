---
id: QuantumNoBroadcastingMixed
language: en
section: quantum-physics
source: Verification/QuantumNoBroadcastingMixed.lean
source_sha256: 8ac538ccc179f892e5860511807a7fa1f1c66421273c6b0d7fd82723e406f1b4
novelty: not-assessed
status: reviewed
---

# No-broadcasting for finite-dimensional mixed states

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumNoBroadcastingMixed.lean)

## Model and theorem

`IsDensityMatrix` means positive semidefinite with complex trace one; positivity
includes Hermiticity. A `CPTPMap d` is a complex-linear map from all d-by-d
matrices to matrices indexed by `Fin d × Fin d`, preserving trace on every input.
Complete positivity independently requires positivity of every finite matrix-block
amplification. No Kraus witness, commutativity, fidelity condition or broadcasting
property is assumed in the channel structure.

`CanBroadcast ρ σ` requires one channel whose two partial traces reproduce each
input. Outputs may be correlated. `partial_trace_B` reuses the operator partial
trace from `QuantumPOVMNaimarkDilation`; the other trace is defined explicitly.

`quantum_no_broadcasting_theorem` proves, for arbitrary density matrices,

    CanBroadcast ρ σ ↔ ρ * σ = σ * ρ.

There is no positive-definiteness, distinct-eigenvalue or full-support hypothesis.
The API quantifies over every natural d; trace-one density matrices cannot exist
when d = 0. The requested d ≥ 1 cases follow directly.

## Constructive sufficiency

Commuting Hermitian matrices admit a joint orthonormal eigenbasis. In that basis,
Kraus operators |jj⟩⟨j| give a measure-and-prepare channel. Unitary conjugation
transports it to the original coordinates. Completeness of the Kraus family
proves trace preservation, and a direct amplification proof establishes complete
positivity for every ancilla dimension. Both marginals equal the original
matrix for diagonal inputs. A mixed qubit regression exhibits an output different
from ρ tensor ρ, so product outputs are not smuggled into the definition.

## Unconditional necessity

The proof uses a symmetric logarithmic derivative and a sum of positive squares;
it does not require fidelity monotonicity or assume an equality-case theorem.

1. `Channel.exists_kraus` derives a finite Kraus representation from block complete
   positivity by factoring the positive Choi matrix. It adds no assumption to CPTP.
2. `exists_symmetric_logarithmic_derivative` constructs Hermitian A satisfying
   Aτ + τA = 2ρ for τ = ρ + σ. In an eigenbasis of τ, its coefficients are
   2ρ_ij / (λ_i + λ_j). If the denominator vanishes, positivity of both inputs
   forces the relevant row of ρ to vanish. Lean's zero-division convention is
   therefore used only in a proved zero block; spectral degeneracy is covered.
3. `kraus_quadratic_saturation` expands the squared defects
   ((A tensor 1) K_j S − K_j A S), where SS† = τ. Trace preservation and the
   fixed marginal equations force their total squared norm to zero. Each defect
   vanishes. The same argument applies to the second output factor.
4. Therefore (A tensor 1) E(τ) = (1 tensor A) E(τ). Hermiticity and cyclicity
   of the partial trace give Aτ = τA. The derivative equation then gives
   ρ = Aτ and hence ρσ = σρ.

The intermediate `broadcasting_commutes_of_sld` has an explicit derivative witness;
`quantum_broadcasting_necessity` constructs it and has only density and broadcasting
hypotheses. Earlier conditional unitary-intertwiner lemmas remain available as
algebraic results; they are not needed to close the theorem.

## Pure states, bridges and regressions

For normalized vectors, `quantum_pure_state_phase_criterion` proves broadcasting
iff their inner product is zero or they differ by a unit-modulus global phase.
Identical mixed states are broadcast by the linear channel X ↦ X tensor ρ.
`bridge_to_quantum_no_cloning` embeds the actual unitary-with-blank density-cloning
model into CPTP channels and derives the pure-state obstruction from the general theorem.

The live Lean regression covers d = 1, commuting mixed qubits, orthogonal projectors,
unitary changes of basis, correlated output, phase invariance, the nonbroadcastable
|0⟩/|+⟩ pair, arbitrary ancillas, a three-dimensional common kernel with repeated
spectrum, general necessity, and the registry suite.
`QuantumNoBroadcastingMixedSuite` / `verification_suite` packages the full equivalence,
both directions, pure-state phase criterion, identical states, qubit obstruction and bridge.

## Verification and Clean Water

The release checks are strict module verify/audit, full `lake build --wfail`,
`verify-all`, live unittest, the registry axiom audit and knowledge validation.
Measured results are recorded separately. Permitted axioms are only propext,
Classical.choice and Quot.sound. Mathematical novelty is not assessed.

Infinite dimensions, approximate broadcasting, continuous variables, thermodynamic
resource reductions and physical measurement implementations are not modeled.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Public release validation is recorded in [v0.5.50](../../docs/release-v0.5.50.en.md).

Theorem reference: [Barnum, Caves, Fuchs, Jozsa and Schumacher](https://arxiv.org/abs/quant-ph/9511010).
The Lean necessity proof uses the quadratic argument above rather than formalizing
the paper's fidelity proof. No external formalization library was added.
