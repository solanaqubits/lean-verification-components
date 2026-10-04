---
id: QuantumPhaseEstimation
language: en
section: quantum-physics
source: Verification/QuantumPhaseEstimation.lean
source_sha256: 73b042a0deffd448b9ef434570890c0f69d9d2072315ae8030bdb84b3a6a7690
novelty: not-assessed
status: reviewed
---

# QuantumPhaseEstimation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumPhaseEstimation.lean)

## Exact finite complex model

Two control qubits use the ordered basis 00, 01, 10, 11 and one target qubit has two complex coordinates. DyadicPhase2 stores b1 (most significant) and b2 (least significant); phaseIndex = 2*b1+b2 and phaseValue = b1/2+b2/4. The four supported phases are exactly 0, 1/4, 1/2, 3/4.

fourierMatrix(j,k) = (1/2)*i^(j*k) is proved equal to the positive-exponent complex exponential kernel. inverseFourierMatrix is its conjugate transpose; inverse_fourier_exponential identifies the negative-exponent kernel. Both composition orders equal the identity, and both transforms preserve the sum of squared complex moduli for arbitrary control vectors. No approximate floating-point exponential evaluation is used.

qpePreState is defined by the complex exponential at the actual phaseValue. Its equality with the appropriate Fourier column is proved, rather than assumed. qpe_pre_state_normalized gives norm squared 1. qpe_inverse_qft_exact gives the full output basis vector; qpe_inverse_qft_exact_cancellation gives zero off the correct index. qpe_deterministic_success gives squared-modulus weight 1 at that index. qpe_reconstructs_dyadic_bits recovers the two bits in the declared order.

## Controlled operations and target state

hadamardPair is the explicit normalized four-coordinate Walsh kernel for the paired Hadamards. Its norm preservation and preparation of the uniform state from basis 00 are proved. controlled applies a supplied complex-linear target map only when the selected control bit is set. runControlled first applies U at the low bit, then U composed with U at the high bit.

controlled_powers_kickback derives the control/target product state from the eigenstate equation Uu = phaseRoot • u (scalar multiplication by phaseRoot). phaseRoot_exponential identifies this scalar with exp(2*pi*i*phaseValue). The proof actually composes the two controlled maps; it does not define their output to be qpePreState. The algebraic identity only needs linearity and the eigenstate equation.

UnitaryEigenInput additionally supplies a norm-preserving target map and a normalized eigenstate. These are input hypotheses, not results of an eigenstate-preparation algorithm. inverseControl applies the inverse Fourier kernel to the control coordinates of the joint eight-coordinate state. qpe_joint_exact preserves the target state and produces the correct control basis vector. qpe_joint_distribution proves weights 1 at the true index and 0 elsewhere; qpe_circuit_normalized preserves total norm. qpe_observed_bits states that any index with positive weight decodes to the original bits.

Squared-modulus and marginal weights have the usual Born-rule interpretation; no physical measurement device or random sampler is implemented or certified.

## Evidence and boundaries

Compiler regressions cover all four phase values, a normalized target with two nonzero complex coordinates, symbolic unitary inputs, normalization, and recovery from the exponential eigenstate equation. Explicit counterchecks distinguish the inverse Fourier sign and the assignment of U versus U² to the two control bits. The zero target cannot satisfy normalization.

The suite is integrated into QuantumPhysicsFullSuite through MasterSuiteComponents. Existing aggregates using that package inherit the new field; the historical hundred-import manifest is not changed. Current counts and audits are recorded in the [validation record](../VERIFICATION.en.md).

This is the exact two-bit case under an exact eigenstate promise. Other rational phases, irrational phases, approximation error bounds, leakage profiles, arbitrary register size, elementary-gate synthesis of the inverse QFT, state-preparation cost, noisy gates, hardware, and Shor's algorithm are outside the model. No scientific novelty is claimed.

[IBM Quantum: phase-estimation procedure](https://quantum.cloud.ibm.com/learning/en/courses/fundamentals-of-quantum-algorithms/phase-estimation-and-factoring/phase-estimation-procedure) describes phase kickback and the Fourier convention used here. The theorem statements above specify this module's narrower exact finite scope.
