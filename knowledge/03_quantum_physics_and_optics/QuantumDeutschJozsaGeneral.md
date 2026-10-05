---
id: QuantumDeutschJozsaGeneral
language: en
section: quantum-physics
source: Verification/QuantumDeutschJozsaGeneral.lean
source_sha256: 212724069433680933166519c16daac4314cd3396294090e35589ad64f6c767f
novelty: not-assessed
status: reviewed
---

# QuantumDeutschJozsaGeneral

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumDeutschJozsaGeneral.lean)

## Operators and circuit

Bits n is Fin n → Bool and has cardinality 2^n, including a singleton when n=0. State n assigns real amplitudes to these bit strings; normalization is not imposed by the type. The zero bit string labels a unit basis vector, not the zero state vector.

The character is χ(x,y)=∏ᵢ sign(xᵢ AND yᵢ), with sign false=1 and sign true=-1. hadamard v(y)=(1/√(2^n))∑ₓχ(x,y)v(x). character_orthogonal proves row orthogonality, hadamard_involution proves H(Hv)=v and hadamard_inner proves preservation of the real inner product for arbitrary states. hadamard_add and hadamard_smul establish linearity. kernel_tensor and splitBits identify the normalized kernel recursively with the tensor product of a one-bit Hadamard and the n-bit kernel. No integer encoding or endian-dependent ordering is required.

phaseOracle multiplies each amplitude by sign(f x). Its linearity, involution and inner-product preservation are proved. runDJ is the actual composition H ∘ phaseOracle ∘ H applied to the zero basis state. output_amplitude derives the complete formula

    runDJ f(y) = (1/2^n) ∑ₓ sign(f x) χ(x,y).

This formula is a theorem, not the definition of the circuit output. run_normalized holds for every Boolean function, including functions outside the promise.

The ancilla minus has amplitudes ±1/√2. minus_prepared derives it from the one-bit |1⟩ input, and hadamard_one relates that explicit operator to the general kernel. xorOracle acts on joint amplitudes by ψ(x,b XOR f x), a linear norm-preserving involution. dj_phase_kickback proves its equivalence to phaseOracle on v⊗minus for arbitrary v. jointRun explicitly applies input H, XOR and input H, and joint_run_eq proves that its output is runDJ f⊗minus. Joint normalization and equality of the input marginal weight to the scalar squared amplitude are proved.

## Promise and finite counting

The scalar definitions also apply to any finite type α. IsConstant requires equality of all function values. IsBalanced means 2*trueCount=card α; counts_partition and balanced_counts connect this to equal true/false counts. zeroStateAmplitude is the mean of the signs. sum_sign expresses the sum using the counts.

For positive cardinality, a constant function has zeroStateProb=1; a balanced function has zero amplitude and weight zero. Under DJPromise, the two weights characterize the two classes. No extra even-cardinality assumption is required for separation: balancing itself forces even cardinality, whereas a constant function can live on an odd nonempty domain. On an empty generic domain the constant and balanced predicates both hold and the Lean division convention gives mean zero, so nonemptiness must not be dropped.

zero_amplitude connects the scalar mean to the actual n-bit output. run_constant proves the full output is ± the zero basis vector, including its global sign. For balanced functions, nonzero_weight proves total weight 1 outside the zero string. promised_outcome_correct proves the correct class on every outcome of positive weight. Deterministic classification does not imply one fixed output string for all balanced functions. The Born-rule interpretation of squared real amplitudes as physical probabilities is external.

## Edge cases, compatibility and counterexamples

For n=0, hadamard is identity; every function is constant, none is balanced, and the zero weight is 1. oneBitEquiv explicitly identifies Bits 1 with Bool. dj_compat_one_qubit matches BOTH amp0 and amp1 from the unchanged QuantumDeutschJozsa module, and constant_compat/balanced_compat match its predicates. Its original suite and registry field remain intact.

absent_promise_counterexample uses two-bit AND: it is neither constant nor balanced, and its zero-string weight is 1/4. nonlinearBalanced(x)=x₀ XOR (x₁ AND x₂) is balanced on three bits. nonlinear_output gives amplitudes 1/2,1/2,1/2,-1/2 on strings with first coordinate true; balanced_not_single_output exhibits distinct outcomes of weight 1/4. plus_does_not_kickback refutes replacing minus by a plus-shaped ancilla in the same identity (the unnormalized plus vector suffices for the algebraic counterexample).

## Scope and evidence

The model covers all finite n with real amplitudes and an ideal XOR oracle. It does not construct that oracle from elementary gates, certify physical state preparation or measurement, model noise, or prove query-cost semantics, oracle construction complexity, classical lower bounds or exponential speedup. The expression contains one XOR application, but this is not an implementation-cost theorem. Functions outside the promise have a defined normalized circuit and formula; only the zero-error classifier guarantee requires the promise.

This work does not formalize a general complex Hilbert-space tensor library. The existing Python/JSON/SHA-256 and SimLab byte-binding obligations are unchanged. Scientific novelty is not assessed. See the [verification record](../../docs/deutsch-general-verification.en.md) for measured checks and hashes.
