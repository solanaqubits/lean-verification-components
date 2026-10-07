---
id: QuantumSimonsAlgorithm
language: en
section: quantum-physics
source: Verification/QuantumSimonsAlgorithm.lean
source_sha256: f59fb92293df5dadc613ad9b4e64c21ea7793ba107e4025726427edf59c66361
novelty: not-assessed
status: reviewed
---

# QuantumSimonsAlgorithm

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumSimonsAlgorithm.lean)

## Registers, oracle and actual circuit

The input and output registers have arbitrary finite sizes n and m. Register aliases the existing Deutsch–Jozsa Bits type; it does not redefine Lean's BitVec. JointState assigns complex amplitudes to both registers. The old real character, normalization factor and Hadamard proofs are reused. hadamard_real_compat explicitly relates the complex operator to the existing real operator.

xorOracle f acts by permuting amplitudes: ψ(x,z XOR f(x)). Complex linearity, involution, self-adjointness and preservation of the full Hermitian product and squared norm hold for arbitrary complex states and arbitrary f. inputHadamard is also complex linear, involutive and Hermitian-product/norm preserving.

runSimon is the composition H_input → U_f → H_input on the actual zero basis state. first_hadamard and after_oracle derive the intermediate states. simon_circuit_amplitude derives, rather than defines as the output, A(y,z) = (1/2^n) sum_{x:f(x)=z} χ(x,y). Empty fibers give zero. Both registers remain represented; probability sums Complex.normSq over every output label.

## Promise and exact distribution

SimonPromise f s requires s ≠ 0 and f(x)=f(x′) iff x=x′ or x=x′ XOR s. Thus each nonempty fiber has exactly two distinct inputs. The signs cancel when dot(y,s)=1 in ZMod 2. simon_amplitude_zero_when_odd_dot proves zero amplitude for every output label in that case.

simon_exact_probability_distribution proves P(y)=2/(2^n) when dot(y,s)=0 and P(y)=0 otherwise. The denominator is a real power; natural subtraction in an exponent is not used. This is a uniform distribution on the binary orthogonal hyperplane. The algebraic proof expands the squared fiber sums, uses the promise to select the two matching inputs, and sums their character contributions.

simon_distribution_normalized proves sum_y P(y)=1 even without the promise, from the normalized initial state and the actual operators. Probabilities are finite Born weights; no implementation of physical measurement is certified.

## Rank-conditional recovery

encode maps booleans to ZMod 2 and preserves XOR as addition. dot is the ordinary binary bilinear pairing, with a proved bridge to the old real character. rowSpan Y is the linear span of the encoded finite set of rows, not its cardinality.

simon_linear_system_recovery assumes a nonzero s, dot(y,s)=0 for every y in Y, and finrank(rowSpan Y)=n−1. It proves, for every v, that all equations dot(y,v)=0 hold iff v=0 or v=s. The standard binary bilinear form is proved nondegenerate; its orthogonal complement has dimension one and is spanned by s. No positive-definite inner product is assumed in characteristic two.

The result establishes a unique nonzero solution, not an implemented solver or a theorem that samples necessarily reach sufficient rank. Zero or repeated observations do not imply rank growth.

## Edges, regressions and limits

Regressions cover arbitrary complex states; n=1 with m=0; impossibility of a nonzero period at n=0; two-bit parity with s=11 and weights 1/2 at 00 and 11; forbidden outcomes; unreachable output labels; singleton full-rank recovery; an extra solution with insufficient rank; and a constant two-bit function outside the promise giving weight 1 at zero.

The s=0 injective branch, independent repeated sampling, sample-count/failure bounds, Gaussian elimination complexity, oracle synthesis, classical lower bounds, exponential speedup and physical noise are not formalized. Generic operators and normalization remain defined outside the promise. Python, JSON/SHA-256 and binding external SimLab data to bytes remain external obligations. Scientific novelty is not assessed.

## Source and validation

Daniel R. Simon, [On the Power of Quantum Computation](https://epubs.siam.org/doi/10.1137/S0097539796298637), SIAM Journal on Computing 26(5), 1997, pp. 1474–1483; preliminary version FOCS 1994. The present scope formalizes exact sampling and rank-conditional algebra, not the paper's expected-time theorem.

[Verification record](../../docs/simon-verification.en.md) · [Reservoir readiness](../../docs/reservoir-readiness.en.md)
