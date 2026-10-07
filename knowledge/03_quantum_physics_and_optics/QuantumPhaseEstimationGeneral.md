---
id: QuantumPhaseEstimationGeneral
language: en
section: quantum-physics
source: Verification/QuantumPhaseEstimationGeneral.lean
source_sha256: ca48423f64948d3b170a7fabf46b6d139a587032ea3b82543c73d019a7596a71
novelty: not-assessed
status: reviewed
---

# General finite-register quantum phase estimation

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumPhaseEstimationGeneral.lean)

## Contract and operational definitions

The control register has N=2^n computational basis states indexed by Fin N.
The target is Fin d → ℂ for an arbitrary finite dimension d. TargetOperator is a
complex-linear endomorphism; IsUnitary requires preservation of the Hermitian
product for all target vectors. UnitaryEigenInput supplies such an operator U,
a target ψ with squared norm one, and U ψ = phase(θ) • ψ for θ : ℝ.
These are input assumptions, not an eigenstate preparation procedure.

phase(t)=exp(i·2πt). The positive Fourier kernel uses phase(jk/N); the inverse
uses its complex conjugate. Both are normalized by 1/√N. Index k uses ordinary
binary integer order, with the least significant control bit driving U.

hadamardKernel gives the normalized binary-dot-product sign matrix on n bits.
hadamard_prepares_uniform proves that it sends the zero basis state to the
constant 1/√N vector. prepare_control_from_hadamard identifies the actual initial
control/target product used by the circuit. No arbitrary-input Hadamard gate
synthesis or complexity theorem is claimed.

controlledCascade is a recursive composition of conditional linear operators.
At each stage it applies the lower-bit cascade, then U^(2^k) precisely on the high
control branch. controlled_cascade_eq_power proves that basis branch j applies
U^j; it does not define the cascade to be an eigenphase. eigen_power and
controlled_powers_kickback derive the pre-Fourier product state from the supplied
eigenvector equation. inverseControl then transforms the control coordinates of
the actual joint state. qpe_amplitude_derivation proves:

runQPE U n ψ y = Aθ(y) • ψ,

Aθ(y) = (1/N) ∑_{k=0}^{N-1} exp(2πi k(θ−y/N)).

qpe_amplitude_exponential exposes this conventional formula directly.
The amplitude identity needs linearity and the eigenvector equation. The
probabilistic interpretation additionally needs normalized ψ. IsUnitary gives
norm preservation for arbitrary joint inputs to the controlled cascade;
qpe_circuit_norm proves norm preservation for the full prepared circuit without
requiring an eigenstate equation.

## Fourier, exact and approximate results

For every N>0, including non-powers of two, inverse_qft_qft and qft_inverse_qft
prove both inverse identities. qft_unitarity and inverse_qft_unitarity preserve
the Hermitian product, hence squared norm. The QPE circuit specializes N to 2^n.

qpe_exact_dyadic_phase gives A(x)=1 and A(y)=0 for y≠x when θ=x/N, x : Fin N.
qpe_exact_probability converts these amplitudes to squared-modulus probabilities.
qpe_probability_normalized proves ∑y Pθ(y)=1 for every real θ from Fourier norm
preservation, not from a postulated distribution.

When δ=θ−y/N is not an integer, qpe_geometric_sum_closed_form proves:

|Aθ(y)| = |sin(πNδ)| / (N |sin(πδ)|).

The excluded singular branch is separately proved by amplitude_of_integral:
phase(δ)=1 implies Aθ(y)=1. Thus division by zero is not used to infer success.
amplitude_periodic proves invariance under every integer shift of θ.

Nearest N θ b means there exists z : ℤ with |θ−b/N−z|≤1/(2N).
nearestSample rounds Nθ to an integer and reduces it modulo N; nearest_sample_valid
proves it satisfies this contract for every θ. The lower-bound theorem applies
to either choice at a midpoint, including ties across the 0/1 boundary.

qpe_arbitrary_phase_lower_bound proves Pθ(b)≥4/π² for every such nearest b.
Its proof uses the geometric sum, Jordan's sine inequality and |sin x|≤|x|,
with the integral-phase case handled separately. qpe_nearest_sample_success
transports this estimate to the marginal squared norm of the actual joint output
for UnitaryEigenInput. Rational non-dyadic, irrational, negative and integer-shifted
phases are all covered. No independence or repeated-measurement assumption is needed.

## Compatibility and edge cases

qpe_bridge_to_two_qubit proves equality of the complete operational output with
QuantumPhaseEstimation.runQPE at n=2 and d=2 for arbitrary U and ψ. Separate
bridges identify the controlled cascade and inverse Fourier operator.
qpe_probability_bridge_two recovers the old exact DyadicPhase2 probabilities.
This is a literal state equality with the same basis order, not only a comparison
of selected outcome weights or an equality up to global phase.

qpe_case_zero_qubits proves the n=0 circuit returns ψ unchanged;
qpe_zero_qubit_probability proves that its only control result has probability one.
The main suite includes operational preparation and amplitudes, both Fourier
inverses, unitarity, norm preservation, exactness, normalization, the geometric
and singular branches, nearest-sample existence, the analytic and measured lower
bounds, compatibility and the zero-control case.

## Regressions and limits

Kernel-checked regressions cover N=8 exact success and off-target cancellation,
θ=1/3, negative θ, integer shifts, the singular branch, n=0, arbitrary n,
controlled-power identities and both nearest choices at θ=31/32 for N=16.
Explicit one-dimensional unitary eigen-inputs exist for every real θ, so the
non-dyadic marginal-probability test has an actual normalized witness.

No physical preparation of ψ, gate decomposition of controlled powers or the
Fourier transform, oracle-cost bound, finite-precision arithmetic, gate noise,
decoherence, fault tolerance or full Shor algorithm is proved. Real phases and
complex amplitudes are exact mathematical objects. Python, JSON/SHA-256 and
external SimLab input-to-byte binding remain separate obligations.

Primary reference: Cleve, Ekert, Macchiavello and Mosca, *Quantum Algorithms
Revisited*, §5, [arXiv:quant-ph/9708016](https://arxiv.org/pdf/quant-ph/9708016).
The bound follows the geometric-sum argument with explicit modular distance and
singular cases. No novelty or literal formalization of a textbook is claimed.

## Historical private implementation and export verification

Base private commit: `09507001387c0e684c981e8d1ffdf67a77f68f41`.

| Check | Result |
|---|---:|
| MasterSuite direct imports | 116 |
| Lean files under Verification/ | 156 top-level + 2 support = 158 |
| Root-inclusive byte-identical proof export | 159 |
| Fresh strict build | 3541 jobs, no warnings |
| Both complete axiom audits | 12210 declarations, no violations |
| Private live tests | 64, no failures or skips (237.486s) |
| Export live tests | 61, no failures or skips (252.818s) |
| Export strict build | 3541 jobs |

Separate module verify and audit each checked 323 transitive declarations.
Both complete audits permit only propext, Classical.choice and Quot.sound.
The independent axiom auditor is pinned at
`46024e005996495c65ef609368e11ab39c4222e3`.
The clean project build used isolated copies of pinned dependency caches; Mathlib
was not rebuilt entirely from source. Counts include generated declarations.

```bash
python3 tools/verifier_skill.py verify Verification/QuantumPhaseEstimationGeneral.lean
python3 tools/verifier_skill.py audit Verification/QuantumPhaseEstimationGeneral.lean
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent auditor was run through `lake env`, with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`. The strict registry
hook is additional to the two project-wide audits, not a separate proof kernel.
The export passed its own clean build, live tests, registry and independent audit.
[Validation snapshot](../../tools/validation_snapshot.json) records source hashes
and the exact scope. Existing subject proofs and Simon contract pins are unchanged.
Integration is idempotent. Original workspace HEAD and 406 tracked-file hashes
outside simulations/ are preserved; this task wrote nothing to simulations/.
That implementation stage made no public release. Fresh public measurements are recorded in the [v0.5.14 release report](../../docs/release-v0.5.14.en.md).
