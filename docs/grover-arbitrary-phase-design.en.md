# Arbitrary phase Grover: design contract

Baseline: ac3e2363e6711b981f31e1cc782ec1b51cf69b35. Existing real four-coordinate
modules cover standard sign reflections, all target subsets and their iterates.
This module adds complex phase operators for one marked coordinate in dimension four.
It does not change those modules.

For z=exp(iφ), w=exp(iψ), define R(v) at the marked coordinate as z*v and
D(v)=v+(w-1)*(sum v)/4 at every coordinate. Prove complex linearity, preservation
of the Hermitian product and inverse/adjoint identities. These establish unitarity
on arbitrary states, without assuming the input is normalized.

The complex span of the marked vector and the uniform unmarked vector is invariant
for every pair φ,ψ. Equality of phases is sufficient but not necessary. A mismatch
must not be called leakage out of that complex plane. Prove its two-coordinate
recurrence and specialize it to equal phases.

From the uniform state with entries 1/2, equal phases give marked amplitude
(z²+6z-3)/8 and unmarked amplitude (z+1)²/8. Prove the exact success probability
P(φ)=1-3*(1+cos φ)²/16, hence P=1 iff cos φ=-1. In particular π succeeds.
For this single-target N=4 case that is the already exact canonical phase, not a
new fractional correction of overshoot.

At π, the oracle agrees with the old oracle; Dπ is the negative of the old
diffusion, so the raw composite is the negative of the canonical step. Prove this
on arbitrary embedded real states and the resulting equality of measurement
weights. Do not assert literal equality with the old diffusion.

Primary references: Høyer, On Arbitrary Phases in Quantum Amplitude Amplification
(2000), https://arxiv.org/abs/quant-ph/0006031; Long, Grover Algorithm with zero
theoretical failure rate (2001), https://arxiv.org/abs/quant-ph/0106071.
Høyer already works in an invariant two-dimensional complex space for arbitrary
phases; his phase-matching relation is convention dependent and is not a criterion
for invariance. Neither his general matching theorem nor Long's general iteration
schedule is claimed here. Limits: fixed dimension and one target, exact algebra,
no gate synthesis, noise, hardware or complexity theorem. Python, parsing,
SHA-256 and external byte binding remain outside the Lean result.
