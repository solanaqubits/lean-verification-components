---
id: QuantumShorContinuedFractions
language: en
section: quantum-physics
source: Verification/QuantumShorContinuedFractions.lean
source_sha256: 281c191f1d94e0a16f0de9cf477b92cb3fc738e40e882cd5e0fc6f9b075d70d0
novelty: not-assessed
status: reviewed
---

# Continued fractions for Shor postprocessing

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumShorContinuedFractions.lean)

## Executable algorithm

convergents and partialQuotients accept a rational number and use floor followed by
reciprocal fractional part. Rat floor is integer Euclidean division. Recursion stops
at an integer and terminates by strictly decreasing canonical denominator. These are
computable definitions, not noncomputable witnesses from Legendre. candidates(y,Q,N)
filters convergents of the exact rational y/Q by denominator < N. Its inputs contain
no unknown spectral numerator s or order r. checkedCandidates additionally takes a
and filters denominators through a^q mod N = 1 mod N.

mem_convergents_iff proves both directions between membership in the finite list and
Mathlib Real.convergent. Mathlib's repeated terminal convergents are covered. The
strict Legendre theorem Real.exists_rat_eq_convergent is reused from pinned Mathlib;
its foundational number theory is not claimed as new work.

The list length is at most the input denominator. More strongly, the number of
Euclidean stages (partial-quotient list length) is at most 2*Nat.log 2 denominator+1,
hence at most 2*Nat.log 2 Q+1 for y/Q with Q>0. The proof uses a strict denominator
reduction at each step and a factor-of-two reduction over two steps. This counts
Euclidean stages, not all list-map work, bit operations, modular exponentiation
cost, or a bound on total program runtime. No O(log N) claim without relating Q to N.

## Approximation and recovery

The existing Shor Parameters supply N≥2, a coprime to N and the padded target
register. The actual period is r=orderOf(a : ZMod N), with r>0 and r<N proved.
The control width n is independent; require Q=2^n≥N². For 0≤s<r and 0≤y<Q,
Nearest Q (s/r) y is the existing modular rounding relation from QPE.
nearest_has_no_wrap proves that this relation gives ordinary distance
|y/Q-s/r|≤1/(2Q), including s=0 and either allowed rounding tie. A coarse measurement
can wrap across 0/1, but such examples do not satisfy this resolution contract.

reduced s r is the canonical rational s/r. Its numerator is s/gcd(s,r), denominator
q=r/gcd(s,r)>0, and the two are coprime. Since q≤r<N and N²≤Q, the approximation
bound is strictly below 1/(2q²). Equality y/Q=s/r is included. The strict sign is
essential: at x=1/2, the rational 1 has error exactly 1/2 but is absent from the
chosen canonical convergents [0,1/2].

convergent_recovery_soundness proves membership of the correct reduced fraction in
the candidate list. shor_nearest_candidate connects this to the actual period and
QPE Nearest contract and proves q divides r. When gcd(s,r)=1, the denominator is r,
and shor_coprime_checked_candidate proves r belongs to the executable checked list.

Other entries of the same list are not asserted to divide r. The algorithm does not
know which spectral component generated a measurement. Passing the modular check
proves r divides q, not minimality: proper multiples may pass. If one separately has
q divides r, checked_divisor_is_order proves equality by mutual divisibility.
For s=0 the reduced denominator is 1; this recovers the order only when r=1.

shor_recovery_peak combines candidate membership with the existing actual-input
QPE marginal bound 4/(r*pi²) at that component's nearest sample. The component bound
4/pi² is not substituted for the mixture bound. No guaranteed success of one sample,
unconditional probability of order recovery, or independence of repeated samples
is asserted.

## Regressions and limits

Kernel-checked computations cover exact and approximate fractions, negative rational
Euclidean input, zero and integer inputs, order one, reduced divisors, strict filtering,
extraneous candidate denominators, passing nonminimal multiples, failed modular checks,
and the N=7,a=2, Q=256 Shor bridge. They use decide +kernel, not native_decide. Generic
regressions preserve the full approximation, size, coprimality and QPE assumptions.

Repeated quantum runs, LCM recovery, classical factorization, long-integer bit
complexity, physical noise and gate synthesis are outside scope. Python, JSON/SHA-256
and external SimLab input-to-byte binding remain open. No scientific-priority claim.
The source hash identifies the proof snapshot; measured build/audit/test outcomes
are recorded in [validation_snapshot.json](../../tools/validation_snapshot.json).

Sources: pinned Mathlib NumberTheory/DiophantineApproximation/Basic.lean
(Real.exists_rat_eq_convergent), and the existing
[order-finding core](QuantumShorOrderFindingCore.md). Context:
[P. Shor, polynomial-time factoring and discrete logarithms](https://arxiv.org/abs/quant-ph/9508027).

## Historical private implementation and export validation

Base snapshot: `ef9c48132533ccbf950462326a7282c335bf0777`.

| Check | Measured result |
|---|---:|
| Direct subject imports | 119 |
| Lean files under Verification/ | 159 top-level + 2 support = 161 |
| Root-inclusive byte-identical export | 162 sources |
| Clean strict private build | 3546 jobs; no warnings |
| Both full axiom audits | 12863 declarations; no violations |
| Private live tests | 67; no failures or skips; 249.602s |
| Export live tests | 64; no failures or skips; 262.612s |
| Export clean strict build | 3546 jobs; no warnings |

Module verify and audit each checked 539 declarations, including transitive project
imports. Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor is pinned at 46024e005996495c65ef609368e11ab39c4222e3.
The strict AxiomAudit registry hook passed separately; it is not a second proof kernel.
Counts include generated declarations. Project build directories started empty;
isolated pinned dependency caches were reused. Integration is idempotent. No earlier
subject proof was modified. Original HEAD and 406 tracked files were preserved.
That implementation task wrote nothing to simulations/ and made no public release. Fresh public measurements appear in the [v0.5.17 report](../../docs/release-v0.5.17.en.md).
