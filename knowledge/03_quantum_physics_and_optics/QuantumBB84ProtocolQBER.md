---
id: QuantumBB84ProtocolQBER
language: en
section: quantum-physics
source: Verification/QuantumBB84ProtocolQBER.lean
source_sha256: e3c0bb64604fdf7a11ab8a00b5c2dd6431768600220b0d7ffb8e9467cb905210
novelty: not-assessed
status: reviewed
---

# BB84: Born-derived QBER and independent detection samples

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumBB84ProtocolQBER.lean)

## Construction and proved results

BB84Basis and BB84Bit are Fin 2 with named Z/X and zero/one values. The four
states are complex 2-by-1 matrices; their normalization is proved. Projectors
are defined as ket times its conjugate transpose, and the rational entry table
is derived. Positivity, Hermiticity, orthogonality and completeness are proved.
Born measurement is an explicit physical modeling postulate, represented by the
real part of Tr(P rho); its nonnegativity and normalization are proved for density
operators. On BB84 preparations the complex trace equals the corresponding real
probability, with deterministic same-basis outcomes and probability 1/2 for MUBs.

The intercept-resend channel is one half of the sum of four P rho P terms.
There are two independently selectable measurement bases, each of which has a
complete pair of outcomes. The quarter-prefactor in the requested CLI contract
was inconsistent with trace preservation: a formal regression proves that it
halves the trace on |0>. The corrected channel preserves trace and positivity.
Each rank-one branch equals Tr(P rho) times P, establishing measurement and
re-preparation rather than an unrelated matrix formula.

The 64-point round space records Alice's bit, Alice/Bob/Eve bases, Eve's result
and Bob's result. Its weight is 1/16 times two derived Born transition
probabilities. The marginal of the first four choices is exactly uniform 1/16.
The marginal over Eve's basis and result equals the optical channel's Born law.
Honest rounds retain an unused Eve-basis coordinate and a dummy zero Eve result.
Partial interception is the independent mixture (1-f) honest + f attack, for
0 <= f <= 1, and is linked to the corresponding mixture of matrix channels.

FiniteLaw includes nonnegative weights and a proved total mass of one. Its PMF
conversion preserves event probabilities, so probabilities are genuine finite
probability laws. Sifting has mass 1/2, joint error and sifting has mass 1/8,
and the conditional QBER is exactly 1/4. Honest sifted error is zero; the partial
interception QBER is f/4. These are conditional theoretical probabilities,
not deterministic lower bounds on the observed error fraction of every sample.

The sifted law is proved to be the full round law conditioned on equal bases.
The m-round law is a product of these laws; an event-factorization theorem derives
independence. No-error probability is (3/4)^m, detection probability is
1-(3/4)^m, and evasion remains strictly positive for every finite m, including
m=0. This does not model sampling without replacement from a fixed bit string.

## Bridge, regressions and scope

The derived QBER equals QuantumBB84Protocol.eveErrorProbabilityPerBit. The old
module is unchanged. Regressions cover f=0, f=1, m=0, m=2 (7/16), PMF normalization,
finite-sample noncertainty, and the incorrect channel prefactor.

The model is an ideal independent individual intercept-resend attack in Z/X,
with single-qubit states, ideal preparation and projective measurement, no losses
or detector bias, independent random choices, and an authenticated classical
basis-comparison channel. Born's rule is assumed, not derived from lower-level
physics. Key secrecy, collective/coherent attacks, active attacks on basis
negotiation, reconciliation, privacy amplification, finite-key security,
weak coherent sources/PNS, noise and dark counts are not modeled.
Python, JSON/SHA-256 and SimLab correctness obligations remain open.
Scientific novelty is not assessed.

Reference: [Bennett and Brassard (1984)](https://arxiv.org/abs/2003.06557).

## Validation

Base snapshot: bc6ec6054e308654f2f2b010c66474b12719cc43.
All project and export checks passed; measured results follow.

## Source theorem links

- [projector_exact](../../Verification/QuantumBB84ProtocolQBER.lean#L49)
- [measurement_channel_bridge](../../Verification/QuantumBB84ProtocolQBER.lean#L118)
- [intercept_resend_error_exact](../../Verification/QuantumBB84ProtocolQBER.lean#L258)
- [partial_intercept_qber](../../Verification/QuantumBB84ProtocolQBER.lean#L284)
- [sample_detection_probability](../../Verification/QuantumBB84ProtocolQBER.lean#L329)
- [evasion_probability_positive](../../Verification/QuantumBB84ProtocolQBER.lean#L335)
- [counterexample_quarter_channel](../../Verification/QuantumBB84ProtocolQBER.lean#L362)
- [born_trace_exact](../../Verification/QuantumBB84ProtocolQBER.lean#L374)
- [measure_prepare_exact](../../Verification/QuantumBB84ProtocolQBER.lean#L384)
- [born_nonneg](../../Verification/QuantumBB84ProtocolQBER.lean#L391)
- [partial_round_channel_bridge](../../Verification/QuantumBB84ProtocolQBER.lean#L447)
- [quantum_bb84_protocol_qber_master_suite](../../Verification/QuantumBB84ProtocolQBER.lean#L483)

## Private snapshot validation: Born-derived BB84 QBER

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 136 |
| Lean sources | 178 under Verification/; 179 including root |
| Strict clean private build | 3726 jobs; no warnings |
| Both full axiom audits | 17081 declarations; no violations |
| Private live tests | 84; no failures or skips; 279.655s |
| Export live tests | 81; no failures or skips; 277.465s |
| Strict clean export build | 3726 jobs; no warnings |

Module verify and audit each covered 226 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 179 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

The channel prefactor is 1/2; the erroneous draft prefactor 1/4 halves the trace.
Born measurement is an explicit physical postulate. The conditional QBER 1/4 is
computed from the quantum experiment. Independent finite samples have strictly
positive evasion probability; no deterministic sample error bound is asserted.

## Public release validation

The [v0.5.34 report](../../docs/release-v0.5.34.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 136 |
| Lean files under Verification/ | 176 top-level + 2 auxiliary = 178 |
| Root-inclusive sources identical to the private snapshot | 179 |
| Clean strict build | 3726 jobs; no warnings |
| Complete verifier audit | 17081 declarations; no violations |
| Pinned independent full audit | 17081 declarations; no violations |
| Public live tests | 81; no failures or skips; 277.682s |
