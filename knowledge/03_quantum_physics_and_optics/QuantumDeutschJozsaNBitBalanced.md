---
id: QuantumDeutschJozsaNBitBalanced
language: en
section: quantum-physics
source: Verification/QuantumDeutschJozsaNBitBalanced.lean
source_sha256: a2c0a646bd46c4c61c76fcb0cded4b0a37232fc02981b8c4733b9510abb2f7e5
novelty: not-assessed
status: reviewed
---

# Exact classification of balanced Deutsch–Jozsa oracles

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumDeutschJozsaNBitBalanced.lean)

## Definitions and proof boundary

The module imports QuantumDeutschJozsaGeneral and reuses its Bits n = Fin n → Bool,
IsBalanced, zeroStateAmplitude, zeroStateProb, runDJ and outcomeWeight. BalancedFamily
is the subtype of all Boolean oracles satisfying that existing predicate. It is
not a newly weakened promise. Old circuit definitions and proofs are unchanged.

The support is the finite set of inputs mapped to true. Its inverse is the Boolean
characteristic function of a finite set. Both inverse laws are proved, yielding
an equivalence of all oracles and all supports. For n≥1 the restriction gives an
equivalence of BalancedFamily n and supports of cardinality 2^(n-1).
Finset.card_powersetCard then yields the exact count choose(2^n,2^(n-1)).

At n=0 the input domain is a singleton: no oracle is balanced and the count is zero.
Natural subtraction saturates, so the unguarded expression choose(2^0,2^(0-1))
equals one and is false as a balanced-family count. The total formula branches on n=0.
Counts 0,2,6,70 follow for n=0,1,2,3. Positive-qubit counts reduce the proved formula
and use kernel reduction of the finite binomial arithmetic, not native_decide.

## Operational connection

For every n and every oracle, without DJPromise, the following are equivalent:
IsBalanced f; zeroStateAmplitude f=0; zeroStateProb f=0;
runDJ f (zeroBits n)=0; outcomeWeight f (zeroBits n)=0.
The converse amplitude theorem uses the exact signed sum card−2*trueCount and the
nonzero size of Bits n. Thus the counted family is exactly the circuit's zero-output-
probability family, not merely a family with an assumed amplitude formula.

With DJPromise, a paired theorem proves (P0=0 iff balanced) and (P0=1 iff constant).
This is not a claim that a single nonzero measurement classifies arbitrary
unpromised oracles. The projection onto the first bit witnesses balance for every
n≥1. Constant oracles are excluded. Relabeling Bits n by Fin (2^n) preserves the
truth count and balanced predicate; the basis equivalence is explicitly provided.

## Main declarations

- supportEquiv, ofSupport_toSupport, toSupport_ofSupport: inverse characteristic maps.
- balanced_iff_card_support, balanced_family_equiv_powerset: positive-qubit classification.
- balanced_card_formula_pos, balanced_card_zero_qubits, balanced_card_formula: exact counts.
- balanced_iff_zero_amplitude, balanced_iff_zero_prob: promise-free equivalences.
- balanced_iff_run_zero, balanced_iff_outcome_zero: bridge to the existing circuit.
- dj_promise_separation_exact: explicitly parenthesized promise separation.
- constructive_witness_n_pos, constants_excluded: nonvacuity and excluded oracles.
- bitsFinEquiv, fin_oracle_trueCount, fin_oracle_balanced: finite-register interface.
- quantum_deutsch_jozsa_nbit_balanced_master_suite: packaged contract.

## Regressions and Clean Water

Regressions cover all four counts, rejection of the unguarded n=0 formula,
support round trips, Fin-register relabeling, arbitrary-oracle interference
without a promise, projection witnesses, constants, and a nonlinear balanced oracle.

The finite cardinality presentation is noncomputable/classical where needed;
no efficient oracle enumeration, sampling or circuit synthesis is claimed.
The asymptotic density of balanced functions, hardware gates, noise and physical
measurement implementation are outside this module. Python, JSON/SHA-256 and
SimLab linkage remain open obligations. Scientific novelty is not assessed.

[Mathlib combination count](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Powerset.html#Finset.card_powersetCard).
[Commands and hashes](../../tools/validation_snapshot.json).

## Historical source-side validation

Base snapshot: `d06eee279392f800cbb8a5ff8dff3af30b051edc`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 125 |
| Lean files under Verification/ | 165 top-level + 2 support = 167 |
| Root-inclusive byte-identical export | 168 sources |
| Clean strict private build | 3616 jobs; no warnings |
| Both full axiom audits | 14330 declarations; no violations |
| Private live tests | 73; no failures or skips; 257.019s |
| Export live tests | 70; no failures or skips; 275.826s |
| Export clean strict build | 3616 jobs; no warnings |

Module verify and audit each covered 258 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor source is pinned to 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not asserted.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. Integration is idempotent.
Prior subject proof sources, original HEAD and 406 tracked files outside simulations/
are preserved. This task makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.23 report](../../docs/release-v0.5.23.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 125 |
| Lean files under Verification/ | 165 top-level + 2 auxiliary = 167 |
| Root-inclusive sources identical to the private snapshot | 168 |
| Clean strict build | 3616 jobs; no warnings |
| Complete verifier audit | 14330 declarations; no violations |
| Pinned independent full audit | 14330 declarations; no violations |
| Public live tests | 70; no failures or skips; 262.919s |
