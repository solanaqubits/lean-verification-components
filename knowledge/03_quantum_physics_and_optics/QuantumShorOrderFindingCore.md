---
id: QuantumShorOrderFindingCore
language: en
section: quantum-physics
source: Verification/QuantumShorOrderFindingCore.lean
source_sha256: 7ecebffd008cd888625cc38cff3acdeeb2c7899d8d3e7ba0cc313729597b7ede
novelty: not-assessed
status: reviewed
---

# Spectral core of quantum order finding

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumShorOrderFindingCore.lean)

## Parameters and actual operator

Parameters supplies a modulus N≥2, a natural base a with Nat.Coprime a N,
and a target width m with N≤2^m. The control width n is independent of m.
The base need not already be reduced modulo N. period is orderOf (a : ZMod N),
not an externally supplied candidate or a computed classical solution.
period_pos and shor_period_modulo prove r>0 and a^r mod N=1;
shor_powers_distinct_modulo proves injectivity of k↦a^k mod N for k<r.

residuePerm multiplies every residue y<N by a modulo N, including zero and
nonunits. Its inverse uses the inverse of the unit supplied by coprimality.
registerPerm extends this permutation to Fin (2^m), fixing every y≥N.
modularOperator pushes amplitudes forward along that permutation: at coordinate
y it reads the input at registerPerm.symm y. modularOperator_basis proves the
claimed basis action. modularOperator_inverse proves both inverse compositions,
and modularOperator_unitary proves Hermitian-product preservation.

The operator and computational input depend on a,N,m, not on knowledge of r.
The mathematical spectral analysis uses r; this is not an efficient algorithm
for classically computing the order.

## Constructed spectrum and accessible input

orbit embeds k : Fin r as a^k mod N in the padded register. orbitLift is a
complex-linear isometry. wave r s is the inverse QFT of basis state s on Fin r.
eigenstate s is its actual embedding into the target, with coefficients

ψ_s = (1/√r) ∑_{k<r} exp(-2πi sk/r) |a^k mod N⟩.

shor_eigenstate_formula identifies these coefficients; the negative sign and
cyclic wraparound are proved consistent with forward modular multiplication.
shor_eigenstates_orthonormal gives ⟨ψ_s,ψ_t⟩=δ_st.
shor_eigenstate_action gives U_a ψ_s=exp(2πi s/r) ψ_s.
These vectors describe the orbit subspace, not an asserted basis of the entire
2^m-dimensional target. Order one is allowed.

eigenInput constructs a genuine instance of the existing UnitaryEigenInput API,
with unitarity, normalization and the eigenvector equation proved in this module.
The real circuit input is instead input=|1⟩. It does not require preparation of
an unknown eigenstate. shor_input_state_decomposition proves the exact identity

|1⟩ = (1/√r) ∑_{s<r} ψ_s.

This is a coherent pure-state decomposition. It is not an assumption that the
target was initially sampled from a classical mixture.

## Operational output and marginal distribution

qpeLinear proves linearity in the target input of the actual runQPE circuit
imported from QuantumPhaseEstimationGeneral. shor_qpe_output derives

runQPE(U_a,n,|1⟩)(y) = (1/√r) ∑_{s<r} A_{s/r}(y) ψ_s.

The target vectors are orthonormal. eigenstate_synthesis_norm removes cross
terms when computing the marginal squared norm. shor_qpe_probability_mixture
therefore proves, rather than defines,

P(y) = (1/r) ∑_{s<r} P_{s/r}(y).

shor_distribution_normalized proves its sum over Fin (2^n) is one. At n=0 the
single control outcome has probability one, as checked by a generic regression.

shor_component_exact transports exact QPE when s/r=x/(2^n), x : Fin (2^n):
the component probability is 1 at x and 0 elsewhere. For any modular nearest
sample b, shor_phase_accuracy_bound gives P_{s/r}(b)≥4/π².
shor_component_nearest_success also states this for the actual eigen-input
circuit and the constructive nearestSample selector.

This component bound must not be assigned to each peak of the overall mixture.
shor_mixture_peak_lower_bound proves the correctly weighted guarantee
P(b)≥(1/r)(4/π²). Coincident component contributions can add; peaks are not
assumed disjoint. Finite control resolution and arbitrary positive orders are
allowed. No asymptotic convergence theorem is asserted.

## Regressions and epistemic boundary

Concrete witnesses cover N=15,a=2,r=4 and N=7,a=2,r=3. Tests check nonunit and
zero residue action, padding at y=15, both inverse/unitary contracts, order one,
generic orthonormality and decomposition, normalized output and n=0. At r=4
and n=2 the actual |1⟩ output is exactly uniform with weight 1/4, while an r=3
component gives a non-dyadic example with its 1/r-weighted marginal bound.
A reduced-phase example has 2/4=1/2 although the order is 4, not 2.
Non-coprime inputs are excluded explicitly.

Estimating s/r does not automatically recover r. Continued-fraction recovery,
validation of candidate orders, repeated independent measurements, LCM recovery,
reduction to integer factorization, complexity bounds and reversible gate
synthesis remain separate obligations. No complete Shor implementation,
hardware noise model or physical preparation theorem is proved. The accessible
|1⟩ input removes the mathematical unknown-eigenstate assumption; it does not
certify a laboratory preparation procedure. Python, JSON/SHA-256 and external
SimLab input-to-byte binding remain outside the formal result.

Primary references: [Shor, factoring and discrete logarithms](https://arxiv.org/abs/quant-ph/9508027)
and [Cleve, Ekert, Macchiavello and Mosca, Quantum Algorithms Revisited, §6](https://arxiv.org/pdf/quant-ph/9708016).
No novelty or first-formalization claim is made.

## Historical private implementation and export verification

Base private commit: `9970e9170023db76f1a392a7235bb5a1af6778e2`.

| Check | Result |
|---|---:|
| MasterSuite direct imports | 117 |
| Lean files under Verification/ | 157 top-level + 2 support = 159 |
| Root-inclusive byte-identical proof export | 160 |
| Clean strict project build | 3542 jobs; no warnings |
| Both complete axiom audits | 12359 declarations; no violations |
| Private live tests | 65; no failures or skips; 250.936s |
| Export live tests | 62; no failures or skips; 252.189s |
| Export clean strict build | 3542 jobs; no warnings |

Separate module verify and audit each checked 471 transitive declarations.
The complete local and independent audits allow only propext, Classical.choice
and Quot.sound. The independent axiom-audit tool is pinned at commit
`46024e005996495c65ef609368e11ab39c4222e3`. The registry hook is additional,
not a second proof kernel. Declaration counts include generated definitions.
Clean builds began with empty project build directories and isolated copies of
pinned dependency caches; Mathlib was not rebuilt entirely from source.

```bash
python3 tools/verifier_skill.py verify Verification/QuantumShorOrderFindingCore.lean
python3 tools/verifier_skill.py audit Verification/QuantumShorOrderFindingCore.lean
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent tool is run through lake env with --root Verification,
--allow propext,Classical.choice,Quot.sound and --json. The English export
passed its own build, full live tests, registry and independent audit.
Integration returns an empty repeat diff. Previous subject proofs are unchanged.
The original workspace HEAD and 406 tracked-file hashes outside simulations/
are preserved. That implementation task wrote nothing to simulations/ and made no public release.
Fresh public release measurements are recorded in the [v0.5.15 release report](../../docs/release-v0.5.15.en.md).
[Validation snapshot](../../tools/validation_snapshot.json) records hashes and scope.
