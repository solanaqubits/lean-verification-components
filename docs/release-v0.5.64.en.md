# Release v0.5.64: Classical POVM data processing

This release adds QuantumChannelClassicalDataProcessing as the 166th direct
MasterSuite import. It constructs stochastic postprocessing of finite POVMs,
proves preservation of absolute continuity and classical KL contraction for
measurement outcome distributions, and proves Shannon entropy growth under
bistochastic postprocessing.

The channel matrix is column-stochastic. The effects are
E'_k = sum_j M(k,j) E_j; positivity, completeness and the probability-map identity
are proved together with identity, relabeling and composition laws. The analytic
log-sum inequality yields KL nonnegativity and data processing for normalized
nonnegative distributions p,q satisfying p(j)>0 implies q(j)>0.

Entropy growth requires a square bistochastic channel. A binary symmetric channel
strictly increases entropy for a nonuniform binary distribution when 0<epsilon<1/2.
Deterministic merging of a fair bit into one outcome decreases entropy from one
bit to zero, demonstrating why arbitrary stochastic postprocessing is insufficient.
Identity/permutation invariance, erasure, zero probabilities and zero effects
are covered by kernel regressions.

[Detailed contract](../knowledge/03_quantum_information/QuantumChannelClassicalDataProcessing.md)

## Scope and open obligations

The total real KL formula is interpreted as finite relative entropy only under
absolute continuity. The singular case requiring positive infinity is not modeled;
checked_kl refuses unsupported inputs as a noncomputable mathematical guard.
The Lean definitions use exact, noncomputable real analysis. No executable
floating-point logarithm implementation or numerical logarithm certificate is claimed.

This is classical DPI for distributions of quantum measurement outcomes. General
Umegaki quantum relative-entropy DPI under CPTP maps, quantum memory and finite-sample
statistical estimation are outside scope. Tendermint Amnesia attribution still
requires a complete observation or justification-evidence contract: absence of a
Polka in a partial observer log does not prove that a validator never received it.
Bulletproofs knowledge extraction, computational binding, HVZK, Fiat-Shamir/ROM,
and external Python, JSON/SHA-256 and SimLab correspondence remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 166 |
| Lean files under Verification/ | 206 top-level + 2 auxiliary = 208 |
| Root-inclusive sources identical to the reference snapshot | 209 |
| Clean strict build | 3846 jobs; no warnings |
| Complete verifier audit | 23587 declarations; no violations |
| Pinned independent full audit | 23587 declarations; no violations |
| Public live tests | 111; no failures or skips; 332.792s |
| New kernel regression declarations | 47 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 209 proof sources match reference snapshot
7eba45c43eebcbe04f7216ae03b94a27cd8d3c0c byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

