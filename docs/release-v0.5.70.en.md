# Release v0.5.70: Trace distance and measurement contraction

This release adds QuantumChannelTraceDistanceContract as the 172nd direct
MasterSuite import. All 215 Lean sources match reference snapshot
6cb4f3eaf0b95aff626de9e827338c0fa1986292 byte-for-byte.

## Formal result

Trace distance is defined as half of module 171's trace_norm(rho-sigma), where
trace_norm is Re Tr(sqrt(A†A)). For density matrices the module proves nonnegativity,
symmetry, separation, the triangle inequality, and bounds 0 <= D <= 1. It assumes
no commutation of states or effects and introduces no norm axiom.

The spectral effect on the positive eigenspace of rho-sigma attains the maximum
absolute effect expectation. The result is an IsGreatest statement with an explicit
optimizer; idempotence, positivity and positivity of the complement are proved.
Equal-prior optimal Helstrom success is (1+D)/2.

Total variation TV(p,q)=(1/2)*sum_j |p_j-q_j| contracts under classical stochastic
channels. For a finite POVM, TV(P_E(rho),P_E(sigma)) <= D(rho,sigma). The binary
spectral POVM attains equality and the maximum over every finite outcome count.
Permutation, erasure and composition properties use the actual postprocess_povm
interface from module 166.

The 36 new kernel regressions include identical states, orthogonal states with
D=1, and noncommuting |0> and |+> states with D=1/sqrt(2). Z-basis measurement of
the latter gives exactly TV=1/2<D. The uninformative POVM (0,I) yields TV=0 for
an orthogonal pair. Tests also cover attained optima, triangle inequalities,
empty classical vectors, identity, permutation, erasure and composed channels.

## Clean Water

Metric theorems concern density matrices. No claim about arbitrary-matrix metrics,
purity preservation or general quantum-channel contraction is made. In particular,
D(Phi(rho),Phi(sigma))<=D(rho,sigma) for CPTP channels needs a separate channel model
and does not follow automatically from classical postprocessing.

Real spectral definitions are noncomputable Lean definitions; regressions are exact
kernel checks, not numerical diagonalization certificates. General quantum
relative-entropy DPI, certified numerical eigensolvers, finite-sample statistics
and physical implementation remain outside scope.
Full Bulletproofs range extraction requires degree-bounded multipoint interpolation
in y,z; independence of powers of one field scalar over that field is not assumed.
Rewinding, computational binding, HVZK, Fiat-Shamir/ROM, Tendermint accountable safety,
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Novelty has not been assessed.

[Detailed contract](../knowledge/03_quantum_information/QuantumChannelTraceDistanceContract.md).

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 172 |
| Lean files under Verification/ | 212 top-level + 2 auxiliary = 214 |
| Root-inclusive sources identical to the reference snapshot | 215 |
| Clean strict build | 3853 jobs; no warnings |
| Complete verifier audit | 24705 declarations; no violations |
| Pinned independent full audit | 24705 declarations; no violations |
| Public live tests | 117; no failures or skips; 341.307s |
| New kernel regression declarations | 36 |
| New numeric runtime scenarios | 0 (analytic Lean definitions) |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 215 proof sources match reference snapshot
6cb4f3eaf0b95aff626de9e827338c0fa1986292 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

