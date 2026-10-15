# Release v0.5.69: Holevo–Helstrom state discrimination

This release adds QuantumHelstromStateDiscrimination as the 171st direct
MasterSuite import. All 214 Lean sources match reference snapshot
1f8a4af621a3b875f94773036eea2412294fe517 byte-for-byte.

## Formal result

For density matrices and nonnegative priors summing to one, the module proves
the Holevo–Helstrom upper bound (1 + ||Delta||_1)/2 without commutation assumptions.
The trace norm is Re Tr(sqrt(Delta† Delta)), identified with the sum of absolute
Hermitian eigenvalues. An orthogonal projector on strictly positive eigenvalues
attains the bound. Independent choices of zero eigenvectors preserve the optimum;
uniqueness and a classification of every optimal effect are not claimed.

The module proves Bayes rule optimality, its attainment, and Guess(M o E) <= Guess(E)
for classical stochastic postprocessing of a finite POVM. Randomized decision rules
induce valid binary effects and are bounded by the global Helstrom optimum.
Regressions cover identical and orthogonal states, zero priors, erasure and outcome
permutations, and noncommuting |0> and |+> states with equal priors: trace norm
1/sqrt(2) and optimal success (1+1/sqrt(2))/2. A fixed suboptimal rule can improve
from zero to one after bit inversion without contradicting optimal guessing DPI.

## Clean Water

These are finite-dimensional analytic spectral and classical probability results.
Real-valued spectral definitions are noncomputable Lean definitions; the 36 new
regressions are kernel-checked declarations, not numerical spectral executions.
Certified floating-point eigensolvers, finite-sample estimation, physical measurement
implementation and general quantum relative-entropy DPI for CPTP channels remain
outside the model. Full Bulletproofs range extraction requires explicit degree bounds
and multipoint interpolation in y,z; powers of one field scalar are not assumed
linearly independent over that field. Rewinding, computational binding, HVZK,
Fiat–Shamir/ROM, Tendermint accountability, Python, JSON/SHA-256 and SimLab obligations
remain open. Novelty has not been assessed.

[Detailed contract](../knowledge/03_quantum_information/QuantumHelstromStateDiscrimination.md).

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 171 |
| Lean files under Verification/ | 211 top-level + 2 auxiliary = 213 |
| Root-inclusive sources identical to the reference snapshot | 214 |
| Clean strict build | 3852 jobs; no warnings |
| Complete verifier audit | 24623 declarations; no violations |
| Pinned independent full audit | 24623 declarations; no violations |
| Public live tests | 116; no failures or skips; 339.56s |
| New kernel regression declarations | 36 |
| New numeric runtime scenarios | 0 (analytic Lean definitions) |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 214 proof sources match reference snapshot
1f8a4af621a3b875f94773036eea2412294fe517 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

