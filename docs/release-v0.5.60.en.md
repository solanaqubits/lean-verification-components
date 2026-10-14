# Release v0.5.60: POVM information entropy

This release adds the 162nd direct subject-suite import,
`QuantumPOVMInformationEntropy`. All 205 root-inclusive Lean proof sources
match reference snapshot 22f869e47aa9b9d9703bee7520b3798e693f6b15 byte-for-byte.

## Mathematical contract

For any nonzero finite Hilbert-space dimension, finite POVMs E,F and density
matrix rho, the module proves the Maassen-Uffink bound in bits:

    H_2(P_E^rho) + H_2(P_F^rho) >= -2 ln(c(E,F))/ln(2).

The coefficient c is max ||sqrt(E_j) sqrt(F_k)|| in the Euclidean operator norm.
The proof establishes 0<c<=1, strict positivity of the lower bound for c<1,
and monotonicity of the lower bound in c. It proves probability normalization,
entropy nonnegativity and concavity. Pure-state uncertainty follows analytically
from Hadamard three-lines and Naimark phase contractions; spectral decomposition
and finite Jensen concavity extend it to all density matrices.

Coles et al. use squared overlap c^2 in Section III.D, equations (49)-(50):
-log_2(c^2) = -2 log_2(c). No inequality is assumed as a substitute for its proof.

Thirty kernel regression examples include Pauli X/Z with overlap 1/sqrt(2),
one-bit bound and attainment on the Z eigenstate, the maximally mixed qubit
with two-bit entropy sum, a noncommuting qutrit pair with a shared zero-entropy
state, zero effects, outcome permutations and the general all-state bounds.
Identical projective basis measurements have c=1; equality E=F alone does not
imply c=1 for arbitrary POVMs.

## Clean Water

The model uses exact noncomputable real/complex mathematics. Finite samples,
statistical estimation, quantum side information, numerical logarithm certificates
and cryptographic protocol security are not modeled. Bulletproofs knowledge
extraction, HVZK and Fiat-Shamir/ROM remain open, as do Python, JSON/SHA-256 and
SimLab correspondence obligations. No mathematical novelty claim is made.

[Detailed contract](../knowledge/03_quantum_information/QuantumPOVMInformationEntropy.md).

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 162 |
| Lean files under Verification/ | 202 top-level + 2 auxiliary = 204 |
| Root-inclusive sources identical to the reference snapshot | 205 |
| Clean strict build | 3842 jobs; no warnings |
| Complete verifier audit | 22607 declarations; no violations |
| Pinned independent full audit | 22607 declarations; no violations |
| Public live tests | 107; no failures or skips; 317.111s |
| New kernel regression examples | 30 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 205 proof sources match reference snapshot
22f869e47aa9b9d9703bee7520b3798e693f6b15 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

