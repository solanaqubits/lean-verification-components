# Release v0.5.51: Informationally complete POVMs

Private reference: `f6730717e96191a569c840a45b1b3ff2ba1bdb9f`.
Previous public release: `e36ccf0596cd5db25db97dab2e2ccd8c8a91dba9`.

The new [IC-POVM module](../knowledge/03_quantum/QuantumPOVMInformationallyComplete.md)
proves informational completeness iff measurement injectivity on the real space
of Hermitian matrices, strict positivity and invertibility of the frame operator,
and exact reconstruction through its canonical dual frame. Density matrices have
nonnegative outcome probabilities summing to one and are uniquely reconstructed
from those exact probabilities. Every IC-POVM has at least d² outcomes.

An explicit four-outcome tetrahedral qubit SIC-POVM establishes a concrete model.
Basis measurements fail to distinguish a pair of states with different relative
phases. Regressions cover scalar, pure and maximally mixed states and outcome
permutations. The canonical inverse is noncomputable; dual operators need not be
positive semidefinite.

## Scope

All-dimension SIC existence (Zauner's conjecture), finite samples and shot noise,
statistical uncertainty, numerical conditioning, efficient numerical inversion
and maximum-likelihood estimation are outside this contract. Python, JSON/SHA-256
and SimLab correspondence obligations remain open.

## Validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 153 |
| Lean files under Verification/ | 193 top-level + 2 auxiliary = 195 |
| Root-inclusive sources identical to the private snapshot | 196 |
| Clean strict build | 3759 jobs; no warnings |
| Complete verifier audit | 20765 declarations; no violations |
| Pinned independent full audit | 20765 declarations; no violations |
| Public live tests | 98; no failures or skips; 309.983s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 196 proof sources match private snapshot
f6730717e96191a569c840a45b1b3ff2ba1bdb9f byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


After correcting the export template package version to 0.5.51, the strict build
was repeated successfully (3759 jobs); proof sources remained unchanged.
