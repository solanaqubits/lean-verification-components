# Release v0.5.50: No-broadcasting for mixed quantum states

Private proof snapshot: `afab7ff359d805188950bb8a073c33f63dcb3b72`.
Previous public main: `e48328ce63953c007dd8d5f82ad01496913c0926`.

## Proven scope

For finite-dimensional complex density matrices, one CPTP channel broadcasts both
states exactly if and only if they commute. Only the two marginals are prescribed;
outputs may be correlated. Complete positivity is defined for all finite matrix
amplifications independently of the broadcasting predicate.

Constructive sufficiency uses a joint orthonormal eigenbasis and explicit
measure-and-prepare Kraus operators. Necessity derives a Kraus representation
from complete positivity, constructs a symmetric logarithmic derivative for the
sum of the states, and applies an operator sum-of-squares argument. Zero spectral
denominators are handled by positivity; singular states and repeated eigenvalues
are included. No fidelity equality condition is assumed.

The pure-state criterion allows orthogonal vectors or equality up to global phase.
The proofs include identical mixed states and a bridge from unitary cloning with
a blank register. Regressions cover scalar dimension, mixed and pure qubits,
correlated outputs, phase changes, arbitrary ancillas and a degenerate common kernel.

Infinite-dimensional spaces, approximate broadcasting, continuous variables and
physical measurement implementations are outside scope. Python, JSON/SHA-256 and
SimLab correspondence obligations remain open. Declaration counts include generated
declarations and are not counts of independent mathematical theorems.

## Public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 152 |
| Lean files under Verification/ | 192 top-level + 2 auxiliary = 194 |
| Root-inclusive sources identical to the private snapshot | 195 |
| Clean strict build | 3752 jobs; no warnings |
| Complete verifier audit | 20622 declarations; no violations |
| Pinned independent full audit | 20622 declarations; no violations |
| Public live tests | 97; no failures or skips; 308.562s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. Integration is idempotent. All 195 proof sources
match private snapshot afab7ff359d805188950bb8a073c33f63dcb3b72 byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Publication and preservation

Publication uses sequential pushes of main and the annotated v0.5.50 tag.
Existing tags are never overwritten. Original workspace HEAD and tracked files
are preserved, and this task does not write to simulations/.

[Detailed contract](../knowledge/03_quantum/QuantumNoBroadcastingMixed.md)
· [Measured commands and hashes](../tools/validation_snapshot.json)
