# Release v0.5.73: CPTP channels and trace-distance contraction

[Detailed contract](../knowledge/03_quantum_information/QuantumCPTPChannelContract.md)

The 175th direct module defines finite rectangular Kraus channels with
sum K_j† K_j = I, reusing the existing complex-linear channel API and its complete
positivity theorem for all finite block amplifications. It proves preservation of
trace and density matrices, the trace-adjoint identity for the dual Kraus map,
and pullback of effects with positive complements.

Trace-distance contraction follows by pulling the output Helstrom effect back
to the input variational bound from module 172. A second theorem covers every
abstract finite-dimensional CPTP Channel in the existing API through positivity,
trace preservation and the positive/negative parts of the input difference.
The existing trace norm is used; no commutation assumption is introduced.

Identity and unitary channels preserve distance. Replacement by a fixed pure
basis state gives zero distance, including rectangular input/output dimensions.
Computational-basis dephasing sends the distinct pure states |+><+| and |-><-|
to I/2, giving strict loss. Thirty exact Lean regressions cover these cases,
arbitrary ancillas, dual effects, non-unital reset, composition and measurement TV.

## Clean Water

The construction starts from a finite Kraus family. No new equivalence theorem
between all channel representations is claimed. Stinespring dilation and that
full equivalence are outside this module; prior library representation results
are reused where relevant. General quantum relative-entropy DPI, numerical
certification of approximate operators and physical implementation are excluded.
Full Bulletproofs range extraction via multipoint interpolation, Tendermint
Accountable Safety, Python, JSON/SHA-256 and SimLab remain open.

## Verification workflow

The updated agent skill and English guide distinguish targeted development checks
from one final full release gate. Module verify already includes its axiom audit;
a second audit on unchanged inputs is redundant. The incremental Lake cache is
retained. Public validation is performed on this export, independently of private
validation; build targets are not described as freshly compiled proofs.

All 218 project Lean sources match private snapshot
6c5e9b05db4502232b9d90608694c9ccf1912a0c byte-for-byte. Only English cards are exported.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 175 |
| Lean files under Verification/ | 215 top-level + 2 auxiliary = 217 |
| Root-inclusive sources identical to the private snapshot | 218 |
| Incremental strict build | 3856 targets; no warnings; 12.582s |
| Complete verifier audit | 25193 declarations; no violations |
| Pinned independent full audit | 25193 declarations; no violations |
| Public live tests | 120; no failures or skips; 355.399s |
| New exact Lean regressions | 30 |

Only propext, Classical.choice and Quot.sound are allowed. Registry and catalog
checks also passed. The independent auditor is pinned to commit
46024e005996495c65ef609368e11ab39c4222e3 and binary SHA-256
8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1; auditor source toolchain file: v4.32.0-rc1.
The independent audit is not a second proof kernel.

The final public gate ran once with the Lake cache retained. This is not a clean
rebuild; the target count does not count freshly compiled proofs. All 218 proof
sources match 6c5e9b05db4502232b9d90608694c9ccf1912a0c byte-for-byte.
Public baseline: deb762a760e4aaee8bbb188740ebb7f71e9681f2. No Russian cards were exported.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```
