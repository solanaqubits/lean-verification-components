# Release v0.5.52: executable Marzullo interval consensus

Private reference: `13f6cabe79f9c25da016489c0777fc4c8a89abb6`.
Previous public main: `5c9dc2d6197afa0acf250061dc465a2e59371526`.

[Detailed contract](../knowledge/09_distributed_systems/DistributedMarzulloIntervalConsensus.md)

The module implements rational boundary-event sorting and cumulative overlap
counters. Starts precede observation and ends follow observation at each coordinate,
so touching and singleton closed intervals are counted correctly. Identical
intervals from distinct sources remain separate votes.

The proofs establish the global maximum, maximal order-convex peak intervals,
and unique selection by shortest length followed by the leftmost endpoint.
Under the fault model, the maximum is at least n − f. The selected peak is
contained, non-strictly, in the safe threshold hull. A three-source counterexample
shows that the selected peak can miss true time. The computed hull agrees exactly
with the real-valued thresholdHull, including models with irrational true time.
Permutation invariance and empty, zero-threshold and infeasible cases are covered.

The public regression wrapper checks 23 Lean examples and 10 compiled execution
scenarios. These execution checks complement the kernel proofs.

Full NTP (RFC 5905, A.5.5.1), clock drift, network asymmetry, jitter filtering,
PLL/FLL and physical clock discipline are outside scope. No O(n log n) complexity
bound is claimed. Python, JSON/SHA-256 and SimLab correspondence obligations
remain open. Novelty is not assessed.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 154 |
| Lean files under Verification/ | 194 top-level + 2 auxiliary = 196 |
| Root-inclusive sources identical to the private snapshot | 197 |
| Clean strict build | 3761 jobs; no warnings |
| Complete verifier audit | 21023 declarations; no violations |
| Pinned independent full audit | 21023 declarations; no violations |
| Public live tests | 99; no failures or skips; 313.507s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 197 proof sources match private snapshot
13f6cabe79f9c25da016489c0777fc4c8a89abb6 byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

