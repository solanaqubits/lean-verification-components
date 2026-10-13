# Release v0.5.55: stable Marzullo event sorting

This release exports DistributedMarzulloEventSorting from private snapshot
`9985f49dc6de270dd89656baa41a386aae9fc6da`, following public main
`2c35cec7f30104d0dfe2a550886009d11d9a6d0d` (v0.5.54).

## Formal contract

The executable merge sort compares rational coordinates and boundary kinds, with
starts before ends at a shared coordinate. Source labels are not part of the key.
Contiguous splitting and left-first merging preserve the entire order within each
key. The proofs establish List.Perm, sortedness, exact filtered-key stability and
literal equality to insertion sort for every fixed input event list.

A counted recursion returns both the sorted events and the number of comparator
calls. The actual counts satisfy the two-half recurrence with merge cost at most
N-1, and C(xs) <= N * Nat.clog 2 N. For n interval sources, N=2n.

The new merge-based counter, maximum, selected peak and threshold hull equal the
existing backend. Source permutations preserve these consensus results even
though zipIdx assigns different sourceId labels. Peak optimality, non-strict
containment in the safe hull and the exact real thresholdHull bridge are retained.
A peak need not contain true time; the safety theorem concerns the threshold hull.
The regression wrapper checks 26 Lean examples and 12 compiled execution cases.

See the [complete contract](../knowledge/09_distributed_systems/DistributedMarzulloEventSorting.md).

## Clean Water boundaries

The complexity bound counts comparator invocations in this sorting recursion.
Rational numerator/denominator bit complexity, fraction normalization, allocation,
cache locality and parallel sorting are not modeled. No O(n log n) bound is proved
for the complete consensus algorithm or its repeated queries and component/hull
construction. No machine-code cost theorem for library runtime optimizations is
claimed. Full NTP and physical clock discipline remain outside scope.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 157 |
| Lean files under Verification/ | 197 top-level + 2 auxiliary = 199 |
| Root-inclusive sources identical to the private snapshot | 200 |
| Clean strict build | 3764 jobs; no warnings |
| Complete verifier audit | 21722 declarations; no violations |
| Pinned independent full audit | 21722 declarations; no violations |
| Public live tests | 102; no failures or skips; 315.374s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 200 proof sources match private snapshot
9985f49dc6de270dd89656baa41a386aae9fc6da byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

