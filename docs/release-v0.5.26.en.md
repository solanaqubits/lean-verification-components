# Release v0.5.26: Raymond tree message complexity

Private proof snapshot: `9cc2a20c343c62e126b0fc1f7fd34fd4ad88f78a`.
Previous public main: `0f215dccc351eb8803eda75ab87e84ce5e854b12`.

## Proven scope and assumptions

The module reuses DistributedRaymondTreeMutex without changing its transition
semantics. A completed isolated request starts with one token owner, empty queues
and no network traffic. Only one client invokes requests. The imported accounting
identity counts actual network sends: REQUEST=dist(u,t), PRIVILEGE=dist(u,t).
Local handler steps, message receipt and elapsed time are not counted as sends.

Finite maxima define treeDiameter and treeHeight. The new theorems establish
M(u,t)=2 dist(u,t)<=2 diameter<=4 height(root). Reaching 4h requires an explicit
pair of maximum-depth vertices whose shortest path passes through the root.
Height alone does not imply diameter=2h.

Finite legal completion is proved separately, by a bounded increasing integer
service rank and existence of an enabled service step while the client remains
requesting. The diameter theorem supplies valid holder routes, an actual finite
IsolatedExecution reaching inCS and send count exactly 2 diameter. This is an
existence theorem using classical choice, not an executable scheduler or a claim
that every arbitrary schedule terminates. No service assumption is inserted into
the existence witness. The prior module's fairness contracts remain separate.

Complete k-ary trees are explicit graphs of words over Fin k of length at most h,
with dropLast as parent. Connectivity and acyclicity are proved. For k>=2, h>=1:
N=sum(j=0..h) k^j=(k^(h+1)-1)/(k-1), height=h, diameter=2h, and Mmax=4h.
The inequalities k^h<=N<k^(h+1) give h=Nat.log k N. A Mathlib IsBigO theorem
formalizes logarithmic cost in actual vertex count, atTop in h for each fixed k.
Isomorphisms transfer these graphs to Fin(card V), where actual protocol traces
attain the stated maxima. Chain and star graphs are explicitly constructed too.

Regressions cover local ownership (zero sends), a chain (2(N-1)), a star for N>=3
(four sends), and the binary height-three tree (15 nodes, diameter six, exactly
12 sends and not eight). A ternary height-two example has 13 nodes and eight
sends. Degenerate single-node and height-zero counting cases are also checked.

Only isolated REQUEST and PRIVILEGE sends are analyzed. Concurrent request costs,
amortized queues, random traffic, physical latency and faults are not modeled by
this extension. Logarithmic cost is specific to this tree family; a chain remains
linear. Implementation refinement, Python correctness, JSON/SHA-256 correctness
and SimLab-to-Lean correspondence remain open. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 128 |
| Lean files under Verification/ | 168 top-level + 2 auxiliary = 170 |
| Root-inclusive sources identical to the private snapshot | 171 |
| Clean strict build | 3619 jobs; no warnings |
| Complete verifier audit | 14727 declarations; no violations |
| Pinned independent full audit | 14727 declarations; no violations |
| Public live tests | 73; no failures or skips; 267.488s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py" -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

Regressions exercise actual finite completion and send counters as well as the
explicit graph families, exact vertex counts and logarithmic relation.
Existing subject definitions and proofs remain unchanged.

All 171 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.26. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedRaymondTreeMessageComplexity.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
