# Release v0.5.42: Three-generals oral Byzantine broadcast

Private proof snapshot: `b16060ad3d32182d2dc14394bc1fccaf8dfc1399`.
Previous public main: `986bdf530d3428b344892268ec703a3ec4777933`.

## Proven scope and assumptions

The module proves impossibility of deterministic Byzantine broadcast for exactly
three processes and at most one static Byzantine identity in synchronous oral
messages (OM). Honest messages are delivered reliably with immediate sender
identities; the faulty node may send arbitrary recipient-specific messages or
remain silent. Only the commander initially receives the binary order.

A joint recursion maintains two honest commander copies and two shared lieutenants.
Three admissible executions are constructed from their earlier states. Induction
on rounds proves equality of the honest lieutenants' local histories; CommanderValidity
forces conflicting decisions when the commander is faulty, contradicting Agreement.
This holds for every fixed finite horizon T, including zero. Constant retreat,
naive direct-command following and all-honest executions are covered by regressions.

The general n <= 3f lower bound, signed messages (SM), randomized consensus and
termination without a common finite bound are outside scope. The result is not
an asynchronous crash-failure FLP theorem. Python, JSON/SHA-256 and SimLab
obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 144 |
| Lean files under Verification/ | 184 top-level + 2 auxiliary = 186 |
| Root-inclusive sources identical to the private snapshot | 187 |
| Clean strict build | 3734 jobs; no warnings |
| Complete verifier audit | 18521 declarations; no violations |
| Pinned independent full audit | 18521 declarations; no violations |
| Public live tests | 89; no failures or skips; 288.517s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

All 187 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.42. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedByzantineThreeGeneralsOralImpossibility.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
