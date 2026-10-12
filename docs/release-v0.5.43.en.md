# Release v0.5.43: Signed Byzantine broadcast

Private proof snapshot: `2b03b38cacf29b0ad2cc386316aeb7ddb1c1fd0e`.
Previous public main: `4e66be99292e0ac581920bafca33849752bb5f70`.

## Proven scope and assumptions

The module proves Agreement and CommanderValidity for a deterministic,
synchronous signed-chain broadcast protocol with n >= f + 2 nodes, a static
fault set of size at most f, and decisions after exactly f + 1 rounds.
The guarantee concerns honest lieutenants; the commander is excluded from
lieutenant-view equality. The population restriction guarantees at least two
honest nodes, not necessarily two honest lieutenants when the commander is honest.

Ideal signatures are modeled by an inductive derivation environment backed by
an operational issuance ledger. Honest signature occurrences require previously
issued matching prefixes. Their actual signing transitions and receipt rounds
are proved from executions; the honest commander signs its input initially.
Delivery assumes reliable honest transmission and derivable signatures, without
assuming propagation or agreement. Acceptance checks the commander root, distinct
signers and a chain length equal to the current round. Honest views accumulate
monotonically. Propagation and a pigeonhole argument for f + 1 distinct signers
imply equal final views. An honest commander's final views are its singleton order.
Reachable nonterminal states can advance and completed executions exist.

Regressions include n = 3, f = 1, contradictory orders, silence, an honest
commander, malformed chains and a valid late short-chain attack when the final
round-length filter is removed. A formal bridge contrasts the result with the
three-node oral-message impossibility theorem. This is an explicit round-indexed
signed-chain implementation, not a claim about every optimization of SM(f).

The cryptographic environment is idealized. Computational properties of concrete
signature schemes such as RSA/ECDSA, byte serialization, asynchronous channels,
dynamic faults and optimal message complexity are outside scope. Python,
JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 145 |
| Lean files under Verification/ | 185 top-level + 2 auxiliary = 187 |
| Root-inclusive sources identical to the private snapshot | 188 |
| Clean strict build | 3735 jobs; no warnings |
| Complete verifier audit | 18776 declarations; no violations |
| Pinned independent full audit | 18776 declarations; no violations |
| Public live tests | 90; no failures or skips; 291.801s |

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

All 188 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.43. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedByzantineSignedGeneralsValidity.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
