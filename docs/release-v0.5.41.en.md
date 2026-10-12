# Release v0.5.41: Finite-group Schnorr aggregation

Private proof snapshot: `0744cfdef0c8cc1529eab2c5006dd47ffb678d27`.
Previous public main: `7352c57235e749f7df2af5dd143ac4a1814ac138`.

## Proven scope and assumptions

Scalars are ZMod q for a prime q. CyclicSetup supplies an additive commutative
group, a compatible module action and a generator G with bijective map x ↦ x • G.
This gives a cyclic group of order q; no efficient discrete-log inverse or hardness
claim is supplied. An ordered Fin n key vector preserves duplicates. The honest
main theorem assumes n >= 2; auxiliary module identities hold more generally.

Two separately typed deterministic functions supply a_i = H_agg L (L i) and
c = H_sig X_agg R_agg m. Honest partials satisfy
s_i • G = R_i + (c * a_i) • X_i. Their sum satisfies aggregate verification.
A separate theorem assembles any accepted partial equations with a common
challenge and coefficients; it does not prove knowledge of the secret keys.
The requested theorem name containing soundness denotes algebraic completeness.

For naive two-key addition, bad = z • G - honest makes the aggregate z • G.
The response r + c * z verifies against nonce r • G using only the honest public
key and the selected scalars z and r. This is a witness against naive aggregation,
not an attack on correctly instantiated MuSig. Regressions include two signers
over ZMod 7, duplicate keys, zero weights and aggregate-key cancellation.
A zero coefficient removes a fixed term; changing the key vector can rehash
other coefficients. Degenerate-key rejection is not implemented.

The scalar bridge specializes a common commutative-ring identity independently
to the existing real two-nonce definitions and to ZMod q scalar action. There is
no asserted map from arbitrary real scalars to the finite field, and two nonce
variables do not model interactive rounds.

This release proves algebraic correctness only. AGM/ROM reductions, hashed-key
rogue-key resistance, nonce generation and non-reuse, concurrent-session security,
interactive MuSig2/BIP327, curve implementation and byte serialization are outside
scope. The two function interfaces do not prove cryptographic domain separation.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 143 |
| Lean files under Verification/ | 183 top-level + 2 auxiliary = 185 |
| Root-inclusive sources identical to the private snapshot | 186 |
| Clean strict build | 3733 jobs; no warnings |
| Complete verifier audit | 18362 declarations; no violations |
| Pinned independent full audit | 18362 declarations; no violations |
| Public live tests | 88; no failures or skips; 290.769s |

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

All 186 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.41. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoSchnorrMultiSignaturesMuSigGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
