# Release v0.5.45: Group ElGamal weighted homomorphism

Private proof snapshot: `3dded0e143eb6064cfccaf8e823147e19c3d4b08`.
Previous public main: `6e9b7cf78b002b0c404f2e7bd73de1cdf5a50017`.

## Proven scope and assumptions

Group and exponential ElGamal decryption correctness, uniqueness of the scalar
preimage, and homomorphism of arbitrary finite weighted sums under one public key
are proved over cyclic groups of prime order q. Algebraic rerandomization adds an
encryption of zero. A public ciphertext shift changes the decrypted point by a
provably nonzero amount for a nonzero scalar shift. A concrete ZMod q model
witnesses the assumptions; a general algebraic identity has separate real and
modular specializations linking the earlier scalar model.

Decryption returns the group point m • G. Uniqueness of m does not supply an
efficient discrete-logarithm decoder. Weighted scalar sums are modulo q; interpreting
them as integer totals requires separate range bounds. Rerandomization is an
algebraic identity, with no probability-distribution claim.

IND-CPA/IND-CCA security proofs, DDH reductions, efficient discrete-logarithm
algorithms, concrete elliptic curves and serialization are not modeled.
Python, JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 147 |
| Lean files under Verification/ | 187 top-level + 2 auxiliary = 189 |
| Root-inclusive sources identical to the private snapshot | 190 |
| Clean strict build | 3737 jobs; no warnings |
| Complete verifier audit | 18916 declarations; no violations |
| Pinned independent full audit | 18916 declarations; no violations |
| Public live tests | 92; no failures or skips; 287.423s |

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

All 190 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.45. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoElGamalHomomorphismGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
