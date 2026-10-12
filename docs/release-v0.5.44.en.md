# Release v0.5.44: BLS aggregation in bilinear groups

Private proof snapshot: `d450b5712764642fbecf436870d0a1f713270819`.
Previous public main: `7cf7827dab55c9dd7faf77c708c72e9e717e9a86`.

## Proven scope and assumptions

The module proves algebraic BLS completeness in three abstract cyclic groups
of prime order q, with scalars in ZMod q and a nondegenerate bilinear pairing.
It establishes individual verification, aggregation for arbitrary finite message
families, common-message aggregation and composition of accepted partials.
Message distinctness is not required for these algebraic identities.

Pairing injectivity follows from cyclicity and nondegeneracy. A concrete model
with all groups equal to ZMod q and multiplication as the pairing witnesses
realizability of the assumptions; this model is not cryptographically secure.
A shared commutative-ring identity is independently specialized over the reals
and ZMod q, without asserting a homomorphism between these fields.

Explicit algebraic counterexamples show rogue-key vulnerability of naive
common-message aggregation without PoP and cancellation of two nonzero signature
errors: both altered components are individually invalid while their sum verifies.
Regressions cover one and two participants, repeated messages and keys,
permutations, zero secrets, and concrete arithmetic modulo 7.

Concrete curves such as BLS12-381, Miller's algorithm, hash-to-curve, point
validation, serialization, PoP and computational security reductions in
ROM/Co-CDH are not modeled. Python, JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 146 |
| Lean files under Verification/ | 186 top-level + 2 auxiliary = 188 |
| Root-inclusive sources identical to the private snapshot | 189 |
| Clean strict build | 3736 jobs; no warnings |
| Complete verifier audit | 18858 declarations; no violations |
| Pinned independent full audit | 18858 declarations; no violations |
| Public live tests | 91; no failures or skips; 294.911s |

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

All 189 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.44. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoBLSSignatureAggregationGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
