# Release v0.5.46: Vector Pedersen commitments

Private proof snapshot: `3f3dc24abfe6d9b6a44069e88f3abd5f49aaa8ed`.
Previous public main: `bd0b9c69c788b37cab34f93a49b6790386a29aa9`.

## Proven scope and assumptions

Vector Pedersen commitments over cyclic groups of prime order q satisfy vector
addition, scalar multiplication and arbitrary finite weighted homomorphism.
For each fixed message vector, the blinding map is bijective; uniform blinding
therefore gives a uniform PMF on the group and identical laws for all fixed vectors.

A collision is equivalent to an exact linear relation among the message generators
and the blinding generator. Distinct message vectors yield a nonzero message
coefficient. One generator logarithm is extracted conditionally when the other
generator relations are known and its coefficient is nonzero. Equal bases give
swap collisions; a known nonzero relation constructs distinct alternate openings.
The k=1 specialization matches the actual scalar Pedersen commitment.

Generators form an indexed family, not a linearly independent basis in a cyclic
group. The concrete ZMod q model witnesses the algebraic assumptions, not hardness.
Computational binding against polynomial-time adversaries, CRS or parameter
generation, coordinate opening proofs, ZKP and Bulletproofs inner-product protocols
are not modeled. Python, JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 148 |
| Lean files under Verification/ | 188 top-level + 2 auxiliary = 190 |
| Root-inclusive sources identical to the private snapshot | 191 |
| Clean strict build | 3738 jobs; no warnings |
| Complete verifier audit | 18990 declarations; no violations |
| Pinned independent full audit | 18990 declarations; no violations |
| Public live tests | 93; no failures or skips; 290.036s |

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

All 191 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.46. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoCommitmentVectorPedersenGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
