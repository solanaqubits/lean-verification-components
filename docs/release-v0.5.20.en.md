# Release v0.5.20: Pedersen homomorphic sums

Private proof snapshot: `2c01798362d54124a711be83a0855e40dbf0efdc`.
Previous public main: `516a6784205e5ae66459def7087733e8dfd152b4`.

## Proven scope and assumptions

The setup is an abstract finite additive abelian group of prime order q, with a
Module (ZMod q) structure and two nonzero generators g,h. No discrete logarithm
relation is supplied. Finite weighted sums satisfy
sum cᵢ • C(mᵢ,rᵢ) = C(sum cᵢmᵢ,sum cᵢrᵢ), including empty families.

Perfect hiding is an exact PMF equality: uniform masking gives a uniform group
value for every fixed message. Aggregate hiding requires an index in the family
with a nonzero coefficient and a fresh independent uniform mask. Coefficients
and messages are fixed; the remaining masks may have an arbitrary joint law.
The refreshed coordinate's joint law with the remaining vector is proved to
factor. All-zero weights give a point mass at zero, not a uniform group value.
Uniform marginals alone do not suffice: correlated masks [t,−t] cancel exactly.

A collision C(m,r)=C(m′,r′) with m≠m′ implies r≠r′ and
h = ((m−m′)/(r′−r)) • g. This is an algebraic DLOG extraction, not a theorem of
computational binding or DLOG hardness. Aggregation concerns the scalar weighted
sum; vectors [1,0] and [0,1] have equal aggregates under weights [1,1].
A concrete setup proves satisfiability, while a known generator relation permits
alternative openings. The older real-scalar commitment module is unchanged.

PPT adversaries, computational hardness, IND-CPA/EUF-CMA games, multi-generator
vector commitments and implementation security are not claimed. Python,
JSON/SHA-256 and SimLab linkage remain open obligations.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 122 |
| Lean files under Verification/ | 162 top-level + 2 auxiliary = 164 |
| Root-inclusive sources identical to the private snapshot | 165 |
| Clean strict build | 3613 jobs; no warnings |
| Complete verifier audit | 13704 declarations; no violations |
| Pinned independent full audit | 13704 declarations; no violations |
| Public live tests | 67; no failures or skips; 248.050s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Its deleted temporary checkout was restored at that commit and rebuilt with Lean
v4.33.1; the resulting binary exactly matches the previous pinned hash.
The auditor source toolchain file records v4.32.0-rc1; the executable is pinned
separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Actual public checks were rerun, rather than inferred
from the earlier private/export evidence. Counts include generated declarations.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py" -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

Regressions cover general prime-order groups, the exact point probability 1/q,
independent refresh and joint-law factorization, correlated uniform marginals,
zero weights and empty families, duplicate values and negative weights, scalar
collision extraction, vector ambiguity, and characteristic-two examples.

All 165 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and public
historical reports are preserved; no Russian cards are exported. Reservoir
metadata are retained; external indexing is not asserted.

## Publication and preservation

Publish the annotated v0.5.20 tag by sequential pushes: main first, verify its
remote SHA, then the tag. This is not atomic. Existing tags are not overwritten.
A publication receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography_and_protocols/CryptoPedersenHomomorphicSum.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
