# Release v0.5.47: Finite-field Shamir sharing

Private proof snapshot: `2ad7e5e834573c88722a35a8ad2c47dbf971e302`.
Previous public main: `b1f43c3adc8eef1c070b64bff19df47078d8e592`.

## Proven scope and assumptions

Shamir sharing uses a prime q, 1 ≤ t ≤ n < q, and distinct nonzero participant
coordinates in ZMod q. Polynomials have degree strictly below t and constant
term s; the leading coefficient may be zero. Lagrange interpolation recovers s
from any t correctly formed shares, with nonzero denominators derived from
coordinate injectivity.

For each fixed coalition A with |A| < t, a normalized vanishing polynomial
L_A has value one at zero and vanishes at every observed coordinate. The explicit
bijection p ↦ p + (s' - s) • L_A changes the secret and preserves the full vector
of observed shares. Transporting the uniform PMF on bounded-degree polynomials
proves equality of the joint observation distributions for every pair of secrets.
This is statistical perfect secrecy for fixed passive coalitions, not merely
algebraic compatibility with a candidate secret.

Finite weighted sums preserve the degree bound and combine both secrets and
shares linearly. The group lift reconstructs the point s • G in a cyclic group
of prime order q. Generator injectivity guarantees mathematical uniqueness of
the scalar, without an efficient discrete-log decoder. The scalar bridge
specializes a field identity independently to the existing real 2-of-n model
and to ZMod q. A concrete ZMod q setup witnesses the assumptions.

Regressions cover a 3-of-4 example, thresholds 1, 2 and n, empty coalitions,
relabelling, zero and negative weights, and leakage from coordinate zero.
VSS/Feldman, active share forgery, DKG, proactive refresh, adaptive corruptions,
threshold signatures, efficient DLOG decoding, concrete curves and serialization
are not modeled. Python, JSON/SHA-256 and SimLab obligations remain open.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 149 |
| Lean files under Verification/ | 189 top-level + 2 auxiliary = 191 |
| Root-inclusive sources identical to the private snapshot | 192 |
| Clean strict build | 3740 jobs; no warnings |
| Complete verifier audit | 19077 declarations; no violations |
| Pinned independent full audit | 19077 declarations; no violations |
| Public live tests | 94; no failures or skips; 297.242s |

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

All 192 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.47. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoShamirSecretSharingGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
