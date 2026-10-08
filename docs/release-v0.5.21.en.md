# Release v0.5.21: Schnorr identification

Private proof snapshot: `0c7104839e071108f4f9d08d6a75c4799f6d2581`.
Previous public main: `6c7a2435b27c46435f4f8fee1222bdd7ba7eaa11`.

## Proven scope and assumptions

The model reuses the Pedersen Setup: an abstract finite additive group of prime
order q with Module (ZMod q) structure. Only the nonzero generator g is used;
oneGeneratorSetup permits h=g. A public Statement contains X, with witness
relation X=x•g. Every group element has a unique witness, derived from the setup.

Perfect completeness proves s•g=R+c•X for R=r•g and s=r+c*x. Two accepting
transcripts with the same R and distinct challenges c₁≠c₂ yield c₁−c₂≠0 and
X=((s₁−s₂)/(c₁−c₂))•g. If X=x•g, the extractor returns exactly x.

The simulator takes only X,c and a uniform response s, and sets R=s•g−c•X.
Perfect special HVZK is an exact equality of full joint transcript PMFs for each
fixed c. The explicit bijection r↦r+c*x relates the real nonce and simulated
response. Equality also holds for any fixed independent challenge PMF, including
the uniform verifier challenge; the real interaction samples its nonce first.
The support is exactly the accepting transcripts with the specified challenge.
Zero secrets, zero nonces, zero challenges and q=2 are included.

Special soundness here is algebraic extraction from two supplied transcripts.
No PPT adversary model, polynomial runtime, adversarial rewinding algorithm,
impersonation bound or computational DLOG hardness is proved. Adaptive malicious
verifiers choosing challenges as a function of R, random oracles, Fiat-Shamir,
noninteractive signatures, concurrent composition and implementation security
are outside this module. The older real-scalar modules remain unchanged.
Python, JSON/SHA-256 and SimLab linkage remain open obligations.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 123 |
| Lean files under Verification/ | 163 top-level + 2 auxiliary = 165 |
| Root-inclusive sources identical to the private snapshot | 166 |
| Clean strict build | 3614 jobs; no warnings |
| Complete verifier audit | 13805 declarations; no violations |
| Pinned independent full audit | 13805 declarations; no violations |
| Public live tests | 68; no failures or skips; 257.020s |

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

Regressions cover arbitrary prime fields and abstract groups, perfect completeness,
the explicit inverse and witness extractor, full transcript laws and (R,s) joint
laws, arbitrary independent challenge distributions, exact support, invalid
responses, zero inputs and characteristic two. Concrete counterexamples show why
same-commitment and distinct-challenge hypotheses are essential for extraction.

All 166 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.21. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography_and_protocols/CryptoSchnorrIdentification.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
