# Release v0.5.34: BB84 QBER from Born measurement

Private proof snapshot: `2fff8672332796ab463396cdf799e0112e3886eb`.
Previous public main: `cefa4374b0985c6d56bc61b2c00ff069148ee0bc`.

## Proven scope and assumptions

The module constructs normalized Z/X qubit states and their rank-one projectors,
proving orthogonality, completeness and mutual unbiasedness. Born measurement is
an explicit physical modeling postulate; its probabilities are proved nonnegative
and normalized for density operators. The measurement-and-repreparation channel
is one half of the sum of the four P rho P terms, with trace preservation and
positivity. A counterexample shows that a quarter-prefactor halves the trace.

A normalized finite round law is linked to the matrix channel and to a PMF.
Independent uniform basis choices give sifting probability 1/2, joint error and
sifting probability 1/8, and conditional error probability Pr(error | S) = 1/4.
Independent partial interception with probability f in [0,1] gives QBER(f) = f/4.
For m independent sifted rounds, the product probability law yields detection
probability 1-(3/4)^m and strictly positive evasion probability (3/4)^m.
This is a theoretical conditional error probability, not a deterministic lower
bound on an empirical error fraction. Regressions include f=0, f=1, m=0, m=2
(detection 7/16), normalization and the incorrect channel prefactor. The derived
error probability agrees with the earlier scalar QuantumBB84Protocol model.

The scope is ideal independent individual intercept-resend in the Z/X bases,
with ideal single-qubit preparation and projective measurement. The classical
basis-comparison channel is assumed perfectly authenticated. Collective and
coherent attacks, active attacks on basis negotiation, error reconciliation,
privacy amplification, finite-key secrecy, imperfect single-photon sources/PNS,
losses and detector dark counts are not modeled. Sampling without replacement
from a fixed bit string is outside the independent-round model.
Python, JSON/SHA-256 and SimLab correctness obligations remain open.
Scientific novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 136 |
| Lean files under Verification/ | 176 top-level + 2 auxiliary = 178 |
| Root-inclusive sources identical to the private snapshot | 179 |
| Clean strict build | 3726 jobs; no warnings |
| Complete verifier audit | 17081 declarations; no violations |
| Pinned independent full audit | 17081 declarations; no violations |
| Public live tests | 81; no failures or skips; 277.682s |

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

All 179 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.34. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumBB84ProtocolQBER.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
