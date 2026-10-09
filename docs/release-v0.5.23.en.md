# Release v0.5.23: Balanced Deutsch-Jozsa oracle classification

Private proof snapshot: `2dba8201d6046e7017c2353c95941dd5d51237f8`.
Previous public main: `471aa8b88920e6c8631786063fa554f5b6f58d17`.

## Proven scope and assumptions

The module reuses Bits n, IsBalanced, runDJ and outcomeWeight from
QuantumDeutschJozsaGeneral. BalancedFamily is the subtype of all oracles satisfying
that existing predicate. Support and Boolean characteristic maps are explicit
inverses. For n>=1 their restriction gives an equivalence with subsets of
cardinality 2^(n-1), yielding choose(2^n,2^(n-1)) via Finset.card_powersetCard.

For n=0 the domain is a singleton and the balanced family is empty. The unguarded
formula is false because natural subtraction saturates: choose(2^0,2^(0-1))=1.
The total formula branches on n=0. Counts for n=0,1,2,3 are exactly 0,2,6,70.
Positive cases use the general theorem and kernel reduction of binomial arithmetic.

For arbitrary n and arbitrary f, without DJPromise, balance is equivalent to zero
signed-mean amplitude, zero squared probability, and zero operational amplitude
and outcomeWeight at the all-zero basis state in runDJ. The circuit result is
inherited through the existing proved amplitude bridge, not postulated afresh.
The first-bit projection witnesses balance for every positive n. A relabeling
between Bits n and Fin (2^n) preserves trueCount and IsBalanced.

Under DJPromise a paired theorem proves (P0=0 iff balanced) and (P0=1 iff constant).
This is not a claim to classify arbitrary unpromised oracles from one nonzero
measurement. The finite cardinality presentation uses noncomputable/classical
constructions where needed. Efficient enumeration, generation or sampling of
oracles, asymptotic density, hardware synthesis and physical noise are not modeled.
Python, JSON/SHA-256 and SimLab remain open obligations. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 125 |
| Lean files under Verification/ | 165 top-level + 2 auxiliary = 167 |
| Root-inclusive sources identical to the private snapshot | 168 |
| Clean strict build | 3616 jobs; no warnings |
| Complete verifier audit | 14330 declarations; no violations |
| Pinned independent full audit | 14330 declarations; no violations |
| Public live tests | 70; no failures or skips; 262.919s |

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

Regressions cover all four small counts, failure of the unguarded zero-qubit
formula, both support round trips, finite-register relabeling, promise-free circuit
interference, first-bit projection, exclusion of constants and a nonlinear balanced
oracle. The existing Deutsch-Jozsa definitions and proofs remain unchanged.

All 168 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; no Russian cards are exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, verify its remote SHA, then
annotated v0.5.23. This is not atomic. Existing tags are not overwritten.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/03_quantum_physics_and_optics/QuantumDeutschJozsaNBitBalanced.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
