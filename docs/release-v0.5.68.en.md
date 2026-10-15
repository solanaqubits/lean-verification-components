# Release v0.5.68: recursive IPA transcript tree extraction

This release adds CryptoBulletproofsTreeExtraction as the 170th direct
MasterSuite import. The complete set of 213 Lean proof sources matches reference
snapshot c665583189f495470fff135cc5406beaa70af249 byte-for-byte.

## Formal result

A complete four-branch IPA tree of depth k is validated against an independently
supplied expected root statement. Each node has shared L,R messages before its
four challenges; challenges must be nonzero with distinct squares. Child targets
and generators use the actual fold_generators_G/H and update_target from module
158. Leaves contain terminal scalar responses; internal witnesses are not assumed.

The recursive extractor returns full vectors of length 2^k representing the
original target, or explicit nonzero coefficients of a zero linear combination
of the original root G,H,U. Lifting relations preserves their evaluation and is
injective for nonzero challenges, so a deep relation remains nontrivial at the
root. Generator independence is not assumed. A relation does not imply that no
witness exists.

The checked interface validates every branch, including branches after the first
valid relation. Success is equivalent to tree validity and every successful result
is valid. A selected path yields an accepted transcript for the real IPA verifier.
Honest trees recover exactly their original vectors at every depth. The tree has
4^k=(2^k)^2=n^2 leaves; this differs from the 2k group elements of one IPA transcript.

Regression tests cover honest depths 0,1,2,3, a deep relation lifted to the root,
leaf counts, corrupted leaves and messages, substituted child targets, zero
challenges, repeated or symmetric challenges, and corruption in a later branch
when an earlier branch already returns a valid relation.

## Clean Water

The result is deterministic algebraic processing of a supplied valid complete IPA
tree. Availability or probabilistic construction of that tree by rewinding,
forking bounds and expected polynomial running time remain open. Full range-witness
extraction with bitness, computational binding or discrete-log reductions, HVZK
and Fiat-Shamir/ROM are not proved. This does not extract from independent
completed proofs. Concrete curves, randomness, serialization, trusted context
storage and deployed implementation correspondence are outside the model.
Tendermint Accountable Safety, Python, JSON/SHA-256 and SimLab obligations remain
open. Novelty has not been assessed.

[Detailed contract](../knowledge/04_cryptography/CryptoBulletproofsTreeExtraction.md).

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 170 |
| Lean files under Verification/ | 210 top-level + 2 auxiliary = 212 |
| Root-inclusive sources identical to the reference snapshot | 213 |
| Clean strict build | 3851 jobs; no warnings |
| Complete verifier audit | 24415 declarations; no violations |
| Pinned independent full audit | 24415 declarations; no violations |
| Public live tests | 115; no failures or skips; 340.928s |
| New kernel regression declarations | 30 |
| New executable scenarios | 28 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 213 proof sources match reference snapshot
c665583189f495470fff135cc5406beaa70af249 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

