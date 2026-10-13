# Release v0.5.49: FROST threshold Schnorr signatures

Private proof snapshot: `2e3aa42501d148f324dd9e1d88803fcf94710938`.
Previous public main: `38d702d21cef56a04dd8d56a9b85546d288a894f`.

The original private snapshot 41df197c failed a clean strict build because the
FROST module lacked its required copyright header. The corrected private snapshot
adds only a five-line license comment to the Lean file and updates card hashes.
Definitions and proofs are unchanged. The checks below used the corrected sources.

## Proven scope and assumptions

This release proves algebraic FROST verification in a cyclic prime-order group
with scalar field ZMod q. Participants hold evaluations of one Shamir polynomial
of degree below t. Any selected set with at least t distinct nonzero identifiers
can sign. Group interpolation explicitly reuses the verified Shamir theorem.

Each participant supplies two nonce commitments. Binding factors depend on the
common key, message, identifier and commitment list sorted by scalar identifier.
The challenge depends on the aggregate commitment, common key and message.
These are abstract deterministic functions, not concrete hashes or random oracles.
Permuting a valid enumeration preserves the entire canonical session; changing
the signing coalition requires independently recomputed coefficients and context.

The proofs cover partial and aggregate verification, alternative coalitions,
single-response tamper rejection under a fixed transcript, and two opposite errors
that leave a valid aggregate while both partial equations fail. Regressions include
t = 1, t = 2, t = n, more signers than the threshold, and duplicate rejection.

Computational unforgeability and ROM security, concurrent-session attack resistance,
nonce generation and enforced one-time nonce use, DKG/Feldman VSS, concrete curves
and byte serialization are outside scope. No safety under nonce reuse is claimed.
Python, JSON/SHA-256 and SimLab obligations remain open. The Lean-invoking test
harness does not verify a runtime FROST implementation.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 151 |
| Lean files under Verification/ | 191 top-level + 2 auxiliary = 193 |
| Root-inclusive sources identical to the private snapshot | 194 |
| Clean strict build | 3742 jobs; no warnings |
| Complete verifier audit | 20451 declarations; no violations |
| Pinned independent full audit | 20451 declarations; no violations |
| Public live tests | 96; no failures or skips; 302.683s |

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

All 194 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.49. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/04_cryptography/CryptoThresholdSchnorrFrostGroup.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
