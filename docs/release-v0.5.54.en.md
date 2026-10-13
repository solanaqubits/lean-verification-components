# Release v0.5.54: linear interactive Pedersen range proofs

This release exports CryptoPedersenRangeProofLinear and its suite integration from
private snapshot `73f9a1aeee7071192a8487dd210a3502b6a74499`. It follows public main
`825c4c7e0cd05eaad43570078d345ea1fd0b4540` (v0.5.53).

## Formal contract

Natural bit decomposition characterizes v < 2^m; the range embeds without wrapping
into ZMod q when 2^m < q. Bit commitments aggregate with weights 2^i to the fixed
public Pedersen commitment. Parallel CDS OR proofs share one verifier challenge.
The verifier checks both branch equations, each challenge split and the aggregate.

Completeness holds for every bounded natural value and every original blinding.
Two accepted transcripts with identical full first messages and distinct common
challenges yield an explicit natural range value and a blinding opening C.
First-message independence from the subsequent challenge is proved separately.

The special HVZK theorem is equality of full joint transcript PMFs, including
correlated bit commitments with their fixed aggregate. A public simulator samples
free group elements, solves the coefficient-one coordinate and simulates the OR
branches. It does not take the secret opening or compute a discrete logarithm.
The interaction theorem covers arbitrary independently sampled challenge PMFs.

Different field openings of the same commitment yield an explicit generator
relation g=((r'-r)/(v-v'))*h. This is an algebraic DLOG reduction, not unconditional
binding. The regression wrapper checks 20 Lean examples and 8 execution cases.
See the [complete contract](../knowledge/04_cryptography/CryptoPedersenRangeProofLinear.md).

## Clean Water boundaries

Fiat-Shamir/ROM, arbitrary malicious verifiers, concrete elliptic curves and byte
serialization are not modeled. Computational DLOG hardness, general adversarial
rewinding runtime, implemented random sampling and unconditional equality with a
previously supplied opening are not proved. Python, JSON/SHA-256 and SimLab
correspondence obligations remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 156 |
| Lean files under Verification/ | 196 top-level + 2 auxiliary = 198 |
| Root-inclusive sources identical to the private snapshot | 199 |
| Clean strict build | 3763 jobs; no warnings |
| Complete verifier audit | 21556 declarations; no violations |
| Pinned independent full audit | 21556 declarations; no violations |
| Public live tests | 101; no failures or skips; 315.244s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 199 proof sources match private snapshot
73f9a1aeee7071192a8487dd210a3502b6a74499 byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

