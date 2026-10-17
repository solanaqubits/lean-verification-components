# Public verification record

## Current checkpoint: v0.7.0

191 direct imports and 235 root-inclusive Lean sources. The subject change is
module 191 in `quantum-physics/qutrit-secret-sharing`. The
[release contract](../docs/release-v0.7.0.en.md) records the exact hierarchy and
acceptance checks. Measured beta results and evidence digests are recorded in the
annotated release tags after validation; historical measurements below retain
their original scope. No prior audit is relabelled as a fresh run.



## Beta 0.6 migration checkpoint

The v0.6.0 candidate contains 190 direct imports and 234 root-inclusive Lean
sources, including three nested support specifications. Publication requires the
complete beta gate in [VERSIONING.md](../VERSIONING.md), with exact source and
runtime fingerprints and externally retained logs. No measurement below is a
new beta 0.6 result; the historical baseline remains distinct until that gate
passes. Independent normative conformance is registered for Simon and the
explicit qutrit decoder, not every subject module.


## Historical full-validation baseline: v0.5.73

[Release v0.5.73](../docs/release-v0.5.73.en.md) · [Detailed contract](03_quantum_information/QuantumCPTPChannelContract.md)

## Historical full-validation measurements

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 175 |
| Lean files under Verification/ | 215 top-level + 2 auxiliary = 217 |
| Root-inclusive sources identical to the private snapshot | 218 |
| Incremental strict build | 3856 targets; no warnings; 12.582s |
| Complete verifier audit | 25193 declarations; no violations |
| Pinned independent full audit | 25193 declarations; no violations |
| Public live tests | 120; no failures or skips; 355.399s |
| New exact Lean regressions | 30 |

Only propext, Classical.choice and Quot.sound are allowed. Registry and catalog
checks also passed. The independent auditor is pinned to commit
46024e005996495c65ef609368e11ab39c4222e3 and binary SHA-256
8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: v4.33.1; auditor source toolchain file: v4.32.0-rc1.
The independent audit is not a second proof kernel.

The final public gate ran once with the Lake cache retained. This is not a clean
rebuild; the target count does not count freshly compiled proofs. All 218 proof
sources match 6c5e9b05db4502232b9d90608694c9ccf1912a0c byte-for-byte.
Public baseline: deb762a760e4aaee8bbb188740ebb7f71e9681f2. No Russian cards were exported.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

## Historical public snapshot: Authorized bad debt writeoff and supplier loss

[Release v0.5.72](../docs/release-v0.5.72.en.md) · [Detailed contract](01_defi/DeFiLendingBadDebtSocialization.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 174 |
| Lean files under Verification/ | 214 top-level + 2 auxiliary = 216 |
| Root-inclusive sources identical to the reference snapshot | 217 |
| Clean strict build | 3855 jobs; no warnings |
| Complete verifier audit | 25105 declarations; no violations |
| Pinned independent full audit | 25105 declarations; no violations |
| Public live tests | 119; no failures or skips; 338.331s |
| New kernel regression declarations | 56 |
| New executable scenarios | 37 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 217 proof sources match reference snapshot
ca3c9c6808805704e84e379a3293093a2d6a6e5b byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Liquidation accounting and separate asset ledgers

[Release v0.5.71](../docs/release-v0.5.71.en.md) · [Detailed contract](01_defi/DeFiLendingLiquidationAccounting.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 173 |
| Lean files under Verification/ | 213 top-level + 2 auxiliary = 215 |
| Root-inclusive sources identical to the reference snapshot | 216 |
| Clean strict build | 3854 jobs; no warnings |
| Complete verifier audit | 24948 declarations; no violations |
| Pinned independent full audit | 24948 declarations; no violations |
| Public live tests | 118; no failures or skips; 349.196s |
| New kernel regression declarations | 46 |
| New executable scenarios | 31 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 216 proof sources match reference snapshot
6866e694d899fc8ab0945b0af7c9a8ea45e93709 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Trace distance and measurement contraction

[Release v0.5.70](../docs/release-v0.5.70.en.md) · [Detailed contract](03_quantum_information/QuantumChannelTraceDistanceContract.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 172 |
| Lean files under Verification/ | 212 top-level + 2 auxiliary = 214 |
| Root-inclusive sources identical to the reference snapshot | 215 |
| Clean strict build | 3853 jobs; no warnings |
| Complete verifier audit | 24705 declarations; no violations |
| Pinned independent full audit | 24705 declarations; no violations |
| Public live tests | 117; no failures or skips; 341.307s |
| New kernel regression declarations | 36 |
| New numeric runtime scenarios | 0 (analytic Lean definitions) |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 215 proof sources match reference snapshot
6cb4f3eaf0b95aff626de9e827338c0fa1986292 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Holevo–Helstrom state discrimination

[Release v0.5.69](../docs/release-v0.5.69.en.md) · [Detailed contract](03_quantum_information/QuantumHelstromStateDiscrimination.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 171 |
| Lean files under Verification/ | 211 top-level + 2 auxiliary = 213 |
| Root-inclusive sources identical to the reference snapshot | 214 |
| Clean strict build | 3852 jobs; no warnings |
| Complete verifier audit | 24623 declarations; no violations |
| Pinned independent full audit | 24623 declarations; no violations |
| Public live tests | 116; no failures or skips; 339.56s |
| New kernel regression declarations | 36 |
| New numeric runtime scenarios | 0 (analytic Lean definitions) |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 214 proof sources match reference snapshot
1f8a4af621a3b875f94773036eea2412294fe517 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Recursive IPA tree extraction

[Release v0.5.68](../docs/release-v0.5.68.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsTreeExtraction.md)

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


## Historical public snapshot: Local Bulletproofs witness extraction

[Release v0.5.67](../docs/release-v0.5.67.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsWitnessExtraction.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 169 |
| Lean files under Verification/ | 209 top-level + 2 auxiliary = 211 |
| Root-inclusive sources identical to the reference snapshot | 212 |
| Clean strict build | 3850 jobs; no warnings |
| Complete verifier audit | 24130 declarations; no violations |
| Pinned independent full audit | 24130 declarations; no violations |
| Public live tests | 114; no failures or skips; 334.96s |
| New kernel regression declarations | 30 |
| New executable scenarios | 28 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 212 proof sources match reference snapshot
c1171d85423c81d3d6dd6eaa8b040c9c817813ac byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Debt-index accrual and rounding reconciliation

[Release v0.5.66](../docs/release-v0.5.66.en.md) · [Detailed contract](01_defi/DeFiLendingCompoundInterestIndex.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 168 |
| Lean files under Verification/ | 208 top-level + 2 auxiliary = 210 |
| Root-inclusive sources identical to the reference snapshot | 211 |
| Clean strict build | 3849 jobs; no warnings |
| Complete verifier audit | 23912 declarations; no violations |
| Pinned independent full audit | 23912 declarations; no violations |
| Public live tests | 113; no failures or skips; 328.465s |
| New kernel regression declarations | 48 |
| New executable scenarios | 30 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 211 proof sources match reference snapshot
530d758583c27e9ed8ef3b6bd2f5298c28ed20d0 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Kinked utilization rates and rounding

[Release v0.5.65](../docs/release-v0.5.65.en.md) · [Detailed contract](01_defi/DeFiKinkedInterestRateUtilization.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 167 |
| Lean files under Verification/ | 207 top-level + 2 auxiliary = 209 |
| Root-inclusive sources identical to the reference snapshot | 210 |
| Clean strict build | 3848 jobs; no warnings |
| Complete verifier audit | 23749 declarations; no violations |
| Pinned independent full audit | 23749 declarations; no violations |
| Public live tests | 112; no failures or skips; 332.383s |
| New kernel regression declarations | 46 |
| New executable scenarios | 25 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 210 proof sources match reference snapshot
4b9e1579c5decc412d4d0ec48ca90e7726f85d08 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Classical POVM data processing

[Release v0.5.64](../docs/release-v0.5.64.en.md) · [Detailed contract](03_quantum_information/QuantumChannelClassicalDataProcessing.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 166 |
| Lean files under Verification/ | 206 top-level + 2 auxiliary = 208 |
| Root-inclusive sources identical to the reference snapshot | 209 |
| Clean strict build | 3846 jobs; no warnings |
| Complete verifier audit | 23587 declarations; no violations |
| Pinned independent full audit | 23587 declarations; no violations |
| Public live tests | 111; no failures or skips; 332.792s |
| New kernel regression declarations | 47 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 209 proof sources match reference snapshot
7eba45c43eebcbe04f7216ae03b94a27cd8d3c0c byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Weighted Tendermint core safety

[Release v0.5.63](../docs/release-v0.5.63.en.md) · [Detailed contract](05_distributed_systems/DistributedTendermintCoreSafety.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 165 |
| Lean files under Verification/ | 205 top-level + 2 auxiliary = 207 |
| Root-inclusive sources identical to the reference snapshot | 208 |
| Clean strict build | 3845 jobs; no warnings |
| Complete verifier audit | 23432 declarations; no violations |
| Pinned independent full audit | 23432 declarations; no violations |
| Public live tests | 110; no failures or skips; 331.279s |
| New kernel regression declarations / compiled scenarios | 49 / 29 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 208 proof sources match reference snapshot
19bd8e16701d694a7def70d8967d1b017ecc7a57 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Lending liquidation health factor

[Release v0.5.62](../docs/release-v0.5.62.en.md) · [Detailed contract](01_defi/DeFiLendingLiquidationHealthFactor.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 164 |
| Lean files under Verification/ | 204 top-level + 2 auxiliary = 206 |
| Root-inclusive sources identical to the reference snapshot | 207 |
| Clean strict build | 3844 jobs; no warnings |
| Complete verifier audit | 22993 declarations; no violations |
| Pinned independent full audit | 22993 declarations; no violations |
| Public live tests | 109; no failures or skips; 329.622s |
| New kernel regression examples / compiled scenarios | 48 / 30 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 207 proof sources match reference snapshot
dde32ddfddd35b3093481ee95a6627383ee1a9c2 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Bulletproofs multi-range aggregation

[Release v0.5.61](../docs/release-v0.5.61.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsAggregation.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 163 |
| Lean files under Verification/ | 203 top-level + 2 auxiliary = 205 |
| Root-inclusive sources identical to the reference snapshot | 206 |
| Clean strict build | 3843 jobs; no warnings |
| Complete verifier audit | 22780 declarations; no violations |
| Pinned independent full audit | 22780 declarations; no violations |
| Public live tests | 108; no failures or skips; 320.972s |
| New kernel regression examples / compiled scenarios | 35 / 38 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 206 proof sources match reference snapshot
e74d187fb7c0fe986ec7fd15af5bd6591f372736 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: POVM entropic uncertainty

[Release v0.5.60](../docs/release-v0.5.60.en.md) · [Detailed contract](03_quantum_information/QuantumPOVMInformationEntropy.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 162 |
| Lean files under Verification/ | 202 top-level + 2 auxiliary = 204 |
| Root-inclusive sources identical to the reference snapshot | 205 |
| Clean strict build | 3842 jobs; no warnings |
| Complete verifier audit | 22607 declarations; no violations |
| Pinned independent full audit | 22607 declarations; no violations |
| Public live tests | 107; no failures or skips; 317.111s |
| New kernel regression examples | 30 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 205 proof sources match reference snapshot
22f869e47aa9b9d9703bee7520b3798e693f6b15 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Constant product with virtual reserves

[Release v0.5.59](../docs/release-v0.5.59.en.md) · [Detailed contract](01_defi/DeFiConstantProductVirtualReserves.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 161 |
| Lean files under Verification/ | 201 top-level + 2 auxiliary = 203 |
| Root-inclusive sources identical to the reference snapshot | 204 |
| Clean strict build | 3768 jobs; no warnings |
| Complete verifier audit | 22437 declarations; no violations |
| Pinned independent full audit | 22437 declarations; no violations |
| Public live tests | 106; no failures or skips; 314.197s |
| New kernel examples / compiled execution cases | 24 / 25 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 204 proof sources match reference snapshot
59ec88ee2ce6cf6f9ff5a51a586fc067dabef630 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Bulletproofs batch verification

[Release v0.5.58](../docs/release-v0.5.58.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsBatchVerification.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 160 |
| Lean files under Verification/ | 200 top-level + 2 auxiliary = 202 |
| Root-inclusive sources identical to the reference snapshot | 203 |
| Clean strict build | 3767 jobs; no warnings |
| Complete verifier audit | 22183 declarations; no violations |
| Pinned independent full audit | 22183 declarations; no violations |
| Public live tests | 105; no failures or skips; 330.075s |
| New kernel examples / compiled execution cases | 18 / 18 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 203 proof sources match reference snapshot
3ae1fc1bffa43c957cdabaf661e375f4f99580b4 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Bulletproofs algebraic range reduction

[Release v0.5.57](../docs/release-v0.5.57.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsRangeReduction.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 159 |
| Lean files under Verification/ | 199 top-level + 2 auxiliary = 201 |
| Root-inclusive sources identical to the reference snapshot | 202 |
| Clean strict build | 3766 jobs; no warnings |
| Complete verifier audit | 22043 declarations; no violations |
| Pinned independent full audit | 22043 declarations; no violations |
| Public live tests | 104; no failures or skips; 317.987s |
| New kernel examples / compiled execution cases | 19 / 13 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 202 proof sources match reference snapshot
76d180a7bac74db68d58218a3df9e4a780d528d1 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Bulletproofs inner product algebra

[Release v0.5.56](../docs/release-v0.5.56.en.md) · [Detailed contract](04_cryptography/CryptoBulletproofsInnerProduct.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 158 |
| Lean files under Verification/ | 198 top-level + 2 auxiliary = 200 |
| Root-inclusive sources identical to the reference snapshot | 201 |
| Clean strict build | 3765 jobs; no warnings |
| Complete verifier audit | 21912 declarations; no violations |
| Pinned independent full audit | 21912 declarations; no violations |
| Public live tests | 103; no failures or skips; 309.775s |
| New IPA kernel examples / compiled execution cases | 22 / 12 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 201 proof sources match reference snapshot
620e2e03d62506f6a231a33c8dc044b31cebd800 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Stable Marzullo event merge sorting

[Release v0.5.55](../docs/release-v0.5.55.en.md) · [Detailed contract](09_distributed_systems/DistributedMarzulloEventSorting.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 157 |
| Lean files under Verification/ | 197 top-level + 2 auxiliary = 199 |
| Root-inclusive sources identical to the private snapshot | 200 |
| Clean strict build | 3764 jobs; no warnings |
| Complete verifier audit | 21722 declarations; no violations |
| Pinned independent full audit | 21722 declarations; no violations |
| Public live tests | 102; no failures or skips; 315.374s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 200 proof sources match private snapshot
9985f49dc6de270dd89656baa41a386aae9fc6da byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Linear interactive Pedersen range proofs

[Release v0.5.54](../docs/release-v0.5.54.en.md) · [Detailed contract](04_cryptography/CryptoPedersenRangeProofLinear.md)

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


## Historical public snapshot: Discrete concentrated-liquidity reference arithmetic

[Release v0.5.53](../docs/release-v0.5.53.en.md) · [Detailed contract](01_defi/DeFiConcentratedLiquidityMath.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 155 |
| Lean files under Verification/ | 195 top-level + 2 auxiliary = 197 |
| Root-inclusive sources identical to the private snapshot | 198 |
| Clean strict build | 3762 jobs; no warnings |
| Complete verifier audit | 21365 declarations; no violations |
| Pinned independent full audit | 21365 declarations; no violations |
| Public live tests | 100; no failures or skips; 302.383s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 198 proof sources match private snapshot
2d3259bc8d8aba61a10eae2c8865b699fd5733ae byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: Executable Marzullo interval consensus

[Release v0.5.52](../docs/release-v0.5.52.en.md) · [Detailed contract](09_distributed_systems/DistributedMarzulloIntervalConsensus.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 154 |
| Lean files under Verification/ | 194 top-level + 2 auxiliary = 196 |
| Root-inclusive sources identical to the private snapshot | 197 |
| Clean strict build | 3761 jobs; no warnings |
| Complete verifier audit | 21023 declarations; no violations |
| Pinned independent full audit | 21023 declarations; no violations |
| Public live tests | 99; no failures or skips; 313.507s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 197 proof sources match private snapshot
13f6cabe79f9c25da016489c0777fc4c8a89abb6 byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


## Historical public snapshot: IC-POVM exact tomography

[Release v0.5.51](../docs/release-v0.5.51.en.md) · [Detailed contract](03_quantum/QuantumPOVMInformationallyComplete.md)

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 153 |
| Lean files under Verification/ | 193 top-level + 2 auxiliary = 195 |
| Root-inclusive sources identical to the private snapshot | 196 |
| Clean strict build | 3759 jobs; no warnings |
| Complete verifier audit | 20765 declarations; no violations |
| Pinned independent full audit | 20765 declarations; no violations |
| Public live tests | 98; no failures or skips; 309.983s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 196 proof sources match private snapshot
f6730717e96191a569c840a45b1b3ff2ba1bdb9f byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```


[Knowledge base](README.md) · [Release v0.5.50](../docs/release-v0.5.50.en.md)

## Historical public snapshot: Mixed-state no-broadcasting

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 152 |
| Lean files under Verification/ | 192 top-level + 2 auxiliary = 194 |
| Root-inclusive sources identical to the private snapshot | 195 |
| Clean strict build | 3752 jobs; no warnings |
| Complete verifier audit | 20622 declarations; no violations |
| Pinned independent full audit | 20622 declarations; no violations |
| Public live tests | 97; no failures or skips; 308.562s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. Integration is idempotent. All 195 proof sources
match private snapshot afab7ff359d805188950bb8a073c33f63dcb3b72 byte-for-byte.
Russian cards are not exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

[Detailed contract](03_quantum/QuantumNoBroadcastingMixed.md) · [Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.49](../docs/release-v0.5.49.en.md)

## Historical public snapshot v0.5.49: FROST threshold Schnorr signatures

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 151 |
| Lean files under Verification/ | 191 top-level + 2 auxiliary = 193 |
| Root-inclusive sources identical to the private snapshot | 194 |
| Clean strict build | 3742 jobs; no warnings |
| Complete verifier audit | 20451 declarations; no violations |
| Pinned independent full audit | 20451 declarations; no violations |
| Public live tests | 96; no failures or skips; 302.683s |

All 194 proof sources match private snapshot `2e3aa42501d148f324dd9e1d88803fcf94710938`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.48](../docs/release-v0.5.48.en.md)

## Historical public snapshot v0.5.48: Raft joint-consensus reconfiguration

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 150 |
| Lean files under Verification/ | 190 top-level + 2 auxiliary = 192 |
| Root-inclusive sources identical to the private snapshot | 193 |
| Clean strict build | 3741 jobs; no warnings |
| Complete verifier audit | 20338 declarations; no violations |
| Pinned independent full audit | 20338 declarations; no violations |
| Public live tests | 95; no failures or skips; 303.516s |

All 193 proof sources match private snapshot `6c11fa68d512262675d779ef4568e3782caa9f43`.

This release proves safety for one arbitrary fixed transition from stable-old
through joint-old-new to stable-new, with commands, leader changes and delayed,
duplicated or reordered messages. Configurations activate from the latest local
log entry before commitment and roll back deterministically on suffix removal.

Reachability implies historical commit-index soundness, committed-prefix
preservation, Election Safety in every term, Log Matching and Leader Completeness.
Old and new stable quorums may be disjoint; incompatible successful elections are
excluded by the historical joint-commit barrier, not by assuming they intersect.
The regressions include a reachable disjoint handover, leader retirement and
rollback after a leader change. The direct-switch counterexample is an algebraic
split-vote construction, not a separate unsafe protocol execution.

Unbounded reconfiguration chains, snapshots, Byzantine faults, crash/recovery
and liveness are outside scope. The static Raft bridge concerns local command-only
log merging, not a full simulation. Python, JSON/SHA-256 and SimLab obligations
remain open; running the test harness does not verify a Python Raft implementation.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.47](../docs/release-v0.5.47.en.md)

## Historical public snapshot v0.5.47: Finite-field Shamir sharing

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 149 |
| Lean files under Verification/ | 189 top-level + 2 auxiliary = 191 |
| Root-inclusive sources identical to the private snapshot | 192 |
| Clean strict build | 3740 jobs; no warnings |
| Complete verifier audit | 19077 declarations; no violations |
| Pinned independent full audit | 19077 declarations; no violations |
| Public live tests | 94; no failures or skips; 297.242s |

All 192 proof sources match private snapshot `2ad7e5e834573c88722a35a8ad2c47dbf971e302`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.46](../docs/release-v0.5.46.en.md)

## Historical public snapshot v0.5.46: Vector Pedersen commitments

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 148 |
| Lean files under Verification/ | 188 top-level + 2 auxiliary = 190 |
| Root-inclusive sources identical to the private snapshot | 191 |
| Clean strict build | 3738 jobs; no warnings |
| Complete verifier audit | 18990 declarations; no violations |
| Pinned independent full audit | 18990 declarations; no violations |
| Public live tests | 93; no failures or skips; 290.036s |

All 191 proof sources match private snapshot `3f3dc24abfe6d9b6a44069e88f3abd5f49aaa8ed`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.45](../docs/release-v0.5.45.en.md)

## Historical public snapshot v0.5.45: Group ElGamal weighted homomorphism

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 147 |
| Lean files under Verification/ | 187 top-level + 2 auxiliary = 189 |
| Root-inclusive sources identical to the private snapshot | 190 |
| Clean strict build | 3737 jobs; no warnings |
| Complete verifier audit | 18916 declarations; no violations |
| Pinned independent full audit | 18916 declarations; no violations |
| Public live tests | 92; no failures or skips; 287.423s |

All 190 proof sources match private snapshot `3dded0e143eb6064cfccaf8e823147e19c3d4b08`.

Group and exponential ElGamal decryption correctness, uniqueness of the scalar
preimage, and homomorphism of arbitrary finite weighted sums under one public key
are proved over cyclic groups of prime order q. Algebraic rerandomization adds an
encryption of zero. A public ciphertext shift changes the decrypted point by a
provably nonzero amount for a nonzero scalar shift. A concrete ZMod q model
witnesses the assumptions; a general algebraic identity has separate real and
modular specializations linking the earlier scalar model.

Decryption returns the group point m • G. Uniqueness of m does not supply an
efficient discrete-logarithm decoder. Weighted scalar sums are modulo q; interpreting
them as integer totals requires separate range bounds. Rerandomization is an
algebraic identity, with no probability-distribution claim.

IND-CPA/IND-CCA security proofs, DDH reductions, efficient discrete-logarithm
algorithms, concrete elliptic curves and serialization are not modeled.
Python, JSON/SHA-256 and SimLab obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.44](../docs/release-v0.5.44.en.md)

## Historical public snapshot v0.5.44: BLS aggregation in bilinear groups

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 146 |
| Lean files under Verification/ | 186 top-level + 2 auxiliary = 188 |
| Root-inclusive sources identical to the private snapshot | 189 |
| Clean strict build | 3736 jobs; no warnings |
| Complete verifier audit | 18858 declarations; no violations |
| Pinned independent full audit | 18858 declarations; no violations |
| Public live tests | 91; no failures or skips; 294.911s |

All 189 proof sources match private snapshot `d450b5712764642fbecf436870d0a1f713270819`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.43](../docs/release-v0.5.43.en.md)

## Historical public snapshot v0.5.43: Signed Byzantine broadcast

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 145 |
| Lean files under Verification/ | 185 top-level + 2 auxiliary = 187 |
| Root-inclusive sources identical to the private snapshot | 188 |
| Clean strict build | 3735 jobs; no warnings |
| Complete verifier audit | 18776 declarations; no violations |
| Pinned independent full audit | 18776 declarations; no violations |
| Public live tests | 90; no failures or skips; 291.801s |

All 188 proof sources match private snapshot `2b03b38cacf29b0ad2cc386316aeb7ddb1c1fd0e`.

The module proves Agreement and CommanderValidity for a deterministic,
synchronous signed-chain broadcast protocol with n >= f + 2 nodes, a static
fault set of size at most f, and decisions after exactly f + 1 rounds.
The guarantee concerns honest lieutenants; the commander is excluded from
lieutenant-view equality. The population restriction guarantees at least two
honest nodes, not necessarily two honest lieutenants when the commander is honest.

Ideal signatures are modeled by an inductive derivation environment backed by
an operational issuance ledger. Honest signature occurrences require previously
issued matching prefixes. Their actual signing transitions and receipt rounds
are proved from executions; the honest commander signs its input initially.
Delivery assumes reliable honest transmission and derivable signatures, without
assuming propagation or agreement. Acceptance checks the commander root, distinct
signers and a chain length equal to the current round. Honest views accumulate
monotonically. Propagation and a pigeonhole argument for f + 1 distinct signers
imply equal final views. An honest commander's final views are its singleton order.
Reachable nonterminal states can advance and completed executions exist.

Regressions include n = 3, f = 1, contradictory orders, silence, an honest
commander, malformed chains and a valid late short-chain attack when the final
round-length filter is removed. A formal bridge contrasts the result with the
three-node oral-message impossibility theorem. This is an explicit round-indexed
signed-chain implementation, not a claim about every optimization of SM(f).

The cryptographic environment is idealized. Computational properties of concrete
signature schemes such as RSA/ECDSA, byte serialization, asynchronous channels,
dynamic faults and optimal message complexity are outside scope. Python,
JSON/SHA-256 and SimLab obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.42](../docs/release-v0.5.42.en.md)

## Historical public snapshot v0.5.42: Three-generals oral Byzantine broadcast

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 144 |
| Lean files under Verification/ | 184 top-level + 2 auxiliary = 186 |
| Root-inclusive sources identical to the private snapshot | 187 |
| Clean strict build | 3734 jobs; no warnings |
| Complete verifier audit | 18521 declarations; no violations |
| Pinned independent full audit | 18521 declarations; no violations |
| Public live tests | 89; no failures or skips; 288.517s |

All 187 proof sources match private snapshot `b16060ad3d32182d2dc14394bc1fccaf8dfc1399`.

The module proves impossibility of deterministic Byzantine broadcast for exactly
three processes and at most one static Byzantine identity in synchronous oral
messages (OM). Honest messages are delivered reliably with immediate sender
identities; the faulty node may send arbitrary recipient-specific messages or
remain silent. Only the commander initially receives the binary order.

A joint recursion maintains two honest commander copies and two shared lieutenants.
Three admissible executions are constructed from their earlier states. Induction
on rounds proves equality of the honest lieutenants' local histories; CommanderValidity
forces conflicting decisions when the commander is faulty, contradicting Agreement.
This holds for every fixed finite horizon T, including zero. Constant retreat,
naive direct-command following and all-honest executions are covered by regressions.

The general n <= 3f lower bound, signed messages (SM), randomized consensus and
termination without a common finite bound are outside scope. The result is not
an asynchronous crash-failure FLP theorem. Python, JSON/SHA-256 and SimLab
obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.41](../docs/release-v0.5.41.en.md)

## Historical public snapshot v0.5.41: Finite-group Schnorr aggregation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 143 |
| Lean files under Verification/ | 183 top-level + 2 auxiliary = 185 |
| Root-inclusive sources identical to the private snapshot | 186 |
| Clean strict build | 3733 jobs; no warnings |
| Complete verifier audit | 18362 declarations; no violations |
| Pinned independent full audit | 18362 declarations; no violations |
| Public live tests | 88; no failures or skips; 290.769s |

All 186 proof sources match private snapshot `0744cfdef0c8cc1529eab2c5006dd47ffb678d27`.

Scalars are ZMod q for a prime q. CyclicSetup supplies an additive commutative
group, a compatible module action and a generator G with bijective map x ↦ x • G.
This gives a cyclic group of order q; no efficient discrete-log inverse or hardness
claim is supplied. An ordered Fin n key vector preserves duplicates. The honest
main theorem assumes n >= 2; auxiliary module identities hold more generally.

Two separately typed deterministic functions supply a_i = H_agg L (L i) and
c = H_sig X_agg R_agg m. Honest partials satisfy
s_i • G = R_i + (c * a_i) • X_i. Their sum satisfies aggregate verification.
A separate theorem assembles any accepted partial equations with a common
challenge and coefficients; it does not prove knowledge of the secret keys.
The requested theorem name containing soundness denotes algebraic completeness.

For naive two-key addition, bad = z • G - honest makes the aggregate z • G.
The response r + c * z verifies against nonce r • G using only the honest public
key and the selected scalars z and r. This is a witness against naive aggregation,
not an attack on correctly instantiated MuSig. Regressions include two signers
over ZMod 7, duplicate keys, zero weights and aggregate-key cancellation.
A zero coefficient removes a fixed term; changing the key vector can rehash
other coefficients. Degenerate-key rejection is not implemented.

The scalar bridge specializes a common commutative-ring identity independently
to the existing real two-nonce definitions and to ZMod q scalar action. There is
no asserted map from arbitrary real scalars to the finite field, and two nonce
variables do not model interactive rounds.

This release proves algebraic correctness only. AGM/ROM reductions, hashed-key
rogue-key resistance, nonce generation and non-reuse, concurrent-session security,
interactive MuSig2/BIP327, curve implementation and byte serialization are outside
scope. The two function interfaces do not prove cryptographic domain separation.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.40](../docs/release-v0.5.40.en.md)

## Historical public snapshot v0.5.40: Coordinated attack impossibility

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 142 |
| Lean files under Verification/ | 182 top-level + 2 auxiliary = 184 |
| Root-inclusive sources identical to the private snapshot | 185 |
| Clean strict build | 3732 jobs; no warnings |
| Complete verifier audit | 18279 declarations; no violations |
| Pinned independent full audit | 18279 declarations; no violations |
| Public live tests | 87; no failures or skips; 276.094s |

All 185 proof sources match private snapshot `516c0748a91a7c5c222d76759b24ae3781886d1d`.

The model has two correct deterministic processes, private binary inputs,
arbitrary message and local-state types, and a fixed finite round horizon T.
Sends depend on pre-round states. Incoming messages can independently be lost;
there is no sender-visible delivery feedback. Self-delivery flags are ignored.

Removing one outgoing delivery preserves the sender's next local state. If no
later messages are delivered, it preserves that sender's entire remaining local
history. These facts are derived from execution, not assumed as external axioms.
Under Agreement, removal preserves the common decision. Strong induction on the
number of actual cross-process deliveries reduces any schedule to total loss.
With total loss, each local state depends only on its own input. Changing the
two private inputs one at a time therefore preserves the common decision.

For every fixed finite T, Agreement and ValidityZero force retreat for all inputs
and schedules, contradicting ReliableSuccess. The impossibility concerns these
three properties together; Agreement alone is not impossible. Regressions cover
T = 0, an always-retreat protocol, commuting removals, and a concrete two-round
request/ack exchange whose lost acknowledgement causes disagreement. A protocol
satisfying Agreement and ValidityZero must retreat on that same schedule.

This is a synchronous lossy-channel result, distinct from FLP. No theorem about
unbounded stopping times or eventual termination without a uniform finite bound
is asserted. Randomized epsilon-agreement, quantum channels and Byzantine
behavior are outside scope. Python, JSON/SHA-256 and SimLab obligations remain
open. No novelty claim is made.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.39](../docs/release-v0.5.39.en.md)

## Historical public snapshot v0.5.39: Exact unitary no-cloning

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 141 |
| Lean files under Verification/ | 181 top-level + 2 auxiliary = 183 |
| Root-inclusive sources identical to the private snapshot | 184 |
| Clean strict build | 3731 jobs; no warnings |
| Complete verifier audit | 18166 declarations; no violations |
| Pinned independent full audit | 18166 declarations; no violations |
| Public live tests | 86; no failures or skips; 289.434s |

All 184 proof sources match private snapshot `845ef3d56ad066f0b3896d917e3ebf90e9f7367c`.

Unitary evolution and tensor factorization imply c=c^2 for exact vector cloning
and t=t^2 for pure-density cloning, where t is the squared overlap. For normalized
inputs this proves a necessary condition: orthogonality or equality of the pure
density matrices. The general sufficiency theorem for an arbitrary orthogonal
pair is not asserted. Global phase invariance is proved for density matrices;
literal cloning of both psi and -psi is impossible.

An explicit unitary CNOT copies the computational basis, but sends |+>|0> to a
Bell state proved unequal to every product vector. A unitary cloner exists for
one prescribed normalized state and blank by isometry extension. This existence
proof is noncomputable and does not synthesize a circuit.

The squared overlap of |0> and |+> is 1/2 in every dimension at least two. No common
unitary and fixed normalized blank can clone both densities, hence no universal
cloner exists. Bridges derive the scalar module's quadratic premise and rule out
joint cloning of the actual four BB84 states.

The scope is exact deterministic square-unitary cloning of pure states on two
systems. General CPTP maps with discarded environments, mixed-state
no-broadcasting, probabilistic or approximate cloners and physical QKD security
are outside scope. Python, JSON/SHA-256 and SimLab obligations remain open.
Scientific novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.38](../docs/release-v0.5.38.en.md)

## Historical public snapshot v0.5.38: Finite Naimark dilation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 140 |
| Lean files under Verification/ | 180 top-level + 2 auxiliary = 182 |
| Root-inclusive sources identical to the private snapshot | 183 |
| Clean strict build | 3730 jobs; no warnings |
| Complete verifier audit | 18067 declarations; no violations |
| Pinned independent full audit | 18067 declarations; no violations |
| Public live tests | 85; no failures or skips; 279.862s |

All 183 proof sources match private snapshot `5cfecd3773d40cc2ceca22686e0976416b3df834`.

For any finite POVM of positive semidefinite complex matrices whose sum is I,
Mathlib CFC.sqrt supplies positive Hermitian roots F_m. The explicit block
isometry V and orthogonal projectors Pi_m satisfy V†V=I and V†Pi_m V=E_m.
Born traces agree for arbitrary complex input matrices. Density matrices lift
to density matrices, and outcome probabilities are real, nonnegative and normalized.

For a nonempty ancilla, a unitary extension U with UJ=V exists for the fixed
pure ancilla |0>. Partial trace of each projected branch gives the unnormalized
Lueders update F_m rho F_m. The singleton Kraus families {I} and {X} demonstrate
that identical POVM effects need not induce identical state updates. Bridges
instantiate the Bell analyzer's three effects and the depolarizing channel's
Kraus effects; the latter matches branch probabilities, not the full state update.

These are noncomputable mathematical constructions, not executable square-root
algorithms or quantum circuit synthesis. Born's rule supplies the physical model.
The theorem concerns finite-dimensional systems and finite outcome sets.
Infinite-dimensional spaces, spectral measures, minimality, gate synthesis and
hardware implementation are outside scope. Python, JSON/SHA-256 and SimLab
obligations remain open. Scientific novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.37](../docs/release-v0.5.37.en.md)

## Historical public snapshot v0.5.37: Qubit depolarization

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 139 |
| Lean files under Verification/ | 179 top-level + 2 auxiliary = 181 |
| Root-inclusive sources identical to the private snapshot | 182 |
| Clean strict build | 3729 jobs; no warnings |
| Complete verifier audit | 17940 declarations; no violations |
| Pinned independent full audit | 17940 declarations; no violations |
| Public live tests | 84; no failures or skips; 281.541s |

All 182 proof sources match private snapshot `09e41d2eca4d4b88ac8c779d8b7d60622b51aaa3`.

The Kraus-defined qubit depolarizing channel is trace preserving for p in [0,1]
and completely positive for every finite ancilla dimension. Its exact linear form
is D_p(M)=(1-4p/3) M+(2p/3) Tr(M) I for arbitrary complex matrices.
The Bloch vector scales by lambda=1-4p/3 and its length by |lambda|, including
negative lambda when p>3/4. Complete depolarization occurs at p=3/4.
Composition has parameter p+q-4pq/3, which remains in [0,1].

Acting on Bob's half of the E91 singlet yields lambda rho_minus+(1-lambda) I_4/4.
The actual Born probabilities give S(p)=-2 sqrt(2) lambda and key QBER=2p/3.
Regressions include endpoint channels, pure input states and a malformed affine
formula without the trace factor, which maps zero to a nonzero matrix.

The CHSH violation threshold is not a secret-key threshold. Quantum capacity,
optimal coding, error-correction protocols, DI-QKD and finite-key effects are not
modeled. The ideal E91 source, measurements and authenticated classical channel
retain their existing assumptions. Python, JSON/SHA-256 and SimLab obligations
remain open. Scientific novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.36](../docs/release-v0.5.36.en.md)

## Historical public snapshot v0.5.36: Born-derived E91

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 138 |
| Lean files under Verification/ | 178 top-level + 2 auxiliary = 180 |
| Root-inclusive sources identical to the private snapshot | 181 |
| Clean strict build | 3728 jobs; no warnings |
| Complete verifier audit | 17806 declarations; no violations |
| Pinned independent full audit | 17806 declarations; no violations |
| Public live tests | 83; no failures or skips; 279.434s |

All 181 proof sources match private snapshot `1816caf49a2eee5ccc791a388fb28b1a83bb1da2`.

The model defines the singlet density matrix and dichotomic XZ observables.
Born probabilities are computed from projector tensor products, with reality,
nonnegativity, normalization and uniform local marginals proved. All nine E91
correlators are derived. The specified settings attain S = -2 sqrt(2), with
|S| = 2 sqrt(2) > 2. Key pairs (2,1) and (3,2) are perfectly anticorrelated;
Bob's bit inversion yields agreement and ideal zero QBER. Independent uniform
settings give key/test/discard probabilities 2/9, 4/9 and 1/3.

The classical CHSH bound covers finite local hidden-variable laws using the same
law for all settings, and finite convex mixtures of products of physical qubit
density matrices. The explicit intercept/resend channel acts on the supplied
singlet: Eve measures Alice's half in any real unit XZ direction and prepares an
arbitrary valid outcome-dependent qubit. Partial-trace calculation gives a
separable result with trace one and |S| <= 2. Arbitrary inputs, general POVMs or
all attack models are not covered by this instrument theorem.

The Born rule is a physical modeling postulate; its algebraic consequences are
proved. Attaining 2 sqrt(2) is not a universal operator Tsirelson upper-bound proof.
Device-independent QKD security, final-key secrecy, finite-key statistics or
guaranteed finite-sample detection, error reconciliation, privacy amplification,
and detection loopholes are outside scope. The singlet source, measurements,
independent settings and authenticated classical channel are idealized.
Python, JSON/SHA-256 and SimLab obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.35](../docs/release-v0.5.35.en.md)

## Historical public snapshot v0.5.35: Operational Multi-Paxos

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 137 |
| Lean files under Verification/ | 177 top-level + 2 auxiliary = 179 |
| Root-inclusive sources identical to the private snapshot | 180 |
| Clean strict build | 3727 jobs; no warnings |
| Complete verifier audit | 17615 declarations; no violations |
| Pinned independent full audit | 17615 declarations; no violations |
| Public live tests | 82; no failures or skips; 278.315s |

All 180 proof sources match private snapshot `c3a0f1586f2d4271fd1bb0ff3d1a22261341b235`.

The operational Multi-Paxos model derives promise monotonicity, uniqueness of proposals per (ballot, slot), preservation of chosen values across ballots, slot Agreement and comparability of executed log prefixes. A phase-one certificate is reused across multiple slots. SingleVote is derived for the older model, not assumed as an external hypothesis. Chosen records historical votes; proposals use write-once storage. Concrete faulty traces show disagreement when maximum-ballot selection or ballot ownership with write-once proposals is weakened.

Safety covers an ideal static, non-Byzantine asynchronous network with arbitrary delays, reordering and duplicates; the model also permits message loss. No liveness or FLP theorem is proved. FLP motivates separating safety from progress: a future progress contract needs a stable leader, an available quorum, suitable delivery/retransmission and scheduling fairness. A stable leader alone does not guarantee termination.

Reconfiguration, checkpoints, log compaction, recovery after loss of durable state and Byzantine attacks are outside scope. Linearizability, client deduplication and exactly-once effects are not proved. Python, JSON/SHA-256 and SimLab correctness obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.34](../docs/release-v0.5.34.en.md)

## Historical public snapshot v0.5.34: Born-derived BB84 QBER

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 136 |
| Lean files under Verification/ | 176 top-level + 2 auxiliary = 178 |
| Root-inclusive sources identical to the private snapshot | 179 |
| Clean strict build | 3726 jobs; no warnings |
| Complete verifier audit | 17081 declarations; no violations |
| Pinned independent full audit | 17081 declarations; no violations |
| Public live tests | 81; no failures or skips; 277.682s |

All 179 proof sources match private snapshot `2fff8672332796ab463396cdf799e0112e3886eb`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.33](../docs/release-v0.5.33.en.md)

## Historical public snapshot v0.5.33: Optical quantum teleportation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 135 |
| Lean files under Verification/ | 175 top-level + 2 auxiliary = 177 |
| Root-inclusive sources identical to the private snapshot | 178 |
| Clean strict build | 3725 jobs; no warnings |
| Complete verifier audit | 16901 declarations; no violations |
| Pinned independent full audit | 16901 declarations; no violations |
| Public live tests | 80; no failures or skips; 276.334s |

All 178 proof sources match private snapshot `bc6ec6054e308654f2f2b010c66474b12719cc43`.

The module derives an optical quantum instrument on the twenty-dimensional
invariant sector (ten Alice Fock outcomes times two Bob modes). Its ten Kraus
operators come from the existing Bell analyzer and resource embedding; their
completeness is proved. The successful branches are E_minus(rho) = XZ rho (XZ)†/4
and E_plus(rho) = X rho X†/4. Each has probability 1/4 for every density operator,
including mixed inputs; total success is 1/2. Unitary corrections ZX and X give
the successful channel rho/2, so normalization recovers rho with squared Uhlmann
fidelity one. Without Alice's classical record the uncorrected channel is I₂/2.
The physical partial trace and the abstract teleportation protocol are linked.

Regressions include |0>, |1>, |+>, |+i>, the maximally mixed input and trace
preservation. Incorrect correction Z leaves residual -X: |+> is preserved, but
|0> and |+i> have squared fidelity zero. Of the six inconclusive detector outcomes,
four have double occupation and two are dark on the embedded input sector.

The result concerns this conditional passive linear-optical scheme, with a supplied
ideal Phi-plus resource, matching photon wave packets, ideal detector projection
and classical feed-forward. Resource generation, deterministic teleportation,
universal optical discrimination bounds, spectral distinguishability, losses,
dark counts and detector noise are not modeled. Python, JSON/SHA-256 and SimLab
correctness obligations remain open.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.32](../docs/release-v0.5.32.en.md)

## Historical public snapshot v0.5.32: Concrete optical Bell analyzer

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 134 |
| Lean files under Verification/ | 174 top-level + 2 auxiliary = 176 |
| Root-inclusive sources identical to the private snapshot | 177 |
| Clean strict build | 3625 jobs; no warnings |
| Complete verifier audit | 16721 declarations; no violations |
| Pinned independent full audit | 16721 declarations; no violations |
| Public live tests | 79; no failures or skips; 277.483s |

All 177 proof sources match private snapshot `59aa296435696dbe388d0e19a110f81c13e8b578`.

The fixed four-mode passive network uses two imported balanced splitters B(1/2),
one for each polarization, and ideal PBS routing. Polynomial substitution derives
the normalized symmetric lift on all ten two-photon occupations. Both the
one-photon and two-photon scattering matrices are unitary.

The four Bell outputs are computed from this network. Psi-minus gives
opposite-polarization detections in different spatial ports; Psi-plus gives
opposite-polarization detections within one spatial port, separated by the PBS.
Each is unambiguously identified with probability one. Phi-plus and Phi-minus
have identical distributions over all ten Fock outcomes, with probability 1/4
on each of four double-occupation outcomes. Their pure output vectors remain distinct.

Detector POVM effects are derived by compressing the output projectors through
the optical transfer. Their exact Bell-projector forms, completeness,
Hermiticity, positivity and Born identity for arbitrary coherent inputs are proved.
Success equals p(Psi-minus)+p(Psi-plus); it is 1/2 for the uniform four-state
ensemble and 1 for a Psi-only ensemble. Equal Phi distributions remain equal
under classical postprocessing; binary guessing for equal Phi priors succeeds
exactly half the time. No postselection discards detector outcomes.

The assumptions are ideal lossless passive optics, matching temporal/spectral
wave packets, ideal PBS routing and Born detection with photon-number resolution.
This is a concrete finite normalized two-boson model, not an electromagnetic
or detector-hardware derivation. The universal Calsamiglia-Luetkenhaus bound
for arbitrary optical networks, ancilla-assisted or adaptive schemes,
chi(2)/chi(3) nonlinearities, spectral distinguishability, photon loss and dark
counts are outside scope. Python correctness, JSON/SHA-256 correctness and
SimLab correspondence remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.31](../docs/release-v0.5.31.en.md)

## Historical public snapshot v0.5.31: Observed-remove set

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 133 |
| Lean files under Verification/ | 173 top-level + 2 auxiliary = 175 |
| Root-inclusive sources identical to the private snapshot | 176 |
| Clean strict build | 3624 jobs; no warnings |
| Complete verifier audit | 16494 declarations; no violations |
| Pinned independent full audit | 16494 declarations; no violations |
| Public live tests | 78; no failures or skips; 277.247s |

All 176 proof sources match private snapshot `9502d727465b13c7895370b4a6dc3f5000616e38`.

The OR-Set retains finite sets of all added element/tag pairs and removed pairs.
Visibility requires an added tag without a tombstone. Componentwise union gives an
unconditional join semilattice; reachable transitions preserve removed subset added.
Persistent per-replica counters imply unique operation IDs and fresh add tags.
Removal captures its observed live tags once; reception never recomputes that context.

Independent observation causality supports add-wins for a concurrent add/remove pair,
including their complete post-operation snapshots. A later removal that observes the
new tag may remove it. Tombstones prevent resurrection of a fixed removed tag;
a new add restores visibility using a fresh tag. Metadata are monotone; visible
membership is not. Equal included immutable updates, with their captured removal
contexts, imply equal states independently of delivery order and duplicates.

Authentic sent snapshots remain reliably available. Recurring sends and weak fairness
for continuously useful receptions imply eventual dissemination. After updates cease,
all replicas stabilize to the finite global join. The causal-broadcast adapter uses
actual delivery logs and proves convergence for an announced covering finite batch,
including snapshots of a fixed reachable checkpoint. It does not claim a fully coupled
serializer for arbitrary ongoing updates. Full-state union does not need causal order.

Regressions cover empty state, local add/remove/re-add, concurrent add/remove, partial
observation, stale snapshots and duplicates. Counterexamples show suppression by tag
reuse and resurrection after premature tombstone collection followed by a stale snapshot.

Correct tombstone garbage collection, ORSWOT compression, linearizability, dynamic
membership, memory-loss recovery and Byzantine behavior are not modeled. Natural
counters do not overflow; bounded machine counters are outside this model. Python,
JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.30](../docs/release-v0.5.30.en.md)

## Historical public snapshot v0.5.30: State-based LWW register

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 132 |
| Lean files under Verification/ | 172 top-level + 2 auxiliary = 174 |
| Root-inclusive sources identical to the private snapshot | 175 |
| Clean strict build | 3623 jobs; no warnings |
| Complete verifier audit | 16006 declarations; no violations |
| Pinned independent full audit | 16006 declarations; no violations |
| Public live tests | 77; no failures or skips; 271.527s |

All 175 proof sources match private snapshot `fb5b736e7f4794f96e1ee5f61d9b50af7cd8a571`.

The model is a state-based LWW register for a fixed group of replicas. Stamps
are ordered lexicographically by logical counter and replica ID. Operational
freshness proves that equal issued stamps carry equal values. Merge forms a
bounded join semilattice on states compatible with a common valid history;
commutativity is not asserted for malformed conflicting values at one full stamp.

The payload is the maximum of its included update history. Equal included update
sets imply equal payloads, independently of ordering and duplicates. This strong
convergence result is distinct from conditional dissemination. Reliable availability
of authentic immutable snapshots, fair sending and per-useful-snapshot weak
fairness imply eventual information subsumption. After new writes cease, all
replica payloads permanently stabilize to the global maximum.

An incremental adapter replays snapshots along actual DistributedCausalBroadcast
application delivery logs. Its finite-batch and checkpoint theorems derive
saturation from reliable arrival and weak fairness. A coupled serializer and
arbitrary ongoing-write transport implementation are not asserted. Regressions
cover bottom, one replica, concurrent equal counters resolved by ID, stale and
duplicate snapshots, fresh relay writes, and malformed tie/stale-write rules.

Convergence concerns the register value, not clocks or ghost logs. Linearizability,
distributed consensus, preservation of all concurrent versions, physical-clock
or NTP synchronization, crash recovery or recovery after nonvolatile-memory failure,
Byzantine participants and dynamic membership are not modeled. Mathematical natural
counters do not overflow; bounded machine-counter implementations are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.29](../docs/release-v0.5.29.en.md)

## Historical public snapshot v0.5.29: Causal broadcast

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 131 |
| Lean files under Verification/ | 171 top-level + 2 auxiliary = 173 |
| Root-inclusive sources identical to the private snapshot | 174 |
| Clean strict build | 3622 jobs; no warnings |
| Complete verifier audit | 15608 declarations; no violations |
| Pinned independent full audit | 15608 declarations; no violations |
| Public live tests | 76; no failures or skips; 272.330s |

All 174 proof sources match private snapshot `77948161a169a42dee824a8a2e1236e582665be4`.

DistributedCausalBroadcast formalizes fixed-group causal multicast with authentic
immutable messages and delivered-prefix vector counters. Broadcast atomically
self-delivers; Arrive only buffers; Deliver requires the next sender sequence
and every cross-sender dependency. Induction over operational transitions proves
continuous prefixes, at-most-once application delivery, exact reflexive causal-past
timestamps and causal delivery safety: if m1 precedes m2 and m2 is delivered at t,
m1 was delivered at a strictly earlier step. Independent message causality is
linked to actual delivery-before-broadcast events, not defined by vector comparison.

Eventual delivery requires reliable network arrival and per-message weak fairness.
It follows by induction on finite causal pasts; readiness is derived rather than
assumed. Reordered and duplicate network arrivals are allowed. Regressions cover
three-process relay, independent broadcasts, immediate self-delivery, a one-node
group, and counterexamples to weakened cross-sender or next-sequence guards.
Buffered arrival alone does not create an application causal dependency.

Causal order does not imply total order or physical simultaneity. Crashes, restarts,
Byzantine messages, dynamic membership, bounded-machine counter overflow, vector
compression and physical delays are outside this model. Mathematical natural
numbers themselves do not overflow. The full ISIS membership and virtual-synchrony
protocol is not claimed. Python correctness, JSON/SHA-256 correctness and the
SimLab-to-Lean correspondence remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.28](../docs/release-v0.5.28.en.md)

## Historical public snapshot v0.5.28: Postselected photonic controlled-Z

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 130 |
| Lean files under Verification/ | 170 top-level + 2 auxiliary = 172 |
| Root-inclusive sources identical to the private snapshot | 173 |
| Clean strict build | 3621 jobs; no warnings |
| Complete verifier audit | 15177 declarations; no violations |
| Pinned independent full audit | 15177 declarations; no violations |
| Public live tests | 75; no failures or skips; 269.270s |

All 173 proof sources match private snapshot `629e2ceb6441538c0abdf75331db6e1be6f2bcd7`.

The module derives a coincidence-postselected controlled-Z operation from three
disjoint ideal lossless beam splitters. The six modes are a0,a1,b0,b1,va,vb;
the pairs (a0,va), (a1,b1), (b0,vb) use the imported complex B(T), for 0 <= T <= 1.
The normalized two-boson basis enumerates 21 unordered mode pairs. Equal-mode
creation monomials carry the factor 1/sqrt(2). A generic polynomial-substitution
theorem connects the symmetric lift to single-particle scattering. Both the
six-mode network and its 21-dimensional two-photon lift are proved unitary.

The dual-rail encoding J is an isometry. Its orthogonal projection JJ† accepts
exactly one photon in each logical rail pair and none in the auxiliary modes.
The success map is defined by compression K(T)=J†U(T)J; its diagonal
(T,T,T,2T-1) is derived. At T=1/3, K=CZ/3 and K†K=I/9. Every normalized input
has success probability 1/9; the normalized successful branch is CZ psi.
The matrix identity K rho K†=(1/9)CZ rho CZ† holds for every matrix rho,
and the success trace is 1/9 for every trace-one density matrix.

CZ is unitary, Hermitian and involutive. Four Pauli conjugation identities are
proved. The product input |++> becomes the graph state (1,1,1,-1)/2. A local
Hadamard maps this state to the Bell state Phi+. Its global density is pure;
both reduced densities are I2/2 and reduced purity is 1/2. The state is proved
not to factor into two local vectors. A product-state purity theorem supplies
an additional bridge to pure-state separability. A general theory of convex
mixed-state separability is not claimed.

Regressions cover all four basis inputs with success probability 1/9 and signs
(+,+,+,-), T=1/2 with K=diag(1/2,1/2,1/2,0), and T=1 with K=I. At T=1/2,
the |11> input bunches in the central computational modes and fails coincidence
selection; this particular input does not leak into the auxiliary vacuum modes.

This is a finite homogeneous-polynomial model of ideal indistinguishable bosons,
not an infinite Fock-space or canonical-commutation-relation construction.
Born-rule interpretation and ideal coincidence selection are model assumptions.
Full scattering is unitary; the accepted branch is conditional. Exact probability
1/9 does not mean deterministic success or a nondestructive herald.
Scalable KLM architectures, Kerr interactions, spectral wave-packet overlap,
partial distinguishability, photon loss and detector noise are not modeled.
Python correctness, JSON/SHA-256 correctness and SimLab-to-Lean correspondence
remain open. Novelty is not assessed. The network isolates the controlled-sign
core associated with Ralph, Langford, Bell and White (2002), using the project's
complex phase convention; exact identity with the paper's full CNOT diagram
is not asserted.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.27](../docs/release-v0.5.27.en.md)

## Historical public snapshot v0.5.27: Vector clocks and causal order

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 129 |
| Lean files under Verification/ | 169 top-level + 2 auxiliary = 171 |
| Root-inclusive sources identical to the private snapshot | 172 |
| Clean strict build | 3620 jobs; no warnings |
| Complete verifier audit | 15015 declarations; no violations |
| Pinned independent full audit | 15015 declarations; no violations |
| Public live tests | 74; no failures or skips; 264.431s |

All 172 proof sources match private snapshot `035b98853ca060ea70ea70815a56ae55d0d7e1d4`.

The new module formalizes vector clocks on Fin n over finite legal histories.
Events have a process, positive local sequence number, and Local, Send or Recv
payload. Message identifiers distinguish actual sends and receives. Every receive
matches an earlier send addressed to that process; timestamps are immutable.
Sends and receives are unique within their respective identifier classes.
Outstanding messages and delivery out of send order are permitted.

HappensBefore is the strict transitive closure of local event order and matching
send-to-receive edges. Its definition does not use vector clocks. CausalPast adds
reflexivity separately. An executable, terminating recurrence computes timestamps
from predecessors using coordinatewise maxima and one increment of the executing
process. The local predecessor fold is proved equal to the last local timestamp;
the message fold is proved equal to the unique delivered send timestamp.
These lemmas recover the ordinary local/send tick and receive max-then-tick rules.

Induction over trace prefixes proves the causal-past invariant: each coordinate
is the maximum local event number of that process in the reflexive causal past,
or zero if empty. It yields both directions of HappensBefore e f iff V(e)<V(f),
timestamp injectivity and causal incomparability iff vector incomparability for
distinct events. Strict vector comparison means coordinatewise <= and unequal
vectors, not strict inequality in every coordinate. The order isomorphism is onto
the image of event timestamps, not onto the entire space of natural-number vectors.
Concurrency here does not mean physical simultaneity or commutation of application
operations. No desired causal invariant is assumed in execution legality.

The n=2 bridge preserves the existing DistributedVectorClocks tick, merge, receive
and comparison operations. Kernel regressions cover independent first events,
a three-process causal relay, out-of-order delivery, outstanding messages, n=1,
and exclusion of self-concurrency. Formal counterexamples show that omitting the
increment can identify causally ordered events and omitting merge can lose a
send-to-receive causal dependency.

These finite-trace safety results require neither FIFO delivery nor an eventual
delivery or scheduler-fairness assumption. Receives must be authentic and match
previous sends; duplicate receives are excluded. Delivery liveness is not claimed.
Counters are unbounded naturals. Bounded-machine counter overflow, node failures,
process restarts, Byzantine timestamp forgery, dynamic membership, clock compression,
physical time and network latency are not modeled. Python correctness, JSON/SHA-256
correctness and SimLab-to-Lean correspondence remain open. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.26](../docs/release-v0.5.26.en.md)

## Historical public snapshot v0.5.26: Raymond tree message complexity

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 128 |
| Lean files under Verification/ | 168 top-level + 2 auxiliary = 170 |
| Root-inclusive sources identical to the private snapshot | 171 |
| Clean strict build | 3619 jobs; no warnings |
| Complete verifier audit | 14727 declarations; no violations |
| Pinned independent full audit | 14727 declarations; no violations |
| Public live tests | 73; no failures or skips; 267.488s |

All 171 proof sources match private snapshot `9cc2a20c343c62e126b0fc1f7fd34fd4ad88f78a`.

The module reuses DistributedRaymondTreeMutex without changing its transition
semantics. A completed isolated request starts with one token owner, empty queues
and no network traffic. Only one client invokes requests. The imported accounting
identity counts actual network sends: REQUEST=dist(u,t), PRIVILEGE=dist(u,t).
Local handler steps, message receipt and elapsed time are not counted as sends.

Finite maxima define treeDiameter and treeHeight. The new theorems establish
M(u,t)=2 dist(u,t)<=2 diameter<=4 height(root). Reaching 4h requires an explicit
pair of maximum-depth vertices whose shortest path passes through the root.
Height alone does not imply diameter=2h.

Finite legal completion is proved separately, by a bounded increasing integer
service rank and existence of an enabled service step while the client remains
requesting. The diameter theorem supplies valid holder routes, an actual finite
IsolatedExecution reaching inCS and send count exactly 2 diameter. This is an
existence theorem using classical choice, not an executable scheduler or a claim
that every arbitrary schedule terminates. No service assumption is inserted into
the existence witness. The prior module's fairness contracts remain separate.

Complete k-ary trees are explicit graphs of words over Fin k of length at most h,
with dropLast as parent. Connectivity and acyclicity are proved. For k>=2, h>=1:
N=sum(j=0..h) k^j=(k^(h+1)-1)/(k-1), height=h, diameter=2h, and Mmax=4h.
The inequalities k^h<=N<k^(h+1) give h=Nat.log k N. A Mathlib IsBigO theorem
formalizes logarithmic cost in actual vertex count, atTop in h for each fixed k.
Isomorphisms transfer these graphs to Fin(card V), where actual protocol traces
attain the stated maxima. Chain and star graphs are explicitly constructed too.

Regressions cover local ownership (zero sends), a chain (2(N-1)), a star for N>=3
(four sends), and the binary height-three tree (15 nodes, diameter six, exactly
12 sends and not eight). A ternary height-two example has 13 nodes and eight
sends. Degenerate single-node and height-zero counting cases are also checked.

Only isolated REQUEST and PRIVILEGE sends are analyzed. Concurrent request costs,
amortized queues, random traffic, physical latency and faults are not modeled by
this extension. Logarithmic cost is specific to this tree family; a chain remains
linear. Implementation refinement, Python correctness, JSON/SHA-256 correctness
and SimLab-to-Lean correspondence remain open. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.25](../docs/release-v0.5.25.en.md)

## Historical public snapshot v0.5.25: Two-photon Hong–Ou–Mandel interference

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 127 |
| Lean files under Verification/ | 167 top-level + 2 auxiliary = 169 |
| Root-inclusive sources identical to the private snapshot | 170 |
| Clean strict build | 3618 jobs; no warnings |
| Complete verifier audit | 14510 declarations; no violations |
| Pinned independent full audit | 14510 declarations; no violations |
| Public live tests | 72; no failures or skips; 260.670s |

All 170 proof sources match private snapshot `611ba17cda45a492ff45c83f698456408ea402e8`.

For 0<=T<=1 and R=1-T, the normalized occupation basis is
|2,0>, |1,1>, |0,2>. The symmetric-square construction is tied to the imported
complex splitter B(T) by a polynomial substitution theorem with factorial
normalizations. This is a finite two-photon sector, not a construction of the
full Fock space or canonical commutation relations.

The lifted matrix U_two_photon satisfies both U†U=I and UU†=I and preserves
the squared Hermitian norm of arbitrary complex input vectors. On |1,1>,
the actual output is (i sqrt(2TR), T-R, i sqrt(2TR)). Born probabilities are
defined as Complex.normSq of these components, yielding P20=P02=2TR and
P11=(2T-1)², nonnegative and summing to one. At T=1/2, P11=0 and the exact
state is (i/sqrt(2))(|2,0>+|0,2>).

The single-mode phase gauge diag(1,i) induces the occupation gauge
Q=diag(1,i,-1). The lifted complex matrix equals Q U_real Q†, and U_real
agrees with QuantumBeamSplitterTransform. For general inputs both input and
output coordinates are rephased. For |1,1> this changes the input by only
a global phase, so all three outcome probabilities agree directly.

The distinguishable reference retains particle labels and assigns independent
joint weights |B(j,0)|² |B(k,1)|². Their nonnegativity, normalization and
factorization into actual marginals are proved. Coincidence is the disjoint
event j!=k, giving P_dist=T²+R²>=1/2>0. The reference assumption is explicit.
HOM visibility uses (P_dist-P11)/P_dist, not a maximum-plus-minimum denominator.
It equals 2TR/(T²+R²), lies in [0,1], and equals one exactly when T=1/2.

Ideal indistinguishable modes, the stated preparation and lossless optics are
model assumptions. The temporal wave-packet profile P(tau), spectral overlap,
dip shape or width, partial distinguishability, photon loss, frequency jitter,
detector noise and hardware implementation are not modeled. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.24](../docs/release-v0.5.24.en.md)

## Historical public snapshot v0.5.24: Complex beam splitter and MZI phase response

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 126 |
| Lean files under Verification/ | 166 top-level + 2 auxiliary = 168 |
| Root-inclusive sources identical to the private snapshot | 169 |
| Clean strict build | 3617 jobs; no warnings |
| Complete verifier audit | 14415 declarations; no violations |
| Pinned independent full audit | 14415 declarations; no violations |
| Public live tests | 71; no failures or skips; 263.419s |

All 169 proof sources match private snapshot `0556810415b74197251b6a7e8c2e712f5375b97f`.

For 0<=T<=1 the lossless symmetric splitter is
B=[[sqrt(T),i sqrt(1-T)],[i sqrt(1-T),sqrt(T)]]. The arm operator is
D(phi)=diag(exp(i phi),1), and U=B†DB explicitly uses the inverse second splitter.
Both inverse identities and Hermitian Euclidean norm preservation hold for B and U.
The reflection factor i=exp(i pi/2) belongs to this chosen convention, not every
reflecting device; a zero component does not have a defined relative phase.

For input (1,0), the actual matrix output gives c0=T exp(i phi)+1-T and
c1=i sqrt(T)sqrt(1-T)(1-exp(i phi)). Probabilities are defined by Complex.normSq,
then proved to equal P0=1-4T(1-T)sin²(phi/2) and P1=4T(1-T)sin²(phi/2).
They lie in [0,1], sum to one, have period 2pi and satisfy the endpoint cases.
At T=1/2 they are cos²(phi/2) and sin²(phi/2). For nonnegative input power,
the corresponding intensities exactly equal the SolarisMithraCore formulas.

For positive I0, port-0 extrema are I0 and I0(2T-1)², with both bounds proved
and attained at phases 0 and pi. They construct a valid InterferencePattern with
V=4T(1-T)/(1+(2T-1)²), equal to one at T=1/2. A constant phase offset shifts
the attainment points but leaves the extrema and visibility unchanged.
Geometric dependence is substitution under the external premise phi=kappa*DeltaL+phi0;
kappa=0 does not allow scanning the phase curve by changing path length.

These results follow from the specified complex matrix model, not from Maxwell's
equations. Material dispersion, polarization, loss, detectors, hardware synthesis
and full Fock-space dynamics are not modeled. Decoherence and stochastic phase
noise are not inferred from a deterministic phase offset. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.23](../docs/release-v0.5.23.en.md)

## Historical public snapshot v0.5.23: Balanced Deutsch-Jozsa oracle classification

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 125 |
| Lean files under Verification/ | 165 top-level + 2 auxiliary = 167 |
| Root-inclusive sources identical to the private snapshot | 168 |
| Clean strict build | 3616 jobs; no warnings |
| Complete verifier audit | 14330 declarations; no violations |
| Pinned independent full audit | 14330 declarations; no violations |
| Public live tests | 70; no failures or skips; 262.919s |

All 168 proof sources match private snapshot `2dba8201d6046e7017c2353c95941dd5d51237f8`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.22](../docs/release-v0.5.22.en.md)

## Historical public snapshot v0.5.22: General Chandy-Lamport snapshots

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 124 |
| Lean files under Verification/ | 164 top-level + 2 auxiliary = 166 |
| Root-inclusive sources identical to the private snapshot | 167 |
| Clean strict build | 3615 jobs; no warnings |
| Complete verifier audit | 14271 declarations; no violations |
| Pinned independent full audit | 14271 declarations; no violations |
| Public live tests | 69; no failures or skips; 260.408s |

All 167 proof sources match private snapshot `d06eee279392f800cbb8a5ff8dff3af30b051edc`.

The model covers arbitrary finite directed networks with edge-indexed FIFO queues,
arbitrary application payloads and local data. A node captures its actual local
value and event counter once, atomically appending markers to outgoing queues.
The cut is consistent: every receipt before the destination cut has a matching
send before the source cut. Phase observations are linked to strict event order.

Every closed channel records exactly the ordered crossing messages: sent before
the sender cut and received after the receiver cut. Packet identities distinguish
repeated payloads. Snapshots and closed channel records remain unchanged.

Termination requires directed reachability of all nodes from the initiator,
ReliableDelivery and WeakFairness. ReliableDelivery means each already queued
item is eventually processed or offered at the FIFO head; it includes progress
past earlier packets and is stronger than absence of transport loss alone.
Weak fairness governs continuously enabled initiation and marker reactions.
The theorem supplies a finite common completion index, not a uniform latency bound.
An explicit reliable fair execution witnesses satisfiability of the assumptions.

A non-FIFO counterexample adds only an adjacent swap: a marker overtakes an older
packet, and the closed channel record misses that packet. This demonstrates failure
of exact recording; it does not claim every reordering violates cut consistency.
A reliable fair disconnected execution demonstrates the need for root reachability.

One snapshot and fixed topology are modeled. Permutation/causal equivalence via
commuting application events, global termination detection, snapshot collection,
crashes, loss, recovery, dynamic topology, overlapping snapshots and Byzantine
behavior are outside the model. Python, JSON/SHA-256 and SimLab remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.21](../docs/release-v0.5.21.en.md)

## Historical public snapshot v0.5.21: Schnorr identification

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 123 |
| Lean files under Verification/ | 163 top-level + 2 auxiliary = 165 |
| Root-inclusive sources identical to the private snapshot | 166 |
| Clean strict build | 3614 jobs; no warnings |
| Complete verifier audit | 13805 declarations; no violations |
| Pinned independent full audit | 13805 declarations; no violations |
| Public live tests | 68; no failures or skips; 257.020s |

All 166 proof sources match private snapshot `0c7104839e071108f4f9d08d6a75c4799f6d2581`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.20](../docs/release-v0.5.20.en.md)

## Historical public snapshot v0.5.20: Pedersen homomorphic sums

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 122 |
| Lean files under Verification/ | 162 top-level + 2 auxiliary = 164 |
| Root-inclusive sources identical to the private snapshot | 165 |
| Clean strict build | 3613 jobs; no warnings |
| Complete verifier audit | 13704 declarations; no violations |
| Pinned independent full audit | 13704 declarations; no violations |
| Public live tests | 67; no failures or skips; 248.050s |

All 165 proof sources match private snapshot `2c01798362d54124a711be83a0855e40dbf0efdc`.

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

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.19](../docs/release-v0.5.19.en.md)

## Historical public snapshot v0.5.19: Raymond tree mutual exclusion

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 121 |
| Lean files under Verification/ | 161 top-level + 2 auxiliary = 163 |
| Root-inclusive sources identical to the private snapshot | 164 |
| Clean strict build | 3585 jobs; no warnings |
| Complete verifier audit | 13610 declarations; no violations |
| Pinned independent full audit | 13610 declarations; no violations |
| Public live tests | 66; no failures or skips; 253.584s |

All 164 Lean sources including the root file match private snapshot `d4a72dfb113fbdb5f4a4157db0f9f824ff5ffb48`.
Both complete audits permit only propext, Classical.choice and Quot.sound.
The strict registry hook and knowledge catalog passed separately. The two nested
specification files remain auxiliary tooling rather than subject-module increments.
[Hashes and measured commands](../tools/validation_snapshot.json).

[Raymond contract](09_distributed_systems/DistributedRaymondTreeMutex.md).

The model uses a fixed finite connected acyclic graph, one initial token owner,
empty queues/channels, and serialized local ASSIGN_PRIVILEGE / MAKE_REQUEST handlers.
The network permits reordering; receipt is exact-once and rejects fabricated messages.
Occurrence serials identify REQUEST packets, not protocol priorities. No mechanical
refinement to an implementation or the original pseudocode is asserted.

Reachable-state proofs establish exactly one privilege token across nodes and transit,
mutual exclusion (each inCS node is an actual owner), and duplicate-free FIFO queues.
Queue uniqueness is derived from request accounting, not imposed by a constructor.

Effective holder paths end at the current owner or the destination of an in-flight
PRIVILEGE. A reachable two-node counterexample has holder(0)=1 and holder(1)=0 while
the token travels from 0 to 1. Thus raw holder pointers need not be globally acyclic;
the effective path stops at the packet destination and suppresses its outgoing edge.

Every requesting observation eventually reaches inCS under ReliableDelivery (eventual
receipt of every REQUEST and PRIVILEGE), WeakFairness of local internal handlers and
FiniteCS (eventual exit). These contracts do not assume eventual service. Concurrent
later requests are allowed. The proof uses finite FIFO positions and the finite holder
path; it does not assert that distance to the token decreases under contention.

For isolated executions from quiescent initialization with only application client u,
at completed entry each message kind has exactly dist(u,initialOwner) sends: total
2*dist. Arbitrary legal delays and interleavings are allowed. Retained-token reentry
adds no traffic. This counts sends, not time or local steps. A chain can require
2*(n-1) messages; O(log n) is not a universal bound and no such bound is claimed under
arbitrary contention.

Node/link failures with token loss, token regeneration, dynamic topology/membership,
Byzantine behavior and real-time guarantees are outside scope. Python, JSON/SHA-256
and external SimLab input-to-byte binding remain open obligations. Scientific priority
has not been assessed.

## Historical verification records

[Knowledge base](README.md) · [Release v0.5.18](../docs/release-v0.5.18.en.md)

Measured: 120 direct imports, 162 Lean files under Verification/,
12,922 project declarations, 3547 strict build jobs and 65 public live tests
without failures or skips (253.994s). Both complete audits allow only
`propext`, `Classical.choice`, and `Quot.sound`. The strict registry hook also passed.
The two nested specification files are auxiliary meta-audit tooling.
[Hashes and measured commands](../tools/validation_snapshot.json).

## Shor LCM/GCD recovery scope

[Theorems and assumptions](03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md).

listLCM is executable structural recursion over a finite list of natural-number
candidates. Neither the unknown order nor spectral numerators are inputs. The empty
LCM is one; append and membership invariance cover incremental use, reordering and
duplicates. No time or bit-complexity bound is asserted.

For r>0 and a nonempty list with every q dividing r, L=listLCM(qs) divides r and
L=r iff foldr (fun q acc => gcd(r/q,acc)) 0 qs = 1. Nonemptiness is necessary for
this unanchored GCD criterion. For spectral denominators q=r/gcd(s,r), the exact
identity is L=r/gcd(r,foldr gcd 0 ss); thus L=r iff the anchored GCD is one.
This version includes empty ss: empty input recovers only order one. At r=6,
ss=[3,2] gives denominators [2,3] and recovers six without any individual q=r.

The bridge reuses module 119's canonical reduced denominators and the existing
Shor Parameters (N>=2, coprime a,N, positive actual order and padded target register).
Given Q=2^n>=N² and each observed y<Q satisfying Nearest to its latent s/r with s<r,
the correct denominator occurs among the corresponding continued-fraction candidates.
This does not identify the latent label or select its denominator from the observable list.

The modular check proves r divides L. With separately established L divides r,
it gives equality. A certified divisor means mathematical provenance, not merely
a successful modular check. No automatic candidate-selection algorithm is supplied.

A kernel-checked counterexample has N=31,a=2,order=5,y=410,Q=1024. Candidate
denominators [1,2,5] have LCM 10, which passes the modular check but is not the order.
Regressions verify 31²<=1024 and |410/1024-2/5|<=1/(2*1024), so this failure persists
at adequate QPE resolution. Taking the LCM of all candidates is unjustified.

No i.i.d. measurement law, probability of a coprime sample family, number of runs,
factorization via gcd(a^(r/2)±1,N), physical implementation or gate synthesis is proved.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
The algebra reuses pinned Mathlib Nat.div_lcm_eq_div_gcd; scientific priority has
not been assessed. This is conditional multi-sample recovery, not a full Shor algorithm.

## Shor continued-fraction scope

[Theorems and assumptions](03_quantum_physics_and_optics/QuantumShorContinuedFractions.md).

The algorithm computes finite partial quotients and convergents of the exact rational
y/Q by Euclidean descent, terminating at an integer. Its inputs y,Q,N do not contain
the unknown spectral numerator s or period r. The candidate list filters denominators
strictly below N. Membership in the unfiltered list is equivalent to being a Mathlib
Real.convergent, including its repeated terminal values.

For N≥2, a coprime to N, r=orderOf(a : ZMod N), 0≤s<r and 0≤y<Q, the existing Shor
model proves 0<r<N. With Q=2^n≥N², the modular QPE Nearest condition implies ordinary
|y/Q-s/r|≤1/(2Q). The proof handles s=0 and rules out wrap-around at this resolution.
Since q=r/gcd(s,r)≤r<N, the error is strictly below 1/(2q²). Pinned Mathlib's strict
Legendre theorem supplies the convergent, and the finite-list bridge proves its
presence among the executable candidates.

The correct reduced denominator q divides r. Other list entries are not asserted
to divide r. If gcd(s,r)=1, q=r and r belongs to the modularly checked list. The
modular check a^q mod N = 1 mod N proves r divides q; proper multiples can pass.
If q divides r is separately established, mutual divisibility gives equality.
For s=0 the reduced denominator is one, recovering the order only when r=1.

The number of Euclidean stages is at most 2*Nat.log 2 Q+1 for Q>0. This counts partial
quotients, not every list operation, bit operation, modular exponentiation or total
runtime. No O(log N) claim is made without additionally bounding Q in terms of N.

The existing actual-input QPE mixture gives a contribution bound 4/(r*pi²) for a
single component's nearest sample, combined here with candidate membership. This
is distinct from the conditional component bound 4/pi². Guaranteed single-run
success, independent repeated measurements, LCM recovery, classical factorization,
long-integer bit complexity, physical noise and gate synthesis are outside scope.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
No scientific-priority claim or full factoring algorithm is asserted.

## Suzuki–Kasami scope

[Model and theorem details](09_distributed_systems/DistributedSuzukiKasamiMutex.md).

The fixed-membership, crash-free model uses Fin n, unbounded natural request
sequences and serialized client invocations. Reachability implies exactly one token,
counting both holders and the channel, mutual exclusion, and a duplicate-free queue.
The payload is a global semantic coordinate exposed only to the holder; it is
unchanged in transit. No runtime shared memory is assumed.

ReliableDelivery requires eventual delivery of actual REQUEST and token messages.
WeakFairness schedules continuously enabled send and enter actions. FiniteCS requires
every critical-section visit eventually to leave. Under these contracts, every
Requesting observation eventually reaches InCS, including runs with later requests.
Safety does not require fairness. No numerical waiting-time bound is proved.

The model separates immediate idle-holder handoff into queue reservation and a
separately scheduled send. New local requests cannot bypass an already reserved
handoff. This serialization is explicit; no mechanized refinement to the original
program is claimed. FIFO holds after queue insertion, not as global request order.
REQUEST fanout is atomically enqueued; individual deliveries are separate, unordered
and exact-once. Token transport uses one in-flight slot, without loss or duplication.

RN and LN are nondecreasing, with LN[j] ≤ RN_j[j] ≤ LN[j]+1 at the sender. The stronger
claim LN[j] ≤ RN_holder[j] is false: a reachable three-node trace leaves node 2 holding
a token with LN[1]=1 and RN_2[1]=0 before a delayed REQUEST arrives. Receiving the token
does not silently synchronize RN. Retained-token reentry does not increment the
network request number and need not join the queue. LN is not a count of every CS visit.

Crashes, lost-token recovery, dynamic membership, partitions, Byzantine behavior,
finite counter overflow, real-time bounds and network/application implementations
are outside scope. Python, JSON/SHA-256 and binding external SimLab inputs to bytes
remain open obligations. No scientific-priority claim is made.

## Spectral order-finding scope

[QuantumShorOrderFindingCore](03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md)
constructs a permutation of every residue modulo N for a coprime base, fixes padded
register states, and proves inverse and unitary operator identities. Its orbit
spectrum is orthonormal and decomposes |1⟩ without requiring knowledge of the order
for input preparation. The actual QPE joint output yields a normalized marginal
mixture with weights 1/r. The nearest-sample 4/π² bound applies to each component;
the guaranteed contribution of one component to the mixture is 4/(rπ²).
Order recovery, continued fractions, repeated-run LCM recovery, factorization,
gate synthesis, complexity and physical noise are outside scope. Python,
JSON/SHA-256 and binding external SimLab inputs to bytes remain external obligations.

## General QPE scope

[QuantumPhaseEstimationGeneral](03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md)
derives the output for an arbitrary finite target and n-bit control register from
controlled powers and the inverse Fourier transform. Fourier unitarity, exact
dyadic recovery, probability normalization and the nearest-sample lower bound
4/π² hold in the exact complex model. The measured-output claims use a supplied
normalized eigenvector of a unitary operator. Both midpoint choices, modular
wraparound, negative phases, the singular geometric-sum branch and n=0 are covered.
The n=2 bridge identifies the complete old operational output.
Eigenstate preparation, gate synthesis and cost, physical noise, decoherence and
full Shor are not proved. Python, JSON/SHA-256 and SimLab byte binding remain external.

## Operational snapshot scope

DistributedChandyLamportSnapshot derives saved-cut consistency and exact completed-channel contents from two-process FIFO transitions. Open-channel recording has separate received-so-far semantics. There is one snapshot instance; no failures, arbitrary n-node topology, fairness, eventual completion or completion detector are verified.

All 163 Lean sources, including the root file, match private snapshot `5e714619c1455a47bc58d0f87d8cfe8a94db0c7b` byte-for-byte.

## Exact QPE scope

QuantumPhaseEstimation has two control qubits and a one-qubit complex target. Controlled U/U² derive phase kickback from an exact eigenstate equation; the inverse Fourier transform returns the correct basis state. The four supported phases are 0, 1/4, 1/2 and 3/4. A normalized eigenstate and norm-preserving complex-linear operator are supplied. Physical measurement, preparation, gate noise and approximate QPE are not certified.

## Numerical scope

- NumericBinaryGrid supplies the exact binary64 magnitude decoder and parity lemmas.
- NumericRoundingCertificates checks rational interval and exact-midpoint witnesses,
  with signed zero, subnormals and overflow. The mathematical checker is not a
  verification of Python or CPU instructions.
- NumericRealRounding transports rational endpoint certificates to enclosed real values.
- NumericSQLIntervalBounds encloses `sqrt(hbar/(mass*frequency))` under explicit
  positive input intervals and containment hypotheses. Physical calibration is external;
  the separate gap expression is handled by NumericSQLGapBounds.
- NumericSQLGapBounds derives affine gap bounds, exact zero iff balance for positive
  parameters, canonical +0 and composition with real rounding. Rationalization,
  exact cell-boundary comparison and the new SimLab search are not formalized.
- NumericCertificateDigestBridge composes explicit pure digest/parser parameters
  with the mathematical checker. Expected digest, parser, grid and SQL inputs are
  external context. SHA-256, JSON/RFC 8259, Python equivalence, byte binding of those
  inputs and source authenticity are not proved. Digest equality is not byte equality.

Historical indeterminate intervals remain indeterminate. Later exact-midpoint or
exact-zero evidence is separate. No simulation runtime or full simulation archive
is distributed. The curated rounding provenance JSON is external metadata; its
source simulation paths are not included in this package.

The earlier placement certificate retains its exact 256 rational records, boundary
and pairwise-disjointness guarantees. The deterministic converter is checked
externally; its JSON parser and hashing are not Lean-verified.

Scalar MuSig2 does not establish cryptographic security; the forking module proves
an elementary finite-matrix bound, not a general ROM reduction. Visibility does
not prove quantum decoherence. The documented optomechanical approximation regime
is not derived in Lean. Historical hundred-module aggregation preserves these limits.

## Multiple-target Grover scope

QuantumGroverMultipleTargets proves all-subset N=4 real dynamics, all-natural-iteration
success weights, arbitrary-state norm preservation, singleton compatibility and
an invariant orthonormal plane for nonempty proper target sets. It also proves
both rank-one reflection counterexamples. No arbitrary-N search, query-complexity,
trigonometric-angle formula, separate topological-closedness theorem, physical
measurement, noise or hardware certification is claimed.

## Raft commit application scope

DistributedRaftCommitApplication and its two support modules derive actual
commit-event provenance for server and RPC prefixes, retained committed prefixes,
and ordered deterministic local application. A reachable 45-transition example
shows why an old-term majority alone is insufficient. Cross-node fold agreement
requires equality of full entries, including commands. This extension does not
prove a new global State Machine Safety theorem, liveness, client exactly-once
behavior, timeout handling, crash/recovery or fsync/WAL.

## Operational 2PC timeout scope

Two independent participants and a stopped coordinator distinguish safe pre-vote
abort from unsafe forced decisions on identical prepared local views. Under both
prepared and coordinator stopped, no queued decision is equivalent to no finite
continuation reaching a terminal participant. Other packets may remain in flight.
Decision delivery is possible, not guaranteed. Fairness, recovery, peer termination,
3PC and disk durability are not claimed.

## Two-participant 3PC scope

The fixed two-participant model uses bounded request/response queues and crash-stop
failures. Reachable agreement includes stopped terminal decisions. Completion paths
and eventual completion under weak fairness are separate theorems. Exact surviving
membership, unique coordinator appointment and atomic epoch fencing are external
contracts. No arbitrary-n protocol, dynamic joining, network partition tolerance,
crash recovery or runtime implementation is certified.

## Static-epoch CMH scope

The graph is fixed within each detector execution. Probe provenance and detection
soundness are inductive invariants; eventual detection after initiation requires
the explicit payload-delivery contract. Graph replacement requires an external
isolated reset. The dynamic counterexample refutes a naive send-time-only check,
not the original CMH protocol. See the [release scope](../docs/release-v0.5.10.en.md).

## Arbitrary-phase Grover scope

The one-target C^4 model proves complex linearity, explicit adjoints and inverse
identities, Hermitian norm preservation and a complex plane invariant under every
pair of real phases. Equal phases from uniform have
P(phi)=1-3*(1+cos(phi))^2/16 and P=1 iff cos(phi)=-1. At pi the raw step is the
negative of the canonical step; measurement weights agree. This is not a general
Hoyer phase-matching theorem or Long iteration schedule. Hardware, noise and
Python/JSON/SHA-256/SimLab byte binding remain outside the result.

## Simon scope

The complex H/XOR/H circuit yields exact uniform probability 2/(2^n) on s-perp under SimonPromise with nonzero s. Recovery requires orthogonal rows spanning rank n-1 over F2. No sample-count bound or implemented Gaussian solver is certified. See the [Simon card](03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md).
