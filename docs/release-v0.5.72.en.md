# Release v0.5.72: Authorized bad debt writeoff and supplier loss

[Detailed contract](../knowledge/01_defi/DeFiLendingBadDebtSocialization.md)

The 174th direct module formalizes a supplied authorization decision and the
accounting policy r=min(R,x), h=x-r. Reserves absorb losses first; supplier claims
absorb the remainder. The transition preserves Cash+B=R+L, changes net accounting
assets by -h, and leaves cash fixed. At a positive fixed borrowing index it
preserves scaled-debt consistency. With a positive fixed supplier-share count,
the share price falls by exactly h/S and is unchanged iff x<=R.

The checked natural implementation validates authorization, positive scale/index,
individual and aggregate debt bounds, supplier coverage and the zero-share case.
The min/remainder loss split is exact; collateral registers stay unchanged.
Zero writeoff burns no shares, even when a positive scaled balance displays zero
debt. Positive partial and full displayed-debt writeoffs have separate rounding
bounds. The supplier price is undefined at S=0; otherwise floor(L*W/S) has explicit
error bounds. The signed debt-ledger/index gap is separate from n-1 reconciliation
dust. Regression coverage includes reserve thresholds, zero reserves, complete
supplier loss, one-unit amounts, nonzero rounding and rejected guards.

## Clean Water

Authorization is an external decision input, not a proof of uncollectibility or
an authentication mechanism. Real debt recoverability, withdrawal liquidity,
economic solvency and deployed-protocol correspondence remain external.
Compound III absorb with collateral transfer and subsequent sale needs a separate
model. Machine overflow, gas and transaction ordering are not modeled.
Full Bulletproofs range extraction through multipoint polynomial interpolation,
Tendermint Accountable Safety, Python, JSON/SHA-256 and SimLab remain open.

## Measured validation

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

