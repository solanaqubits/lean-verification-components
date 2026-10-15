# Release v0.5.62: Lending liquidation health factor

This release adds `DeFiLendingLiquidationHealthFactor`, the 164th direct
MasterSuite import. It models exact lending-position accounting, conditional
health improvement and residual debt coverage, with executable liquidation
transitions and directed integer rounding.

[Detailed contract](../knowledge/01_defi/DeFiLendingLiquidationHealthFactor.md)

## Proven contract

Collateral value C, threshold-weighted coverage W and the LTV borrowing limit are
separate quantities. Health is W/B for positive debt; zero debt has no numeric
health factor and is not liquidatable. Partial repayment r with bonus beta and
selected collateral threshold LT_k satisfies, at fixed settlement prices:

    HF' - HF = r * (HF - LT_k * (1 + beta)) / (B - r)
    C' - B' = C - B - beta * r.

For 0 < r < B, strict health improvement requires and is equivalent to
HF > LT_k * (1 + beta). Exact residual coverage is equivalent to
beta * r <= C - B. Admission to liquidation alone implies neither condition.
Executable guarded transitions enforce coverage, including sequences of steps.
Full repayment has a separate debt-free branch. Multi-collateral regressions
show that choosing different collateral assets can reverse the health change.

Natural collateral payouts round down; sufficient repayment rounds up.
Rounding errors, minimum repayment, debt/collateral limits and correspondence
between guarded natural subtraction and rational accounting are proved.
The bonus-budget condition suffices for integer residual coverage; it is not
claimed necessary after rounding. Counterexamples exhibit declining health and
a position deficit under admissible but insufficiently constrained liquidation.

## Scope

These are reference-model guarantees for individual positions. They do not prove
pool-wide solvency, oracle truth, market liquidity, slippage tolerance or protection
against MEV, transaction delays, gas ordering or cascading liquidation losses.
Price monotonicity is proved with other parameters fixed; time-dependent market
volatility is not modeled. No production Aave implementation equivalence is claimed.

Bulletproofs knowledge extraction, computational binding, HVZK and Fiat-Shamir/ROM,
and external Python, JSON/SHA-256 and SimLab correspondence remain open.

## Measured validation

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

