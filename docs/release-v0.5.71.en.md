# Release v0.5.71: Liquidation accounting and separate asset ledgers

[Detailed contract](../knowledge/01_defi/DeFiLendingLiquidationAccounting.md)

The 173rd direct module connects liquidation admission to fixed-index debt repayment.
It proves collateral bonus splitting, with the protocol fee booked in a separate
collateral treasury rather than debt-asset reserves; conservation of both asset
balances; consistency of scaled debt; and conditional health-factor changes.
For positive debt, full repayment satisfies the close-factor constraint iff the
factor is one. Other admission guards, including sufficient collateral, still apply.

The executable natural reference policy checks scale, prices, index, repayment,
close factor, liquidatability and collateral sufficiency. It specifies the order
of floor divisions and uses a residual liquidator allocation. Partial share burns
and full displayed-debt repayment have distinct error bounds. The independently
maintained debt-ledger/index gap is separate from the n-1 reconciliation dust bound.
Regressions cover partial/full repayment, fee endpoints, zero bonus, unhealthy
and healthy positions, rejected inputs, one-unit amounts and nonzero rounding.

## Clean Water

These are bookkeeping guarantees. Oracle accuracy/freshness, market liquidity,
slippage, conversion of treasury collateral, bad-debt recoverability, overall
protocol solvency, actual token transfers and deployed-contract correspondence
remain external obligations. Machine overflow and gas are not modeled.
Full Bulletproofs range extraction through multipoint polynomial interpolation,
Tendermint Accountable Safety, Python, JSON/SHA-256 and SimLab remain open.

## Measured validation

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

