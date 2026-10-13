# Release v0.5.53: discrete concentrated-liquidity reference arithmetic

This release exports DeFiConcentratedLiquidityMath and its integration from private
snapshot `2d3259bc8d8aba61a10eae2c8865b699fd5733ae`. It follows public main
`68c341f54b5bc03804e643d17082246c09d6af13` (v0.5.52).

## Formal contract

The executable Q64.96 reference quantizer has a proved one-grid-unit error bound
relative to the real square root of the ideal tick price. Integer token deltas
round upward for collection and downward for payout, with errors below one unit.
An exhaustive finite-grid swap search proves price bounds, input-plus-fee budget
bounds for exactInput and output caps for exactOutput. Position-derived tick net
changes preserve nonnegative active liquidity in both directions; finite traces
satisfy the signed-change identity and repeated same-boundary application is
inactive. The test wrapper includes 23 kernel examples and 16 execution cases.

See the [complete contract](../knowledge/01_defi/DeFiConcentratedLiquidityMath.md)
for hypotheses and exact-output semantics.

## Clean Water boundaries

This is an executable mathematical reference model. Equality with Solidity
SwapMath/TickMath branches, EVM machine overflow, efficient wide-grid search and
the full pool lifecycle are not modeled. Exact-output correctness means an output
cap and maximal feasible grid progress, not guaranteed fulfillment of every
requested amount. The caller supplies the target-price/boundary-tick association.
No economic returns, market-value preservation or MEV protection are asserted.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.

## Measured validation

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

