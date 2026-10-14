# Release v0.5.59: Constant product with virtual reserves

This release adds DeFiConstantProductVirtualReserves as the 161st direct import
of MasterSuite. All 204 Lean sources, including Verification.lean, match reference
snapshot 59ec88ee2ce6cf6f9ff5a51a586fc067dabef630 byte-for-byte.

## Proved contract

Nonnegative rational reserves x,y and fixed nonnegative offsets alpha,beta give
positive effective reserves X=x+alpha,Y=y+beta. For gross input d>=0 and fee
0<=gamma<1, e=(1-gamma)*d and the exact output is o=Y*e/(X+e).
The module proves the exact real-reserve solvency criterion
`o <= y iff beta*e <= y*X`. Positive virtual reserves alone do not ensure solvency.
The executable rational transition checks input, fee and this condition.

Fees remain in trading reserves. The updated product satisfies
`K' = K + gamma*d*(Y-o) >= K`, with equality for zero fees and strict growth
for positive input and fee. Reverse swaps follow by swapping the axes.
For a fixed fee, output strictly increases with input, and average output per
unit of positive gross input does not increase. A regression demonstrates that
arbitrary fee changes need not preserve that average-price monotonicity.
Successful executable finite chains with variable valid fees preserve offsets
and have nondecreasing product.

The natural model rounds payouts down and required gross inputs up, with
nonnegative errors strictly below one. The rounded-up input is the least natural
input whose exact quote covers the requested payout. Both modes and directions
preserve state validity and nondecreasing product through successful finite chains.
Exact-input execution conservatively checks exact rational solvency before
rounding. Exact-output execution pays the requested amount, retaining any surplus
from rounding the input up; it does not pay the potentially larger recomputed quote.
Real-reserve exhaustion is permitted when virtual reserves remain positive.

Regression coverage comprises 24 kernel assertions and 25 compiled cases,
including zero input, one wei, exact division, reserve exhaustion, both directions
and modes, variable-fee chains, invalid parameters and the changing-fee counterexample.

## Clean Water

This model includes fees in trading reserves and differs from Uniswap v3's
separate fee accounting. Fixed offsets do not model tick crossings, changing
liquidity or the full pool lifecycle. Exact Solidity/EVM correspondence, machine
overflow, optimized integer implementation and gas bounds are not modeled.

Nondecreasing product does not establish absence of arbitrage, preservation of
market value at external prices, MEV or sandwich protection, or economic returns.
Bulletproofs witness extraction, HVZK and Fiat-Shamir/ROM remain open.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Scientific novelty is not assessed.

[Detailed contract](../knowledge/01_defi/DeFiConstantProductVirtualReserves.md) ·
[Lean source](../Verification/DeFiConstantProductVirtualReserves.lean)

## Measured validation

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

