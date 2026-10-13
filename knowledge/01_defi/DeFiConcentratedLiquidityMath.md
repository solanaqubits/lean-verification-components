---
id: DeFiConcentratedLiquidityMath
language: en
section: finance
source: Verification/DeFiConcentratedLiquidityMath.lean
source_sha256: 289fc1a14182883142db8f19694426e2e94f672cd8b477aeb99b6a2d7719f29c
novelty: not-assessed
status: reviewed
---

# Discrete concentrated-liquidity reference arithmetic

[Section](../finance/README.md) · [Lean](../../Verification/DeFiConcentratedLiquidityMath.lean)

## Price representation and rounding

The ideal rational tick price is (10001/10000)^i for an integer i. `scale = 2^96`
and `decode s = s / scale`. The executable reference root-price quantizer takes
Nat.sqrt of the natural floor of idealPrice i * scale². `sqrt_reference_bracket`
and `sqrt_reference_error` prove that its decoded value is below the true real
square root with error strictly less than 1/scale. This reference quantizer is
not Uniswap's table-of-bit-constants TickMath implementation. Extremely negative
unrestricted ticks can quantize to zero; swap parameters separately require
strictly positive current and target prices. Machine word bounds are not imposed.

`mulDivFloor` and `mulDivCeil` are executable rational floor/ceiling operations.
The proved formulas identify them with (a*b)/c and (a*b+c-1)/c, with c>0 for the
ceiling formula. Both directional errors are nonnegative and strictly below one.
`amount0Exact` and `amount1Exact` use natural raw-price endpoints a≤b and the
Q64.96 scale. The rational and real bridge theorems identify the exact deltas with
the existing continuous deltaX/deltaY formulas when denominators are positive.
Token amounts use ceiling for collection and floor for payout; the corresponding
one-token-unit error bounds are proved. These are reserve-accounting statements,
not preservation of market value at external prices.

## Executable swap reference model

`SwapParams` includes positive raw prices, natural liquidity and remaining budget,
a fee below 1,000,000, and exactInput/exactOutput. Direction is determined by the
current and target prices. `priceAt` enumerates integer progress toward the target.
`inputAt` rounds the exact input delta up; `outputAt` rounds the output delta down.
`feeFor` is ceil(amountIn * feePips / (1,000,000-feePips)).

`computeSwapStep` exhaustively searches the finite set of admissible progress
values and chooses its maximum. Progress zero is always feasible. Zero remaining
budget leaves the price unchanged. `chosen_maximal` proves maximality for positive
remaining budget, and an affordable target is reached. Bounds and strict
positivity of the next price, input+fee≤remaining for exactInput and
output≤remaining for exactOutput follow from the executable search. `fee_budget_iff`
proves equivalence to the fee-discounted floor input budget. Input and output
rounding guarantees also hold at the actual selected price. Zero liquidity with
positive remaining budget transits to the target with all token amounts zero.

This is an exhaustive mathematical reference algorithm, not a formal port of
Uniswap's closed-form next-price branches or its exact-output stopping rules.
No equality with Solidity computeSwapStep, optimal gas bound, or practical runtime
on wide Q64.96 intervals is claimed. Exact-output correctness here is the proved
output cap and maximal feasible grid progress; it is not a theorem that every
requested amount is filled. `spendTrace` derives each next remaining budget by
subtraction and proves the total input-plus-fees bound by induction. It permits
arbitrary supplied step parameters and does not certify a complete pool/router loop.

## Position-derived boundary transitions

A finite list of positions has ordered integer tick bounds and natural amounts.
Active liquidity is their sum on lower≤tick<upper. Tick net changes are induced
by entries and exits of these positions, not an arbitrary signed table.
`active_cross` proves the signed boundary identity. Both crossing directions give
exactly the new active sum, so nonnegativity is established before any toNat
conversion. `cross_trace_preserves` and `cross_trace_telescope` prove invariant
preservation and the cumulative signed-change formula for finite traces.

The stored tick chooses the appropriate side of a boundary. `crossAt` requires
that side and a reached flag; it is idempotent for the same boundary and direction.
`crossAfterSwap` obtains the flag from equality of the computed price and target.
The caller supplies the association of that target to the boundary tick; a full
TickMath-driven pool loop is outside scope. An unreached boundary leaves the state
unchanged. Returning across a boundary restores the valid starting state.

## Clean Water and verification

No global invariant asserting an unchanged L² across liquidity changes is used.
The model excludes EVM/Solidity overflow, Yul/bit-level TickMath correspondence,
fee-growth distribution, full on-chain pool execution, MEV/arbitrage security,
impermanent loss and economic returns. Python, JSON/SHA-256 and SimLab
correspondence obligations remain open. Novelty is not assessed.

The suite is `DeFiConcentratedLiquidityMath.verification_suite`.
The regression wrapper checks 23 kernel examples and 16 compiled execution cases,
including both directions/modes, one wei, fees, exact target, zero liquidity,
multiple boundary crossings and no duplicate boundary application. Compiled
execution tests complement the proofs and do not introduce axioms.
Actual full-project measurements are recorded in tools/validation_snapshot.json.

References: [SqrtPriceMath](https://github.com/Uniswap/v3-core/blob/main/contracts/libraries/SqrtPriceMath.sol),
[SwapMath](https://github.com/Uniswap/v3-core/blob/main/contracts/libraries/SwapMath.sol),
[TickMath](https://github.com/Uniswap/v3-core/blob/main/contracts/libraries/TickMath.sol).
These references motivate the arithmetic; no source-code equivalence is claimed.
