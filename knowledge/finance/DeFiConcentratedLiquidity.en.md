---
id: DeFiConcentratedLiquidity
language: en
section: finance
source: Verification/DeFiConcentratedLiquidity.lean
source_sha256: 1b86c9d50298ec845903c27e087b0efc8de2e7691ad7d8b33578719ba3e2eabd
novelty: not-assessed
status: reviewed
---

# DeFiConcentratedLiquidity

[Section](README.md) · [Lean](../../Verification/DeFiConcentratedLiquidity.lean)

## Verified result

The existing RangePosition and PriceRangePosition results are retained. The new RangePool specifies L>0 and 0<sa<sb. Its shifted reserves simplify to L/s and L*s; for s>0 their product equals L². At sa, Y is zero and X is strictly positive; at sb, X is zero and Y is strictly positive. X strictly decreases for 0<s1<s2, while Y strictly increases whenever s1<s2.

The inequalities capital_savings_x and capital_savings_y follow from the positive offsets L/sb and L*sa. They compare the defined real and virtual quantities. They do not establish economic capital efficiency, equal market depth between implemented pools, an optimization result or a return guarantee.

Key new entry points: virt_x_eq, virt_y_eq, concentrated_virtual_product, uniswap_v3_invariant_identity, boundary_at_sa_y_zero, boundary_at_sa_x_pos, boundary_at_sb_x_zero, boundary_at_sb_y_pos, reserve_x_strictly_decreases and reserve_y_strictly_increases.

## Assumptions and limitations

The functions accept arbitrary real s and do not enforce sa≤s≤sb. Outside the range, a real reserve can be negative; no piecewise clamping is defined. Product preservation requires positive s. The reserve-offset comparisons hold even outside the range and therefore are not physical-capital guarantees. Endpoints describe single-token coordinates, not an executed swap trajectory or conversion of all assets. Monotonicity is a comparison of formulas at fixed L and endpoints.

The previous APIs, theorem signatures, master alias and concentrated_liquidity registry accessor are preserved. DeFiConcentratedLiquidityFormalSuite gains the new fields, which manual constructors must provide. No duplicate module/import is added.

Discrete tick spacing, Q64.96 arithmetic and rounding, cross-tick swap loops, feeGrowthInside, slippage and impermanent-loss dynamics are not formalized in this module. No correspondence with deployed Uniswap contracts is proved. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiConcentratedLiquidity.defi_concentrated_liquidity_master_suite`.
