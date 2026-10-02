---
id: DeFiBondingCurve
language: en
section: finance
source: Verification/DeFiBondingCurve.lean
source_sha256: bddbfa7b14d5d1f6186fb7de8cb6dc0f0cf12511f064f14e86a51936516af5f3
novelty: not-assessed
status: reviewed
---

# DeFiBondingCurve

[Section](../finance/README.md) · [Lean](../../Verification/DeFiBondingCurve.lean)

## Verified result

For m>0 and b≥0, the model defines P(s)=m*s+b and R(s)=m*s²/2+b*s. Expanding the reserve differences gives the exact mint and burn formulas. Adding mintCost to R(s), or subtracting burnRefund, gives the prescribed post-operation reserve. Minting ds at s and immediately burning ds at s+ds yields equal cost and refund for the same curve.

For ds≠0, average mint price equals P(s)+m*ds/2; for ds>0 it strictly exceeds P(s). Spot price strictly increases for arbitrary s1<s2. The reserve polynomial strictly increases when 0≤s1<s2. Main entry points are mint_cost_formula, burn_refund_formula, solvency_mint, solvency_burn, round_trip_conservation, avg_price_formula, spot_lt_avg_price, spot_price_strict_mono and reserve_strict_mono.

## Assumptions and limitations

R is defined as a quadratic polynomial; no derivative or integral identity is formalized. The balance identities are consequences of reserve-difference definitions. They do not establish unconditional pool solvency, positive payouts, burn affordability or contract execution. Functions accept arbitrary real s and ds; there is no enforcement of nonnegative supply, positive trade size or ds≤s for burns. The average-price theorem excludes ds=0.

Round-trip conservation concerns one immediate mint-then-burn with identical parameters and no fees or intervening trades. It is not a general absence-of-arbitrage theorem, a statement about external markets, MEV or all execution paths. Prices and reserves use exact real arithmetic, not currency units or integer settlement.

Nonlinear price curves of degree at least two, fractional-power reserve-ratio/Bancor formulas, exponential curves, Solidity/EVM floor rounding, fixed-width arithmetic, dynamic mint/burn fees and correspondence with deployed Bancor or Pump.fun contracts are not formalized. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiBondingCurve.defi_bonding_curve_master_suite`.
