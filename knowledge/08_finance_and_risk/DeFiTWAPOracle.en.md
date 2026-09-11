---
id: DeFiTWAPOracle
language: en
section: finance
source: Verification/DeFiTWAPOracle.lean
source_sha256: 8e444f00451a648e2c06962e2a282a1867a20bc4ff5c1118a5bd496564de0f2c
novelty: not-assessed
status: reviewed
---

# DeFiTWAPOracle

[Section](../finance/README.md) · [Lean](../../Verification/DeFiTWAPOracle.lean)

## Verified result

A strictly ordered time window has positive, nonzero duration. Dividing a supplied accumulator increment P * duration by that duration returns P. For a baseline P0 and a spike P_spike lasting dt_spike within totalT, the specified two-period arithmetic average differs from P0 by exactly (dt_spike / totalT) * (P_spike - P0).

## Assumptions and limitations

The displacement identity assumes totalT > 0 and retains 0 ≤ dt_spike ≤ totalT as physical domain conditions; those latter inequalities are not needed for the algebraic equality. Prices and accumulator observations are arbitrary real numbers. The weighted-average lemma is a definitional identity, not a theorem deriving accumulator composition from a price history. No integral, continuous-time process, observation sampling or block transition is modeled.

The identity provides duration weighting, not an absolute manipulation bound without a bound on the spike price. Flash-loan resistance, attack costs, timestamp control, uint256 modular wrap-around, integer rounding, and the logarithmic/geometric TWAP of Uniswap v3 are not formalized. This module does not verify a deployed oracle.

## Value and novelty

Reusable scalar checks for an arithmetic accumulator and a single-spike scenario. Mathematical novelty and first-formalization status are not assessed.

## Verification

[Validation record](../VERIFICATION.en.md). Entry point: `DeFiTWAPOracle.defi_twap_master_verification_suite`. The weighted-average lemma is checked as a module declaration but is not a field of the supplied suite.
