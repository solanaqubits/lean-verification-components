---
id: DeFiOvercollateralizedLending
language: en
section: finance
source: Verification/DeFiOvercollateralizedLending.lean
source_sha256: 37ef8795e3103e7e56c6508867c7257fb9172e63c7e62794ffcb9697ade01743
novelty: not-assessed
status: reviewed
---

# DeFiOvercollateralizedLending

[Section](../finance/README.md) · [Lean](../../Verification/DeFiOvercollateralizedLending.lean)

## Verified result

For positive collateral C, debt D, both prices Pc,Pd and 0<LT<1, the values Vc=C*Pc and Vd=D*Pd and the health factor HF=Vc*LT/Vd are positive. HF≥1 implies Vd<Vc. Adding positive collateral strictly raises HF; adding positive debt strictly lowers HF, with both prices and LT unchanged.

The prescribed seized collateral (repaidDebt*Pd*(1+bonus))/Pc has value exactly repaidDebt*Pd*(1+bonus). If Vd*(1+bonus)≤Vc, seizure for full debt repayment is at most C. The interface retains a nonnegative-bonus assumption, although this last implication only needs positive Pc and the coverage premise.

Key theorems: health_factor_pos, safe_position_strictly_solvent, add_collateral_increases_hf, borrow_more_decreases_hf, liquidation_seized_collateral_value and full_liquidation_collateral_sufficient.

## Assumptions and limitations

These are exact real-arithmetic results for one position, not a contract execution or pool-wide solvency proof. Safe means threshold coverage, and HF<1 does not necessarily mean Vd>Vc. Strict solvency depends on LT<1. BorrowMore has no admission check ensuring that its result remains safe. The model excludes zero debt and therefore does not construct a debt-free post-liquidation position.

The seizure-value identity allows arbitrary real repayment and bonus; it imposes no positivity, repayment cap or liquidation trigger. Full-liquidation sufficiency explicitly assumes bonus-inclusive coverage and does not derive it from isSafe or isLiquidatable. It does not guarantee successful execution, restoration of HF or prevention of bad debt.

Utilisation-dependent or kink interest rates, close-factor partial-liquidation limits, stale/crashed oracle prices, bad-debt socialisation, integer rounding and correspondence with Aave, Compound or Maker/Sky contracts are not formalized. Scientific novelty has not been assessed.

## Verification

[Validation](../VERIFICATION.en.md). Entry point: `DeFiOvercollateralizedLending.defi_overcollateralized_lending_master_suite`.
