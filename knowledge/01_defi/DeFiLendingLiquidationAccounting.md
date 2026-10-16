---
id: DeFiLendingLiquidationAccounting
language: en
section: finance
source: Verification/DeFiLendingLiquidationAccounting.lean
source_sha256: 674da0747fb1d8a7a4a97edfba80e945177265d2788272c28dcf8cbee302fc94
novelty: not-assessed
status: reviewed
---

# Liquidation accounting with separate debt and collateral ledgers

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingLiquidationAccounting.lean)

## Rational transition and admissibility

At fixed index I>0, borrower debt is scaled_i*I in debt-token units. Prices pd>0
and pc>0 use a common numeraire. The bridge to module 164 constructs a one-asset
Position with monetary debt pd*B_i and collateral value pc*C_i. The liquidation
threshold ell satisfies 0<ell<=1; liquidatable means ell*pc*C_i < pd*B_i with
positive monetary debt. The close factor alpha satisfies 0<alpha<=1.
Admission requires a valid nonnegative pool/collateral state, positive repayment
r, r<=B_i, r<=alpha*B_i and sufficient collateral for the seizure.

For B_i>0 and alpha<=1, B_i<=alpha*B_i iff alpha=1. This characterizes the
close-factor restriction on full repayment, not all admission conditions:
liquidatability and sufficient collateral must still hold. Zero debt admits no
positive liquidation. `admissible_health_factor_bridge` proves admission by the
module-164 interface with monetary repayment pd*r, rather than mixing token units.

The reference allocation is:

    base = r*pd/pc
    bonus = beta*base
    seized = base+bonus
    fee = phi*bonus
    liquidator = base+(1-phi)*bonus

For beta>=0 and 0<=phi<=1, base and liquidator are strictly positive and bonus and
fee are nonnegative. Liquidator+fee=seized exactly. Zero phi allocates the whole
bonus to the liquidator; phi=1 allocates only base to the liquidator; beta=0 makes
both bonus and fee zero. The fee-on-bonus convention is a mathematical reference
policy, not a bytecode refinement claim.

The debt-asset pool uses module 168's actual `transfer_debt`/`RepayStep`:
Cash'=Cash+r, scaled_i'=scaled_i-r/I; other shares and I remain fixed. Debt is
derived from the shares, so B'=B-r is proved. Reserves R and supplier liabilities
L are unchanged. Validity, Cash+B=R+L and net accounting assets Cash+B-R are
preserved from their stated initial hypotheses. Rational execution is proved
equivalent to input admission followed by this update.

The collateral asset has separate registers for the liquidator and treasury:
C_i'=C_i-seized, L_coll'=L_coll+liquidator, T_coll'=T_coll+fee. Their sum is
preserved; other borrowers' collateral is unchanged. Collateral fees are never
added to debt-asset R. Exchanging treasury collateral is a separate operation.

## Health factor is conditional

For a partial repayment 0<r<B_i at fixed positive prices, define
HF=ell*pc*C_i/(pd*B_i). The exact condition HF' >= HF is
ell*(1+beta)<=HF. Strict decline is equivalent to HF<ell*(1+beta).
With pd=pc=1, ell=3/4, beta=1/10, B_i=100 and r=20, C_i=120 gives
HF=9/10 and HF'=147/160 (improvement), whereas C_i=100 gives HF=3/4
and HF'=117/160 (decline). Both initial positions are liquidatable.
No unconditional improvement or solvency conclusion is asserted. These HF
comparisons exclude full repayment, where residual debt is zero.

## Executable natural arithmetic and rounding

The scale W and index I_int are positive. Token balances use smallest units;
pd/pc must already include token-decimal conversion, with a common price scale.
Threshold, close factor, bonus and fee fraction are encoded with scale W.
All products precede division and naturals are unbounded:

    base_int = floor(r*pd/pc)
    bonus_int = floor(beta_int*base_int/W)
    seized_int = base_int+bonus_int
    fee_int = floor(phi_int*bonus_int/W)
    liquidator_int = seized_int-fee_int

The checked Option transition rejects zero scale/index/prices, invalid threshold,
close factor or fee fraction, zero repayment, repayment exceeding the displayed
individual debt or independent pool ledger, exceeding floor(alpha_int*B_i_int/W),
a healthy position, or insufficient collateral. Liquidatability is checked by
cross multiplication, without a rounded HF quotient. The displayed individual
debt is floor(scaled_i*I_int/W); admission intentionally uses this rounded debt.

The fee is bounded by the rounded bonus; subtraction is therefore exact. Debt
cash increases by r and the independent debt ledger decreases by r. Both integer
asset-conservation laws are proved for successful execution. Reserves, supplier
liabilities, index and other borrowers' balances are unchanged.

Partial repayment burns floor(r*W/I_int) shares. The new scaled balance is above
its exact rational target by a value in [0,1) scaled unit. Full repayment of the
displayed debt burns all shares; the exact remaining scaled amount removed by
this special branch is in [0,W/I_int). This prevents a leftover share balance
but does not identify the independently maintained ledger with the index product.
A one-unit partial repayment can burn zero shares; the discrepancy is recorded,
not silently treated as exact repayment in the index representation.

Base, bonus and fee divisions each have error in [0,1) relative to their local
rational inputs. The total seizure is below the exact formula evaluated at the
encoded inputs by a value in [0,2+beta_int/W). These bounds do not include price
or parameter estimation error. The independent ledger/index gap has a proved
signed update law. Module 168's reconciliation identity and n-1 bound (n>=1)
apply to the sum of individually rounded balances at the fixed index, separately
from this gap. A one-borrower example has reconciliation dust zero and gap -1.

## Clean Water and validation

Accounting identities do not prove oracle accuracy or freshness, market liquidity,
absence of slippage/default, debt recoverability, withdrawal liquidity, overall
solvency, treasury exchange, actual token transfers or deployed-contract equivalence.
Machine overflow, gas and adversarial transaction ordering are not modeled.
Full Bulletproofs range extraction through multipoint interpolation, Tendermint
accountability with justification evidence, Python, JSON/SHA-256 and SimLab
correspondence remain open. Novelty is not assessed.

The regression file exercises partial/full liquidation, fee endpoints, zero bonus,
invalid guards, one-unit amounts and nonzero rounding. Tests do not verify Python.
See the [validation record](../VERIFICATION.en.md) for measured CLI results.
Only propext, Classical.choice and Quot.sound are permitted.

## Proof entry points

- [`full_repay_iff_close_factor_one`](../../Verification/DeFiLendingLiquidationAccounting.lean#L57)
- [`collateral_seize_split_identity`](../../Verification/DeFiLendingLiquidationAccounting.lean#L31)
- [`admissible_health_factor_bridge`](../../Verification/DeFiLendingLiquidationAccounting.lean#L429)
- [`scaled_debt_sum_preserved`](../../Verification/DeFiLendingLiquidationAccounting.lean#L138)
- [`rational_execution_spec`](../../Verification/DeFiLendingLiquidationAccounting.lean#L444)
- [`health_nondecreasing_iff`](../../Verification/DeFiLendingLiquidationAccounting.lean#L200)
- [`health_decreases_iff`](../../Verification/DeFiLendingLiquidationAccounting.lean#L208)
- [`execute_int_invariants`](../../Verification/DeFiLendingLiquidationAccounting.lean#L331)
- [`seize_int_error`](../../Verification/DeFiLendingLiquidationAccounting.lean#L367)
- [`partial_shares_rounding`](../../Verification/DeFiLendingLiquidationAccounting.lean#L383)
- [`full_shares_rounding`](../../Verification/DeFiLendingLiquidationAccounting.lean#L394)
- [`ledger_gap_update`](../../Verification/DeFiLendingLiquidationAccounting.lean#L411)
- [`post_liquidation_reconciliation`](../../Verification/DeFiLendingLiquidationAccounting.lean#L419)
- [`verification_suite`](../../Verification/DeFiLendingLiquidationAccounting.lean#L505)
