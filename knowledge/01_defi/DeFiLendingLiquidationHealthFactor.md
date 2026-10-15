---
id: DeFiLendingLiquidationHealthFactor
language: en
section: finance
source: Verification/DeFiLendingLiquidationHealthFactor.lean
source_sha256: a19620ed192419f6194179273b54c2ca33b547f34c20a4743a05f83e0ee3e4e1
novelty: not-assessed
status: reviewed
---

# Lending liquidation, health factor and conditional coverage

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingLiquidationHealthFactor.lean)

## Accounting and admission

The executable reference model uses rational arithmetic and a finite vector of
collateral quantities, positive collateral prices, thresholds LT and borrowing
weights LTV, with 0<=LTV<=LT<=1. Debt B is already valued in a common numeraire.
Valid positions allow zero quantities and zero debt. C=sum price*quantity,
W=sum LT*price*quantity and borrowLimit=sum LTV*price*quantity are distinct.
Borrowing admission B<=borrowLimit implies threshold safety and C>=B. A position
can be liquidatable (0<B and W<B) while still having C>=B.
`healthFactor` returns None at B=0 and Some(W/B) otherwise. None is a debt-free
status, not a numeric zero or an assertion that Lean division by zero is infinite.
Price monotonicity holds at fixed balances, thresholds and debt. Increasing B at
fixed collateral values decreases the ratio; simultaneous arbitrary price changes
are not ordered by this result.

`execute` checks validity, liquidation eligibility, positive repayment r, r<=B,
nonnegative bonus beta, a close factor in (0,1], r<=close*B and sufficient units
of the selected collateral k. It seizes s=(1+beta)*r/price_k, subtracts r from B,
and leaves prices, thresholds and borrowing weights unchanged. Full repayment is
an explicit branch and produces None health. Invalid inputs return None at the
transition level. `execute_success_iff` and `execute_spec` characterize admission
and post-state accounting. No configured Aave close-factor constant is assumed.

## Exact guarantees and counterexamples

For every successful partial step, with prices fixed during settlement,

    C' = C-(1+beta)*r
    W' = W-LT_k*(1+beta)*r
    B' = B-r
    HF'-HF = r*(HF-LT_k*(1+beta))/(B-r).

For 0<r<B, strict HF improvement is equivalent to HF>LT_k*(1+beta);
nondecrease uses >=. The single-collateral theorem specializes W=LT*C.
`real_health_bridge` connects positive scalar instances to the existing real
DeFiOvercollateralizedLending API. Multi-collateral health depends on which asset
is seized: a two-asset regression exhibits opposite health changes at the same r.

    C'-B' = C-B-beta*r
    C'>=B' iff beta*r<=C-B.

The base liquidation transition does not require this last condition and can
create a position deficit. For C=100,B=95,LT=4/5,r=50,beta=1/10 the health factor
falls from 16/19 to 4/5 while residual value coverage is exactly tight. For
beta=1/5 the same admissible base step leaves C'=40,B'=45. `executeCovered`
rejects it. This optional guard preserves valid position coverage, not pool-wide
solvency. `executeChain` composes guarded steps; induction proves coverage and
C_final-B_final=C_initial-B_initial-sum beta_t*r_t. The surplus is spent on bonuses,
not monotonically increased. Every successful prefix has the same guarantee.

## Integer execution and directed rounding

`DiscretePosition` has natural token quantities and natural numeraire debt units;
prices, LT, LTV, bonus and close factor remain exact rationals. This is an explicit
reference unit convention, not a token-decimal or multi-debt contract encoding.
`floorSeizure` rounds collateral units down. `ceilRepayment` rounds
price_k*requested_units/(1+beta) up and is the least natural repayment whose
bonus-inclusive value covers that exact requested payout. Both errors are in
[0,1) in their respective units. The rounding surplus stays with the borrower.

`executeFloor` and `executeCeil` use `executeDiscrete`, which checks the actual
integer repayment and seizure, debt and collateral caps, eligibility, close
factor and price_k*seizure<=(1+beta)*repayment. Natural subtraction is proved to
match rational subtraction under these caps; truncated subtraction cannot hide
a deficit. Zero repayment is rejected, and a one-unit repayment can yield a zero
floor payout. Full integer repayment produces debt-free None health.

The integer post-state is valid. The same conservative bonus-budget condition
beta*r<=C-B is sufficient for residual coverage; unlike exact settlement it is
not claimed necessary because rounding may retain additional collateral.
`executeDiscreteCovered` enforces that sufficient condition. The actual rounded
HF is at least the exact-seizure HF for the same r when debt remains positive.
Thus the stated HF nondecrease condition also suffices with downward payout.
No unconditional HF improvement is inferred from rounding.

## Validation and boundaries

48 kernel regression examples and 30 compiled scenarios cover no debt, zero and
negative repayment, invalid parameters, healthy positions, caps, two collateral
choices, complete repayment, a two-step chain, exact and inexact rounding,
minimal natural amounts and the two negative liquidation examples.
The suite is `DeFiLendingLiquidationHealthFactor.verification_suite`; it is
integrated in FinanceRiskFullSuite. Full measured results and source hashes are
recorded in tools/validation_snapshot.json. Source baseline:
e74d187fb7c0fe986ec7fd15af5bd6591f372736.

This is exact reference accounting, not an Aave implementation equivalence or
a proof of actual oracle truth, available market liquidity, slippage, MEV safety,
liquidator profitability or absence of system-wide bad debt. Interest accrual,
protocol fees, dynamic parameter governance, token decimals, machine overflow,
liquidation timing and production close-factor policies are not modeled.
Bulletproofs witness extraction, HVZK and Fiat-Shamir/ROM remain open, as do
Python, JSON/SHA-256 and SimLab correspondence obligations. Only propext,
Classical.choice and Quot.sound are permitted. Novelty is not assessed.

Reference: [Aave health factor and liquidations](https://aave.com/help/borrowing/liquidations).
