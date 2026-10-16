---
id: DeFiLendingBadDebtSocialization
language: en
section: finance
source: Verification/DeFiLendingBadDebtSocialization.lean
source_sha256: 27b14d9d71ebfacdbc6c1a2073a67abc454b0eafbb6c15db09cdd7a7e0adfecb
novelty: not-assessed
status: reviewed
---

# Authorized bad debt writeoff and supplier loss allocation

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingBadDebtSocialization.lean)

## Rational accounting contract

WriteOffAuthorized is an explicit Boolean decision supplied by the caller. The
module neither authenticates that decision nor derives economic uncollectibility
from zero collateral. The rational state reuses module 168's PoolState and adds
supplier shares S. At a fixed positive borrowing index I, the admission guards
require a nonnegative valid pool and S>=0, authorization, 0<=x<=B_i<=B,
h<=L and S=0 implies h=0. Here B_i=scaled_i*I and B=(sum scaled_i)*I.
The checked Option function is proved equivalent to these input guards and the
specified transition; failed authorization is rejected even for zero writeoff.

The policy is r=min(R,x), h=x-r=max(x-R,0). Exactly r+h=x, with
0<=r<=R and 0<=h<=x for nonnegative inputs. The update is Cash'=Cash,
B'=B-x, R'=R-r, L'=L-h. It preserves Cash+B=R+L whenever that balance held
initially. From that balance, Cash>=0, L>=0 and x<=B, the bound h<=L follows;
L>=0 is essential in this scalar lemma. The executable guard also checks h<=L
for states without an assumed balance. Rational validity is preserved.

Net accounting assets A=Cash+B-R satisfy A'=A-h. The following are equivalent:
x<=R, h=0, A'=A and L'=L. Positive socialized loss occurs iff x>R. Cash is
unchanged: reserve absorption is an allocation of accounting loss, not a cash
injection. No collateral or treasury conversion is inferred.

Only borrower i's scaled debt decreases by x/I; other scaled debts and I are
unchanged. The aggregate decreases by exactly x, preserving its indexed
representation. Supplier shares S also remain fixed. For S>0, e=L/S and
e'=(L-h)/S satisfy e-e'=h/S>=0 and e'=e iff x<=R. For S=0, positive haircut
is rejected. A reserve-covered writeoff with S=0 is admitted by this reference
policy; it does not assert that arbitrary supplier-share issuance is consistent.

## Exact integer split and separate rounding effects

The integer state reuses module 173's distinct debt and collateral registers.
Scale W and index I_int must be positive. Displayed individual debt is
floor(scaled_i*I_int/W); the independent total debt register must be at least this
individual debt. The function checks x<=B_i_int, h<=L and the zero-supplier-share
guard. Cash, collateral, liquidator collateral and treasury collateral are all
unchanged. Integer min/subtraction allocates the entire loss exactly and preserves
the balance from a balanced input. All subtractions are proved within bounds.
Casts to rationals agree exactly with the rational reserve/haircut split.

Zero writeoff burns no debt shares, including when positive shares display zero
debt. Positive partial writeoff burns floor(x*W/I_int) shares: the remaining
scaled balance exceeds its rational target by an error in [0,1). Positive full
writeoff of displayed debt clears all shares. The exact residual removed by this
branch is bounded in [0,W/I_int). A one-unit writeoff can burn zero shares.

The supplier price is Option-valued: no price is returned when S=0; otherwise it
is floor(L*W/S). Its error relative to the exact scaled price is in [0,1), and
it never increases on writeoff. The error in the difference between two rounded
prices lies strictly between -1 and 1 scaled price unit. These are arithmetic
bounds, not estimates of economic value. W and S are fixed in each comparison.

The signed independent debt-ledger/index gap has an exact update law. It is not
bounded by n-1: the n-1 bound (n>=1,W>0) concerns only reconciliation of the sum
of individually rounded debts against the aggregate at the same fixed index.
Both terms appear separately in the proved reconciliation identity. A one-borrower
example has gap -1 and reconciliation dust zero.

## Clean Water and validation

This formalizes an explicitly chosen accounting policy. Legal/economic grounds
for uncollectibility, decision authorization mechanisms, withdrawal liquidity,
overall economic solvency, external markets and deployed-code correspondence
remain outside scope. Compound III absorb, collateral transfers and subsequent
collateral sales require a separate model. Unbounded naturals do not model
machine overflow, gas or adversarial ordering.
Full Bulletproofs range extraction via multipoint interpolation, Tendermint
Accountable Safety with justification evidence, Python, JSON/SHA-256 and SimLab
correspondence remain open. Novelty is not assessed.

The regression suite has 56 kernel checks and 37 executable scenarios covering
reserve thresholds, zero reserves, complete supplier loss, one-unit amounts,
rounding and rejected guards. See the [validation record](../VERIFICATION.en.md)
for measured CLI results. Only propext, Classical.choice and Quot.sound are allowed.

## Proof entry points

- [`haircut_le_liabilities_of_balance`](../../Verification/DeFiLendingBadDebtSocialization.lean#L56)
- [`balance_sheet_preserved_on_writeoff`](../../Verification/DeFiLendingBadDebtSocialization.lean#L63)
- [`net_assets_after_writeoff`](../../Verification/DeFiLendingBadDebtSocialization.lean#L68)
- [`scaled_debt_consistency_on_writeoff`](../../Verification/DeFiLendingBadDebtSocialization.lean#L125)
- [`execute_invariants`](../../Verification/DeFiLendingBadDebtSocialization.lean#L171)
- [`lp_exchange_rate_preserved_iff`](../../Verification/DeFiLendingBadDebtSocialization.lean#L166)
- [`integer_split_cast`](../../Verification/DeFiLendingBadDebtSocialization.lean#L233)
- [`execute_int_invariants`](../../Verification/DeFiLendingBadDebtSocialization.lean#L276)
- [`partial_scaled_error`](../../Verification/DeFiLendingBadDebtSocialization.lean#L294)
- [`full_scaled_residual_bound`](../../Verification/DeFiLendingBadDebtSocialization.lean#L307)
- [`lp_rate_drop_error`](../../Verification/DeFiLendingBadDebtSocialization.lean#L329)
- [`post_writeoff_reconciliation`](../../Verification/DeFiLendingBadDebtSocialization.lean#L348)
- [`verification_suite`](../../Verification/DeFiLendingBadDebtSocialization.lean#L427)
