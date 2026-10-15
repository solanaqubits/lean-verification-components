---
id: DeFiLendingCompoundInterestIndex
language: en
section: finance
source: Verification/DeFiLendingCompoundInterestIndex.lean
source_sha256: 527cf034d023f69fe2e0981eec37e5de3afc904854d4a3402c6f39dd0c5be195
novelty: not-assessed
status: reviewed
---

# Debt-index accrual and explicit rounding reconciliation

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingCompoundInterestIndex.lean)

## Exact rational accounting

The index step is I'=I*(1+r*dt), with I>0, r>=0 and dt>=0. It stays positive and
cannot decrease. Zero rate or duration leaves it unchanged. A finite sequence is
I0 times the product of its interval factors. This is simple accrual within each
interval, compounded across updates; it is not continuous exponential accrual.
Two positive intervals at the same positive rate exceed a single combined step
by exactly I*r^2*dt1*dt2. Thus update frequency matters even at a constant rate.
The rate can be supplied by the nonnegative borrow curve from module 167.

PoolState stores nonnegative cash, reserves and supplier liabilities, a positive
index and nonnegative scaled borrower shares. Total debt is derived as
B=(sum shares)*I, rather than stored with an assumed consistency equation.
It equals the sum of individual debts. AccrueStep keeps cash and every scaled
share unchanged. Aggregate interest d=B*r*dt equals the sum of borrower increments.
Reserves increase by rho*d and supplier liabilities by (1-rho)*d, with 0<=rho<=1.

BorrowStep and RepayStep are separate transitions at a fixed index. Borrowing a
nonnegative amount a requires a<=cash, subtracts a from cash and adds a/I to the
selected borrower's scaled share. Repayment requires a<=that borrower's debt,
adds a to cash and subtracts a/I from the share. Full repayment is admitted.
Both preserve valid states and the accounting balance. Executable rational Option
interfaces are proved equivalent to the corresponding guarded transition predicates.
Conservation is a theorem of these updates, not a premise hidden in a transition.

For A=cash+B-R, accrual proves A'-A=(1-rho)*d>=0. The balance cash+B=R+L is
preserved from a balanced initial state. Positive net accounting assets do not
ensure unit-interval utilization: R'<=cash iff rho*d<=cash-R. With positive new debt
and denominator, this is also the exact condition for U'<=1 using module 167.
The concrete example cash=10,B=100,R=5,r=1/5,dt=1,rho=1/2 produces B'=120,R'=15:
A rises from 105 to 115 while U rises from 20/21 to 24/23, above one.

## Executable natural reference policy

The scale W is positive, the encoded rate is rate/W, dt is a natural number of
matching time units and the encoded reserve factor satisfies rho<=W. The checked
interface rejects zero scale, rho>W and a zero initial index. All multiplication
precedes division; natural numbers are unbounded:

    d = floor(B*rate*dt/W)
    I' = I + floor(I*rate*dt/W)
    reserve = floor(rho*d/W)
    supplier = d-reserve
    B' = B+d; R'=R+reserve; L'=L+supplier; cash'=cash.

The reserve allocation never exceeds d, so natural subtraction is exact.
Allocating the residual to suppliers preserves cash+B=R+L exactly in integers.
The index remains positive and nondecreasing; total debt does not decrease.
Integer interest is within one unit below its exact rational reference. Index
error after division by W is in [0,1/W), downward relative to the rational step
at the same encoded rate and initial index. Reserve-allocation error is in [0,1);
the supplier residual is within one unit above its exact allocation of the
already rounded interest. These local error bounds do not assert a global
uniform error bound over arbitrarily many updates or parameter quantization.

## Two distinct reconciliation quantities

Individual displayed debts are floor(b_i*I/W), and the index-derived aggregate is
floor((sum b_i)*I/W). Their difference recon_dust is nonnegative and at most n-1
for n>=1 and W>0. The empty case is zero. For W=10,I=15,two shares equal to one,
the aggregate is three but the two displayed debts sum to two. Four unit shares
at I=19,W=10 attain dust three. These are general quotient bounds with examples,
not conclusions inferred from a finite corpus.

An independently accrued integer debt ledger is a different quantity. Its signed
ledger_index_gap to the index-derived aggregate is explicit. The proved identity
is ledger debt minus summed individual debts = ledger_index_gap + recon_dust.
For W=10,I=1,one share 100,B=10,rate=1,dt=1, the ledger rises to eleven while the
index remains one and its derived debt remains ten. Dust is zero for one borrower,
but the separate gap is one. The n-1 bound must not be applied to that gap.

## Clean Water

These are bookkeeping and rounding guarantees. Debt recoverability, default
freedom, sufficient cash for withdrawals, market liquidity and overall economic
solvency do not follow. Liquidations, writeoffs, deposits/withdrawals, oracle truth,
governance updates, continuous-time dynamics, machine overflow and gas are not
modeled. No bit-exact refinement of deployed Compound or Aave contracts is claimed.

[Compound CToken accrueInterest](https://github.com/compound-finance/compound-protocol/blob/master/contracts/CToken.sol)
is a formula reference; this module defines its own explicit scaled-share and
supplier-liability bookkeeping. It does not claim that Aave uses the same interval
formula. All rates and durations must use matching units.

Tendermint accountability still needs complete observations or justification
evidence. Bulletproofs extraction, binding, HVZK, Fiat-Shamir/ROM, Python,
JSON/SHA-256 and SimLab correspondence remain open. Novelty is not assessed.
Only propext, Classical.choice and Quot.sound are permitted; tests do not formally
verify Python. See the [validation record](../VERIFICATION.en.md).

## Proof entry points

- [`accrue_index_pos`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L26)
- [`accrue_chain_product`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L46)
- [`subdivision_compounding_strict_gt`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L37)
- [`sum_debt_increments`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L74)
- [`net_assets_growth_identity`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L82)
- [`balance_sheet_conservation`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L95)
- [`accrue_step_invariants`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L148)
- [`borrow_step_invariants`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L179)
- [`repay_step_invariants`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L192)
- [`execute_accrue_iff`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L221)
- [`utilization_after_accrual_iff`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L247)
- [`utilization_exceeds_one_after_accrual_counterexample`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L254)
- [`accrue_discrete_spec`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L297)
- [`index_floor_error`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L322)
- [`supplier_split_error`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L341)
- [`recon_dust_bounds`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L369)
- [`ledger_reconciliation_identity`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L399)
- [`verification_suite`](../../Verification/DeFiLendingCompoundInterestIndex.lean#L431)
