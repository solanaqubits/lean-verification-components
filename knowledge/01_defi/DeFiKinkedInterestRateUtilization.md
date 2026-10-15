---
id: DeFiKinkedInterestRateUtilization
language: en
section: finance
source: Verification/DeFiKinkedInterestRateUtilization.lean
source_sha256: 22c131e0aaa540d1909207ee242c0ded7119d2f4fd7e73c339511311f11fedd8
novelty: not-assessed
status: reviewed
---

# Kinked utilization rates and directed rounding

[Section](../finance/README.md) · [Lean](../../Verification/DeFiKinkedInterestRateUtilization.lean)

## Exact model and admission

All curve parameters and reference calculations are rational. Cash, borrows B and
reserves are nonnegative. If B=0, utilization is explicitly zero; the unused
D=Cash+B-Reserves need not be positive. If B>0, ValidPoolState requires D>0.
checked_utilization returns none outside this domain. The total raw formula is
not an economic interpretation of division by zero.

For B>0,D>0, utilization is positive and U<=1 iff Reserves<=Cash. Positive D alone
does not ensure this: Cash=10,B=100,Reserves=20 gives U=10/9. The exact reserve/cash
condition matters even when rounding would hide a small excess over one.

KinkRateParams requires r0,s1,s2>=0, 0<k<1 and 0<=rho<=1. The borrow curve is
r0+s1*u below and at k, and r0+s1*k+s2*(u-k) above k. Both branches coincide at k.
The hinge representation proves topological continuity over Q for every admitted
pair of slopes. The curve is monotone on all Q and nonnegative for u>=0.
If s1<=s2 it is the maximum of two affine functions and is ConvexOn Q univ;
this is a Jensen convexity theorem, not merely branch agreement. Exact increments
on either side identify the slopes. A regression with decreasing slopes preserves
monotonicity while violating convexity.

The supply curve is rs=u*(1-rho)*rb. It is nonnegative and nondecreasing for u>=0
at fixed parameters. On 0<=u<=1, 0<=rs<=rb and

    rb-rs = rb*(1-u*(1-rho)).
    rs<rb iff rb>0 and u*(1-rho)<1.

At u=1,rho=0 the spread is zero. At rho=1 the supply rate is zero. A zero borrow
curve never has a strictly positive spread. No rate period conversion is assumed;
all parameters refer to the same fixed time unit.

## Executable fixed-point algorithm

FixedParams stores natural scale W>0, base, slopes, kink and reserve factor.
It requires 0<kink<W and reserveFactor<=W. Dividing each encoded parameter by W
produces the proved rational parameter structure. Natural numbers are unbounded.
The algorithm fixes the operation order as follows, with u the encoded utilization:

    u = floor(W*B/(Cash+B-Reserves))         (separate B=0 branch)
    C = base*W + slope1*min(u,kink) + slope2*(u-kink)
    rbInt = ceil(C/W)
    rsInt = floor(u*(W-reserveFactor)*rbInt/(W*W)).

The subtraction u-kink is natural truncated subtraction, used only as a positive
part of the hinge. The reserve subtraction is exact because reserveFactor<=W.
ceil_div is natural division plus one precisely when the remainder is nonzero.
utilization_int rejects W=0 or a nonpositive denominator for positive debt.
quote_rates additionally checks Reserves<=Cash or B=0 and returns (u,rbInt,rsInt).
Its successful-result specification proves u<=W and rsInt<=rbInt.

This is a reference rounding policy: one upward rounding for the entire borrow
numerator and one downward rounding for supply. It is not a bit-exact reproduction
of Compound's intermediate floor divisions or Aave's implementation. Machine-word
overflow and gas costs are not modeled.

## Quantitative error guarantees

Write uHat=u/W, bHat=rbInt/W and sHat=rsInt/W. The following bounds are proved:

    0 <= U-uHat < 1/W;
    0 <= bHat-rb(uHat) < 1/W;
    -1/W < sHat-rs(uHat) < 1/W                 (u<=W).

The supply floor relative to the already rounded borrow input has a one-sided
error in [0,1/W). Its net error relative to the exact borrow curve can have either
sign. For L=max(s1,s2), the full borrow error against unquantized U satisfies

    -L/W <= bHat-rb(U) < 1/W.

For admitted unit-interval states and S=(1-rho)*(rb(1)+L), the full supply error is

    -(S/W+1/W) < sHat-rs(U) < 1/W.

These compare against the exact rational lift of the same encoded parameters;
parameter quantization from some other real-valued curve is not included.
They include utilization quantization, not just the final division. The growth
bounds cover intervals crossing the kink. The integer rate-order theorem is
proved for every u<=W, not only the finite regression corpus.

## Regression coverage

Kernel checks and executable scenarios cover zero debt, zero/negative effective
denominators, all three kink regions, full utilization, reserve factors zero/one,
zero curves, decreasing slopes, one-wei input, exact/remainder divisions and U>1.
For W=1000, Cash=0,B=10001,Reserves=1, utilization_int returns 1000 but quote_rates
rejects the state: admission uses the exact condition, not the rounded quotient.
The runtime suite uses the actual natural algorithms and checks concrete outputs.

## Clean Water

Rate order is an instantaneous algebraic property under fixed parameters. It does
not prove pool-wide solvency, absence of default, availability of withdrawable
cash or protection against liquidity crunches. Compound interest, debt indices,
bad-debt writeoffs, reserve dynamics and governance parameter changes require
separate state-transition models. Market and oracle correctness, MEV and deployed
contract refinement are outside scope.

Tendermint accountable safety still requires a complete observation/justification
contract for Amnesia. Bulletproofs extraction, computational binding, HVZK,
Fiat-Shamir/ROM and external Python, JSON/SHA-256 and SimLab correspondence remain
open. Scientific novelty is not assessed. Kernel proofs use only propext,
Classical.choice and Quot.sound; executable tests do not formally verify Python.
See the [validation record](../VERIFICATION.en.md) for measured checks.

[Compound BaseJumpRateModelV2](https://github.com/compound-finance/compound-protocol/blob/master/contracts/BaseJumpRateModelV2.sol)
is a reference for the utilization and piecewise rate formulas, not an asserted
implementation equivalence. The present slopes are direct slopes in utilization;
no annual-rate constructor normalization is imported.

## Proof entry points

- [`utilization_le_one_iff`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L47)
- [`utilization_in_unit_interval`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L53)
- [`utilization_gt_one_counterexample`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L67)
- [`borrow_rate_continuous`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L123)
- [`borrow_rate_monotone`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L104)
- [`borrow_rate_convex_slope`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L140)
- [`supply_rate_monotone`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L172)
- [`rate_spread_identity`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L178)
- [`strict_spread_iff`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L190)
- [`ceil_div_bounds`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L217)
- [`borrow_numerator_spec`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L277)
- [`utilization_int_error`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L388)
- [`borrow_rate_int_error`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L299)
- [`supply_rate_int_error`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L354)
- [`borrow_rate_total_error`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L484)
- [`supply_rate_total_error`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L519)
- [`quote_rates_spec`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L444)
- [`quote_rates_preserves`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L460)
- [`verification_suite`](../../Verification/DeFiKinkedInterestRateUtilization.lean#L603)
