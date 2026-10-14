---
id: DeFiConstantProductVirtualReserves
language: en
section: finance
source: Verification/DeFiConstantProductVirtualReserves.lean
source_sha256: 7aaf5c6490b10ae9aa135e5497f5ecabfe24276ba26667733846257a05d737cf
novelty: not-assessed
status: reviewed
---

# Constant product with virtual reserves and retained fees

[Section](../finance/README.md) · [Lean](../../Verification/DeFiConstantProductVirtualReserves.lean)

## State, exact execution and solvency

`VirtualReservesState` stores nonnegative rational real reserves x,y and fixed
nonnegative offsets alpha,beta with positive effective reserves X=x+alpha and
Y=y+beta. The product K=X*Y is an accounting invariant. The fee rate gamma lies
in [0,1), gross input d is nonnegative, and e=(1-gamma)*d. The exact output is
Y*e/(X+e). `remaining_identity` proves Y-o=X*Y/(X+e)>0.

`solvency_criterion_iff` proves o<=y iff beta*e<=y*X. Virtual positivity alone does
not imply real solvency. `execute_swap_x_to_y` is executable and returns None
for a negative input, invalid fee or failed solvency condition. Its exact success
criterion is proved. A successful result has x'=x+d,y'=y-o and unchanged offsets.

`invariant_growth_identity` proves K'=K+gamma*d*(Y-o). Thus K is nondecreasing,
strictly increasing for positive input and positive fee, and exactly conserved
for zero fee. These identities do not assume solvency; solvency is additionally
required to construct a valid post-state. `swapAxes` gives the reverse direction,
including a reverse solvency equivalence and growth identity. `execute_chain`
sequences actual Option-valued swaps in either direction, rejecting on failure.
Its induction proves K_final>=K_initial and unchanged offsets even with different
valid fees at each step. Applying the same theorem to any successful prefix gives
intermediate product bounds.

With a fixed fee, output strictly increases with nonnegative input and average
output per gross input decreases for positive inputs. `price_impact_average_rate`
excludes d=0. No such average-price monotonicity is asserted for arbitrary changing
fees; a regression demonstrates its failure. `real_quote_bridge` embeds the
rational effective-reserve quote into the pre-existing real CPMM API. That API's
gamma is the effective fraction, whereas this module's gamma is the fee rate.
The actual imported CPMM file is DeFiConstantProductSwap, not a new AMM alias.

## Natural execution and directed rounding

`DiscreteState` stores natural reserves and offsets. Its validity requires positive
sums x+alpha,y+beta. Fees remain rational; intermediate quote arithmetic is exact
rational arithmetic. `floor_div_output` and `ceil_div_input` return natural numbers
using executable floor/ceiling. No floating-point computation is used.

`discrete_swap_floor` checks state validity, fee validity and the exact rational
solvency condition before paying floor(o). This is intentionally conservative:
it may reject an exactly insolvent quote even when rounding would produce a
solvent zero payout. The payout never exceeds y, the new effective reserves remain
positive, offsets stay fixed, and the natural product cannot decrease.
`floor_output_error` proves 0<=o-floor(o)<1.

For a requested natural payout a with a<=y and a<Y, the exact gross input is
X*a/((1-gamma)*(Y-a)). `ceil_div_input` rounds that quantity up.
`ceil_input_error` proves 0<=ceil(input)-input<1, and `ceil_input_minimal` proves
that it is the least natural input whose exact quote covers a.
`discrete_swap_ceil` pays exactly a and collects that rounded input; it does not
pay a potentially larger recomputed quote. The rounding surplus remains in the
pool. The same validity and product guarantees hold. Exhausting y is allowed
when beta>0; exhausting Y requires infinite input and is rejected.

`discrete_step` implements both modes and both directions. `discrete_chain`
sequences the real executable transitions, and `discrete_chain_monotone` proves
validity and nondecreasing product through any successful finite sequence.
Natural subtraction is used only after proving the payout is at most the real
reserve, so truncation cannot hide a deficit.

## Validation and boundaries

The suite is `DeFiConstantProductVirtualReserves.verification_suite`. The test
wrapper covers 24 kernel assertions and 25 compiled cases: zero input, one wei,
exact division, exact reserve exhaustion, fees, both directions/modes, rejected
invalid inputs/states, multiple steps and a changing-fee counterexample.
Source reference snapshot: 59ec88ee2ce6cf6f9ff5a51a586fc067dabef630. Actual CLI results,
source hashes and full-project metrics are recorded in tools/validation_snapshot.json.
Only propext, Classical.choice and Quot.sound are allowed.

Fees are included in trading reserves. This is a shifted CPMM reference model,
not Uniswap v3 fee accounting, where collected fees are separate from active
liquidity. Fixed offsets do not model tick crossings, liquidity changes or a full
pool lifecycle. Exact Solidity/EVM correspondence, machine overflow, optimized
integer implementations and gas bounds are excluded.

Nondecreasing product does not establish external-price market-value preservation,
absence of arbitrage, MEV/sandwich protection or economic returns. Those claims are
not proved. Bulletproofs witness extraction, HVZK and Fiat-Shamir/ROM remain open;
this unrelated module does not close them. Python, JSON/SHA-256 and SimLab
correspondence obligations remain open. Novelty is not assessed.

Reference: [Uniswap v3 whitepaper, shifted reserves and separate fee accounting](https://app.uniswap.org/whitepaper-v3.pdf).

[`solvency_criterion_iff`](../../Verification/DeFiConstantProductVirtualReserves.lean#L63) · [`invariant_growth_identity`](../../Verification/DeFiConstantProductVirtualReserves.lean#L76) · [`price_impact_average_rate`](../../Verification/DeFiConstantProductVirtualReserves.lean#L116) · [`execute_success_iff`](../../Verification/DeFiConstantProductVirtualReserves.lean#L151) · [`dynamic_fee_chain_monotone`](../../Verification/DeFiConstantProductVirtualReserves.lean#L189) · [`ceil_input_minimal`](../../Verification/DeFiConstantProductVirtualReserves.lean#L239) · [`discrete_chain_monotone`](../../Verification/DeFiConstantProductVirtualReserves.lean#L384) · [`verification_suite`](../../Verification/DeFiConstantProductVirtualReserves.lean#L470)
