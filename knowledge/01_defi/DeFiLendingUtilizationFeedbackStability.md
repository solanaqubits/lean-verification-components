---
id: DeFiLendingUtilizationFeedbackStability
language: en
section: finance
source: Verification/DeFiLendingUtilizationFeedbackStability.lean
source_sha256: 781c96a6c593c8a2fb21a659ca9a57730edc6403bcdc0a829c1d8d1511f54b36
novelty: not-assessed
status: reviewed
---

# Conditional utilization stability under a prescribed feedback law

[Section](../finance/README.md) · [Lean](../../Verification/DeFiLendingUtilizationFeedbackStability.lean)

## Model and bridge to module 167

Parameters are the existing rational KinkRateParams. rate is their real-valued
piecewise-affine extension, not a different interest model. rate_rat proves exact
agreement with borrow_rate on every rational input. Both slopes are nonnegative;
no ordering between them is required. The reserve factor is not part of this
borrow-rate feedback law.

project_unit(x) = max(0,min(1,x)). The update is
u_next = project_unit(u + eta*(d-rate(u)) + noise).
Here d, eta and noise are external scalar inputs. This feedback response is a
chosen mathematical model; it is not derived from borrower behavior or the
Cash/B/Reserves accounting transitions. In particular, projection is explicit
saturation of this controller, not a claim that all valid pool states have
utilization <= 1 (module 167 includes a counterexample).

## Verified bounds

project_unit_bounds proves the output lies in [0,1] for any input.
project_unit_nonexpansive proves |project(x)-project(y)| <= |x-y|; the projection
alone is not strictly contractive. trajectory_invariant keeps every iterate in
[0,1] when the initial value is in that interval, for arbitrary noise and step.

kappa = max(|1-eta*slope1|,|1-eta*slope2|).
raw_step_lipschitz proves this bound for the unprojected map, including crossings
of the kink, by splitting at the common affine-branch junction. feedback_lipschitz
then applies nonexpansiveness of projection, for the same disturbance in both
trajectories. feedback_noise_bound separately bounds sensitivity to disturbance.

kappa_lt_one_iff proves the exact criterion for this coefficient:
0 < eta*slope1 < 2 and 0 < eta*slope2 < 2.
suitable_step_contracts supplies a convenient sufficient condition: eta>0,
both slopes positive and eta*max(slope1,slope2)<2. A zero slope makes this
coefficient at least one. This does not rule out additional contraction caused
by saturation on a restricted domain.

IsEquilibrium means a fixed point of the zero-noise PROJECTED map.
A unit-interval point satisfying rate(u*)=d is such an equilibrium;
projection can also create boundary equilibria with rate(u*) different from d.
equilibrium_unique proves uniqueness under kappa<1. The general stability
statements assume a specified fixed point; no generic existence construction
is needed or claimed. The concrete examples supply actual equilibria.

bounded_perturbation_stability proves, at every natural time t,

    |u_t-u*| <= kappa^t*|u_0-u*| + epsilon*(1-kappa^t)/(1-kappa)

under kappa<1, the fixed-point equation and |noise_t|<=epsilon at every time.
The zero-noise specialization gives geometric error decay. noiseless_converges
proves actual Tendsto convergence over the reals, not just a finite prefix test.
The bound holds for arbitrary initial real u0; the [0,1] invariant additionally
requires the initial point in [0,1].

## Rounding and executable correspondence

combined_disturbance_bound and rounding_and_noise_stability use the exact residual
noise_t - eta*rate_error_t + update_residual_t. For eta>=0 and separate bounds
epsilon, er, eq, the total disturbance is bounded by epsilon + eta*er + eq.
The update residual is an explicitly bounded input BEFORE projection; this
statement does not automatically certify arbitrary machine arithmetic.

fixed_rate_error reuses module 167's borrow_rate_int_error. At an integer grid
input u/W, the normalized upward-rounded borrow rate has error in [0,1/W).
rounded_rate_step_identity proves that using this rate in the real update is
exactly equivalent to adding -eta*fixed_rate_error to the disturbance. The
reference uses unbounded natural numbers; no machine overflow or complete
fixed-point implementation of the dynamic controller is asserted.

project_rat, feedback_rat and trajectory_rat are executable exact-rational
versions. Their cast theorems identify each rational step and complete finite
trajectory with the real model. No floating-point approximation is hidden in
these executable examples.

## Nonvacuous results and regressions

linearModel has rate(u)=u. At eta=1/2, d=1/2, kappa=1/2 and every zero-noise
trajectory converges to 1/2. With persistent noise 1/8, the point 3/4 stays fixed,
showing a nonzero steady error. With eta=3, the orbit from zero alternates exactly
between zero and one; its distance from 1/2 stays 1/2 and it does not converge to
that equilibrium. Projection still keeps this unstable feedback example bounded.
flatModel at d=0 leaves every initial unit-interval point unchanged.

Regressions also cover increasing/decreasing slopes, crossing the kink, boundary
equilibria, large disturbances, and an actual nonzero integer-rate residual:
W=10, integer input 3, exact rate 9/100, rounded rate 1/10, error 1/100.
The Python harness checks 22 named exact-rational executable scenarios.

## Clean Water and validation provenance

The result is conditional mathematical stability of a prescribed scalar response.
Real market response, panic withdrawals, collateral adequacy, secondary-market
liquidity and economic solvency are external. Time delays, varying parameters,
vector feedback, deployment/bytecode equivalence and full machine rounding
semantics are not proved. Remaining Bulletproofs protocol extraction/security,
Tendermint reference acquisition/slashing, Python equivalence, JSON/SHA-256 and
SimLab obligations remain separate. Mathematical novelty is not assessed.

Public gamma release v0.5.78 exports private snapshot
8224e7cf8eaeeb5d9779618dfe7e6f36c36e0d92. The previous public scoped release is
b7494acdd830b6132406678265768803590f278f (v0.5.77). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.78.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.
