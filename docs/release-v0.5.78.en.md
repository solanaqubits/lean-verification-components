# Release v0.5.78 — conditional utilization feedback stability

This gamma release exports private snapshot
`8224e7cf8eaeeb5d9779618dfe7e6f36c36e0d92`. The previous public scoped release is
`b7494acdd830b6132406678265768803590f278f` (v0.5.77). The last fully validated
public baseline remains `b3410720b9af49c2fb70d15d65d3d012091cbf0b` (v0.5.73).
A scoped release does not advance that full-validation baseline.

## Mathematical scope

DeFiLendingUtilizationFeedbackStability uses module 167's rational KinkRateParams.
The real-valued rate extension agrees exactly with borrow_rate on rational
inputs. The prescribed feedback step is

    u_next = max(0, min(1, u + eta*(d-rate(u)) + noise)).

Projection is nonexpansive, and every projected output lies in [0,1]. For initial
values in that interval, all trajectory values remain there, for any noise and
step. This controller saturation is distinct from the accounting definition of
pool utilization, which can exceed one in module 167's model.

The coefficient kappa=max(|1-eta*slope1|,|1-eta*slope2|) bounds the unprojected
map across both affine regions, including crossings of the kink. Projection
preserves that bound. kappa<1 is equivalent to both 0<eta*slope_j<2. No ordering
of the two slopes is required. Zero slope prevents this coefficient from being
strictly less than one, without ruling out extra contraction from saturation.

For a specified fixed point of the zero-noise projected map and noise bounded by
epsilon, the module proves at every natural time:

    |u_t-u*| <= kappa^t*|u_0-u*| + epsilon*(1-kappa^t)/(1-kappa).

Under kappa<1, fixed points are unique and noiseless trajectories converge in
the real topology. A unit-interval point with rate(u*)=d is a fixed point;
projection can also create boundary fixed points without that equality.
The general theorems assume a specified equilibrium; no generic construction
of existence is claimed. Examples supply actual equilibria.

The rounding bridge reuses module 167's actual integer-rate error in [0,1/W)
at grid inputs u/W. Using that rounded rate is exactly equivalent to adding
-eta*rate_error to the disturbance. Separately bounded noise, rate error and
pre-projection update residual combine into epsilon + eta*er + eq for eta>=0.
Exact rational execution has cast theorems for the step and entire trajectory;
no floating-point implementation is assumed.

A linear rate with eta=1/2 converges to the specified equilibrium. Persistent
noise produces a nonzero stationary error. At eta=3, the trajectory from zero
alternates between zero and one and does not converge to 1/2. Projection still
keeps that counterexample bounded. Flat rates provide stationary counterexamples
to a general convergence guarantee without positive slopes.

## Integration and provenance

All 223 root-inclusive Lean sources match the private snapshot byte-for-byte.
MasterSuite has 180 direct imports. FinanceRiskFullSuite gains
`utilization_feedback` in MasterSuiteComponents. Root and registry imports,
AxiomAudit, the integration recipe, targeted tests and English knowledge cards
are synchronized. Russian cards are not exported. Version 0.5.78 is set before
validation. Toolchain, dependency pins, verifier and CI implementation are unchanged.

## Clean Water

This is conditional stability of a prescribed scalar feedback response, not
real market stability, liquidity or economic solvency. Economic response,
panic withdrawals and collateral adequacy remain external. Delays, varying
parameters, multivariable feedback, full machine rounding/overflow semantics
and deployed-bytecode equivalence are not proved. Remaining Bulletproofs protocol
extraction/security, Tendermint reference acquisition/slashing, Python equivalence,
JSON/SHA-256 and SimLab obligations remain separate. No novelty claim is made.

## Automatic CI scope

The existing push workflow runs full checks. After successful public-tree scoped
validation, this release uses the explicitly authorized `skip-checks: true`
commit trailer. A skipped workflow is not reported as a passing CI result.
Full gates remain for alpha/beta checkpoints; valid Lake caches are retained.
No duplicate standalone audit follows verify on unchanged inputs.

## Measured public validation

All required checks passed in this public tree with version 0.5.77 already set.

| Check | Measured result |
| --- | --- |
| `lake build --wfail` | 3861 incremental targets, no warnings; 12.169s |
| Module `verify` | 533 declarations in 4-source imported closure; 14.073s |
| MasterSuite `verify` | 25851 declarations in 217-source imported closure; 37.015s |
| Strict registry AxiomAudit | Passed; 2.507s |
| Module/registry unittest | 2 passed; 4.459s including startup |
| Existing registry unittest | 4 passed; 2.977s including startup |

All six selected tests ran with LEAN_VERIFIER_LIVE_TESTS=1, without errors or
skips. New regression files contain 38 kernel-checked examples (34 model checks and
4 registry checks), plus 22 executable scenarios with exact rational outcomes.
They cover projection, both kink branches and crossings, increasing/decreasing
slopes, convergence, persistent noise, boundary equilibria, large-step cycles,
flat rates, rational/real correspondence and a nonzero integer-rate residual.
Knowledge/catalog checks passed.

Both verifier reports have ok=true, source_unchanged=true, no policy findings
and no axiom violations. Only propext, Classical.choice and Quot.sound occur.
Declaration counts describe overlapping imported closures, not a new whole-project
measurement. Lake targets include cached work, not only freshly compiled proofs.
Full verify-all, the complete unittest suite and the independent full auditor
were not run for this gamma release.

[Machine-readable evidence](../tools/validation_v0.5.78.json) binds commands and
outcomes to source/configuration/test hashes. The last full public baseline
remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
