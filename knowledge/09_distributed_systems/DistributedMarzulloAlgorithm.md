---
id: DistributedMarzulloAlgorithm
language: en
section: distributed
source: Verification/DistributedMarzulloAlgorithm.lean
source_sha256: a7c0b9c3f55e2be53a7cc5e90e567990295e699fbfc82172d5668f006ceef08d
novelty: not-assessed
status: reviewed
---

# DistributedMarzulloAlgorithm

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedMarzulloAlgorithm.lean)

## Model and result

The module specifies a static threshold envelope for a list of closed real intervals. `TimeInterval` requires `low ≤ high`, so singleton intervals are allowed. `supporters` counts source indices; identical interval values at different list positions remain distinct votes. `overlapCount_eq_filter_length` relates this count to filtering the original list.

For a threshold `k`, a point is feasible when its overlap count is at least `k`. `acceptedLows` and `acceptedHighs` retain source endpoints meeting that threshold. For a positive, feasible threshold, `thresholdHull` returns the interval from the least accepted lower endpoint to the greatest accepted upper endpoint. The endpoint-witness lemmas justify these finite extrema: every feasible point has an accepted lower endpoint below it and an accepted upper endpoint above it.

`thresholdHull_spec` states that the returned interval contains every feasible point and that both output endpoints are feasible. `thresholdHull_minimal` states that every other closed interval containing all feasible points also contains the returned interval. `thresholdHull_success_iff` characterizes success by positive threshold and nonempty feasibility; zero threshold and infeasible inputs return `none`.

## Fault assumptions and their consequences

Write `n = sources.length`. `FaultModel sources f t_true` assumes `f < n` and the existence of an indexed set `H` with at least `n - f` members, each enclosing the same specified `t_true`. The model assumes this enclosure property; it does not derive physical accuracy or source honesty from measurements.

`true_time_overlap_lower_bound` gives overlap at least `n - f` at `t_true`. Consequently, `marzullo_fault_tolerance_soundness` gives a successful threshold hull at `k = n - f` containing `t_true`. Under the stated enclosure assumption, `f < n` suffices for this containment; a strict majority is unnecessary for that theorem. `marzullo_intersection_nonempty` uses the assumed common witness to establish the honest intervals' nonempty intersection.

`threshold_shares_honest_source` has a different conclusion: for an explicit `H` satisfying the same size and enclosure conditions, any point supported by at least `k > f` sources shares an interval from `H` with `t_true`. At `k = n - f`, this requires `n - f > f`, equivalently `n > 2f`. It neither identifies that point with the truth nor applies automatically to every interior point of the output hull.

## Why maximum overlap is insufficient

`maximum_overlap_can_exclude_truth` uses two indexed copies of `[0,10]` and one interval `[8,9]`, with `f = 1` and `t_true = 1`. The two wide intervals form an honest strict majority. The truth has overlap `2`, whereas overlap `3` occurs exactly on `[8,9]`. Thus the unique maximum-overlap region excludes the truth despite the honest-majority assumption.

The threshold hull encloses all feasible components and can contain gaps of insufficient overlap. For example, `[0,1], [0,3], [2,3]` at threshold `2` has feasible set `[0,1] ∪ [2,3]`; its enclosing interval is `[0,3]`, while `3/2` has overlap `1`. This illustrates the distinction between an enclosing interval and the feasible set.

## Scope and dependencies

This is a noncomputable specification over exact real numbers with classical comparisons and finite endpoint extrema. It does not implement a sorted event sweep, certify an NTP implementation, or model time evolution, clock drift, message delays, fault detection, or repeated synchronization. No claim connects the abstract interval assumptions to physical clocks. The module has no direct imports of other `Verification` modules; its imports are from Mathlib.

[RFC 5905 §11.2.1](https://www.rfc-editor.org/rfc/rfc5905.html#section-11.2.1) provides application context through a modified Marzullo selection procedure. No equivalence with that procedure, its midpoint checks, or its changing fault budget is proved here. Mathematical novelty and priority of formalization are not assessed.

## Verification

The module passed `verify`, `audit`, and integration as `DistributedSystemsFullSuite.marzullo_algorithm`. Strict build, `verify-all`, independent axiom audit, all 35 public tests without skips, and catalog checks passed. Compiler regressions cover shared endpoints, a gap inside the envelope, a misleading maximum, repeated intervals, and impossible thresholds. See the [validation record](../VERIFICATION.en.md).
