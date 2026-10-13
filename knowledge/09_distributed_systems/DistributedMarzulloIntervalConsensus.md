---
id: DistributedMarzulloIntervalConsensus
language: en
section: distributed
source: Verification/DistributedMarzulloIntervalConsensus.lean
source_sha256: ad3e965849e9366ffa466f981c99e4d35dd7aa27ea181117bf07ea4c59ff5db9
novelty: not-assessed
status: reviewed
---

# Executable rational interval agreement

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedMarzulloIntervalConsensus.lean)

## Model and algorithm

`RationalInterval` has rational endpoints with left ≤ right. Sources are indexed
by list position: identical intervals remain distinct votes. `source_events`
creates a start and end for each source. `sorted_events` uses executable insertion
sort by coordinate, with starts before ends at equal coordinates.

`sweep_counters` makes an accumulating prefix-sum pass with integer increments
+1 and -1. `sweep_overlap_count` observes the table after all starts at a coordinate
and before any ends there; `grouped_observations` removes duplicate coordinates.
`sweep_counter_step`, `events_sorted`, `sweep_overlap_count_correct` and
`grouped_observation_correct` prove the arithmetic and observation semantics.
No asymptotic complexity bound is claimed: insertion sorting, prefix lookup and
construction of source intersections are not a certified O(n log n) implementation.

`max_overlap` maximizes endpoint observations. Every real feasible point has a
rational source endpoint with at least its support. At a peak, `support_span`
intersects its supporting sources. `peak_components` enumerates these spans at
accepted lower endpoints and removes duplicate intervals. Gap-witness lemmas
prove their maximality, not merely that they are constant-overlap subintervals.
`mem_peak_components_iff` and `peak_components_cover` prove exactness and coverage.
These are maximal order-convex intervals over Q, not topological connected
components of Q. Their real counterparts have the intended interval meaning.

`select_best_peak_component` minimizes the lexicographic key (length, left endpoint).
`best_peak_uniquely_optimal`, `interval_order_iff` and `best_peak_exists` establish
unique optimality and existence for nonempty input. `selection_permutation` and
`hull_permutation` show independence of source enumeration. Empty input gives
peak 0 and no selected interval or finite hull. Threshold 0 also returns none.

## Safety bridge and counterexample

`algorithmic_hull_matches_marzullo_hull` equates the embedded algorithmic result
with the existing real `thresholdHull` for every input and threshold, including
failure cases. `rat_to_real_embedding_preserves_membership` and
`embedding_preserves_overlap` give the scalar bridges. True time may be irrational.
The existing `FaultModel` supplies at least n-f honest intervals containing it
and assumes f < n. `max_overlap_ge_fault_bound` proves M ≥ n-f;
`algorithmic_hull_contains_true_time` transfers the safety theorem to the algorithm.

`peak_component_subset_threshold_hull` proves non-strict inclusion for any positive
threshold at most M. Proper inclusion is not guaranteed. For sources [0,10],
[0,1], [8,10], f=1 and true time 9, the peak is 2. The shortest component [0,1]
excludes truth while the level-2 hull [0,10] contains it. The first and third
sources witness the honest set. Peak components and safety hulls have different
contracts; the hull may include gaps with insufficient support.

## Clean Water

This is exact rational arithmetic and an exact bridge to a static real interval
specification. The suite does not certify full NTP (RFC 5905 A.5.5.1), midpoint
selection, outlier/jitter filtering, oscillator drift, network asymmetry, PLL/FLL,
or physical clock discipline. Python, JSON/SHA-256 and SimLab correspondence
obligations remain open. Compiled execution regressions complement kernel proofs
and introduce no axioms; no native-decide proof shortcut is used.

Mathematical novelty is not assessed. Module verify/audit and full-project checks
are recorded in tools/validation_snapshot.json after completion.

Reference: [RFC 5905, A.5.5.1](https://www.rfc-editor.org/rfc/rfc5905.html#appendix-A.5.5.1)
is related protocol context, not a claim of full RFC conformance.
