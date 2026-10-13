---
id: DistributedMarzulloEventSorting
language: en
section: distributed
source: Verification/DistributedMarzulloEventSorting.lean
source_sha256: 7992114ec99f30e122b4d689c66b1689427a35573764cde5568cda7cd48e9fc7
novelty: not-assessed
status: reviewed
---

# Stable merge sorting for Marzullo events

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedMarzulloEventSorting.lean)

## Executable model

`event_cmp` compares rational coordinates and then the boundary rank (start before
end). It deliberately ignores sourceId. `split_list` uses contiguous halves of
length ceil(N/2) and floor(N/2), preserving the order of equal keys. `merge_events`
returns both the merged list and the exact comparator-call count; every branch
with two nonempty inputs makes one call, and exhausting either input makes none.
`sort_counted` recursively sorts and merges with a depth budget. `merge_sort_events`
and `comparisons_count` project its result at depth Nat.clog 2 N. The output theorem
proves that this depth suffices and that the list equals Lean's library mergeSort.
No proof assumes that the input events are already sorted.

## Proved contracts

- `merge_sort_perm` preserves all event occurrences, including duplicates.
- `merge_sort_sorted` proves pairwise event ordering.
- `merge_sort_stable` preserves any fixed-key subsequence;
  `merge_sort_filter_key` proves exact equality of each key's filtered list.
- `merge_sort_eq_insertion_sort` proves literal equality to the existing insertion
  sort for the same event list. The proof uses stability under a total preorder;
  it does not assume antisymmetry for distinct source labels.
- `merge_events_count` bounds a merge by max(0, N-1) comparisons.
  `comparisons_count_recurrence` bounds the actual recursive counts on the two
  halves plus N-1 for N >= 2. `sort_counted_depth_irrelevant` proves that surplus
  depth changes neither the output nor its count.
- `comparisons_count_bound` proves C(xs) <= N * Nat.clog 2 N, including empty and
  singleton lists. `source_events_length` proves N=2n and
  `source_comparisons_bound` specializes the bound to n interval sources.

## Consensus backend and safety

The new `merge_sweep_overlap_count`, `merge_max_overlap`, `merge_peak_components`,
`merge_select_best_peak_component` and `merge_compute_threshold_hull` compute
using the merge-sorted event backend. Equality theorems connect these definitions
to module 154 without changing its existing API. Start-before-end observation
preserves closed-interval touching and point intervals.

`consensus_permutation_invariance` proves source-permutation invariance of the
counter function, maximum, selected peak and every threshold hull. It does not
claim equality of labeled event lists: zipIdx reassigns sourceId after a source
permutation. `merge_peak_optimal`, `merge_peak_contained`, `merge_fault_bound`,
`merge_hull_real_bridge` and `merge_hull_safe` transfer the prior optimality,
non-strict containment, fault bound and exact real thresholdHull specification.
The existing counterexample still applies: a selected peak can exclude true time,
whereas the safe hull contains it under FaultModel.

## Clean Water

The formal complexity statement counts comparator invocations in the defined
sorting recursion. It excludes rational numerator/denominator bit complexity,
fraction normalization, memory allocation, cache locality and parallel sorting.
It is not an O(n log n) bound for the complete consensus algorithm: repeated
queries, source intersections and peak/hull construction retain their separate
costs. Nor is this a benchmark or machine-code cost proof for Lean's optimized
library sorting backend. The implementation here computes its own counted recursion.

Full NTP, clock drift, network asymmetry and physical clock discipline remain
outside scope. Python, JSON/SHA-256 and SimLab correspondence obligations remain
open. Compiled regressions supplement kernel proofs without native-decide axioms.
Mathematical novelty is not assessed. Actual verification and axiom-audit results
are recorded in tools/validation_snapshot.json after the release checks.
