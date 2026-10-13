import Verification.DistributedMarzulloEventSorting

open DistributedMarzulloIntervalConsensus DistributedMarzulloEventSorting

example : DistributedMarzulloEventSortingSuite := DistributedMarzulloEventSorting.verification_suite
example : merge_sort_events [] = [] := by decide
example : comparisons_count [] = 0 := by decide
example (e : SweepEvent) : merge_sort_events [e] = [e] := by
  rw [merge_sort_eq_insertion_sort]; rfl
example (e : SweepEvent) : comparisons_count [e] = 0 := by simp [comparisons_count, sort_counted]
example (es : List SweepEvent) : (merge_sort_events es).Perm es := merge_sort_perm es
example (es : List SweepEvent) : (merge_sort_events es).Pairwise event_le := merge_sort_sorted es
example (es : List SweepEvent) : merge_sort_events es = es.insertionSort event_le :=
  merge_sort_eq_insertion_sort es
example (es : List SweepEvent) (x : ℚ) (k : BoundaryType) :
    (merge_sort_events es).filter (fun e => e.coord = x ∧ e.kind = k) =
    es.filter (fun e => e.coord = x ∧ e.kind = k) := merge_sort_filter_key es x k
example (es : List SweepEvent) : comparisons_count es ≤ es.length * Nat.clog 2 es.length :=
  comparisons_count_bound es
example (es : List SweepEvent) (h : 2 ≤ es.length) :
    comparisons_count es ≤ comparisons_count (split_list es).1 +
      comparisons_count (split_list es).2 + es.length - 1 := comparisons_count_recurrence es h
example (s : List RationalInterval) :
    comparisons_count (source_events s) ≤ (2 * s.length) * Nat.clog 2 (2 * s.length) :=
  source_comparisons_bound s
example (s : List RationalInterval) (x : ℚ) :
    merge_sweep_overlap_count s x = (overlap_count s x : ℤ) := sweep_count_invariant s x
example (s : List RationalInterval) (k : ℕ) :
    (merge_compute_threshold_hull s k).map embed =
      DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k := merge_hull_real_bridge s k
example {s t : List RationalInterval} (h : s.Perm t) :
    merge_select_best_peak_component s = merge_select_best_peak_component t :=
  (consensus_permutation_invariance h).2.2.1
example {s t : List RationalInterval} (h : s.Perm t) (k : ℕ) :
    merge_compute_threshold_hull s k = merge_compute_threshold_hull t k :=
  (consensus_permutation_invariance h).2.2.2 k

private def unit : RationalInterval := ⟨0, 1, by norm_num⟩
private def point : RationalInterval := ⟨1, 1, le_rfl⟩
private def touch : List RationalInterval := [unit, ⟨1, 2, by norm_num⟩]
private def tied : List SweepEvent :=
  [⟨1, .endPoint, 7⟩, ⟨1, .startPoint, 9⟩, ⟨1, .startPoint, 2⟩,
   ⟨1, .endPoint, 4⟩, ⟨1, .startPoint, 9⟩]
private def reverseEvents : List SweepEvent :=
  [⟨3, .startPoint, 0⟩, ⟨2, .startPoint, 1⟩, ⟨1, .startPoint, 2⟩, ⟨0, .startPoint, 3⟩]

example : (merge_sort_events tied).map SweepEvent.sourceId = [9, 2, 9, 7, 4] := by
  rw [merge_sort_eq_insertion_sort]; decide
example : (merge_sort_events reverseEvents).map SweepEvent.coord = [0, 1, 2, 3] := by
  rw [merge_sort_eq_insertion_sort]; decide
example : comparisons_count reverseEvents = 4 := by
  norm_num [comparisons_count, reverseEvents, sort_counted, split_list, merge_events,
    event_cmp, event_le, BoundaryType.rank, Nat.clog_of_two_le]
  rw [merge_events.eq_2 _ (by simp)]
  norm_num
example : merge_sweep_overlap_count touch 1 = 2 := by rw [sweep_count_invariant]; decide
example : merge_sweep_overlap_count [point] 1 = 1 := by rw [sweep_count_invariant]; decide
example : merge_sweep_overlap_count [unit, unit, unit] (1/2) = 3 := by
  rw [sweep_count_invariant]
  norm_num [overlap_count, contains, unit]
example : merge_sorted_events [unit, point] ≠ merge_sorted_events [point, unit] := by
  simp only [merge_sorted_events_eq]; decide
example : merge_sweep_overlap_count [unit, point] = merge_sweep_overlap_count [point, unit] :=
  (consensus_permutation_invariance (List.Perm.swap _ _ [])).1
example : merge_select_best_peak_component misleading_sources = some misleading_peak := by
  rw [merge_selection_eq]
  exact peak_not_necessarily_true_time_counterexample.2.2.1
example : merge_compute_threshold_hull misleading_sources 2 = some misleading_hull := by rw [merge_compute_threshold_hull_eq]; decide

private def runChecks : IO Unit := do
  let checks : List Bool := [
    decide (merge_sort_events [] = [] ∧ comparisons_count [] = 0),
    decide (comparisons_count (source_events [unit]) = 1),
    decide ((merge_sort_events tied).map SweepEvent.sourceId = [9, 2, 9, 7, 4]),
    decide ((merge_sort_events reverseEvents).map SweepEvent.coord = [0, 1, 2, 3]),
    decide (comparisons_count reverseEvents = 4),
    decide (merge_sweep_overlap_count touch 1 = 2),
    decide (merge_sweep_overlap_count [point] 1 = 1),
    decide (merge_sweep_overlap_count [unit, unit, unit] (1/2) = 3),
    decide (merge_select_best_peak_component misleading_sources = some misleading_peak),
    decide (merge_compute_threshold_hull misleading_sources 2 = some misleading_hull)]
  unless checks.all id do throw (IO.userError "Marzullo sorting regression failed")
  let many := (List.range 257).reverse.map fun i =>
    (⟨(i / 3 : ℕ), if i % 2 = 0 then .endPoint else .startPoint, i⟩ : SweepEvent)
  unless merge_sort_events many == many.insertionSort event_le do
    throw (IO.userError "Large stable-sort equivalence failed")
  unless comparisons_count many ≤ many.length * Nat.clog 2 many.length do
    throw (IO.userError "Comparison bound failed")
  IO.println "MARZULLO_SORT_EXEC_OK: 12 cases"

#eval runChecks
