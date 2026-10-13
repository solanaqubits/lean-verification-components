/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedMarzulloIntervalConsensus
import Mathlib.Data.Nat.Log

/-!
# Stable event sorting with an executable comparison counter

The count records one Boolean comparator call at each nonempty merge branch.
Rational bit complexity and the cost of the rest of interval consensus are separate.
-/

namespace DistributedMarzulloEventSorting
open DistributedMarzulloIntervalConsensus

/-- Ties deliberately ignore source labels. -/
def event_cmp (a b : SweepEvent) : Bool := decide (event_le a b)

theorem event_trans (a b c : SweepEvent) (h : event_le a b) (h' : event_le b c) :
    event_le a c := by
  unfold event_le at *
  rcases h with h | ⟨h, hk⟩ <;> rcases h' with h' | ⟨h', hk'⟩
  · exact Or.inl (lt_trans h h')
  · exact Or.inl (h' ▸ h)
  · exact Or.inl (h ▸ h')
  · exact Or.inr ⟨h.trans h', hk.trans hk'⟩

theorem event_total (a b : SweepEvent) : event_le a b ∨ event_le b a := by
  unfold event_le
  rcases lt_trichotomy a.coord b.coord with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.kind.rank b.kind.rank with hk | hk
    · exact Or.inl (Or.inr ⟨h, hk⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hk⟩)
  · exact Or.inr (Or.inl h)

private theorem cmp_trans : ∀ a b c, event_cmp a b → event_cmp b c → event_cmp a c := by
  simpa [event_cmp] using event_trans
private theorem cmp_total : ∀ a b, event_cmp a b || event_cmp b a := by
  simpa [event_cmp] using event_total

/-- Contiguous splitting is essential for stability. Left gets the odd element. -/
def split_list (xs : List SweepEvent) : List SweepEvent × List SweepEvent :=
  (xs.take ((xs.length + 1) / 2), xs.drop ((xs.length + 1) / 2))

/-- Output and exact number of comparator calls, computed together. -/
def merge_events : List SweepEvent → List SweepEvent → List SweepEvent × ℕ
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if event_cmp x y then
      let r := merge_events xs (y :: ys)
      (x :: r.1, r.2 + 1)
    else
      let r := merge_events (x :: xs) ys
      (y :: r.1, r.2 + 1)
termination_by xs ys => xs.length + ys.length

theorem merge_events_output (xs ys : List SweepEvent) :
    (merge_events xs ys).1 = List.merge xs ys event_cmp := by
  fun_induction merge_events xs ys <;> dsimp +zetaDelta at * <;>
    simp_all only [List.merge, Bool.false_eq_true, ↓reduceIte]

theorem merge_events_length (xs ys : List SweepEvent) :
    (merge_events xs ys).1.length = xs.length + ys.length := by
  rw [merge_events_output, List.length_merge]

/-- Even a singleton exhausted side does not incur an extra comparison. -/
theorem merge_events_count (xs ys : List SweepEvent) :
    (merge_events xs ys).2 ≤ xs.length + ys.length - 1 := by
  fun_induction merge_events xs ys <;> dsimp +zetaDelta at * <;> omega

/-- Fuel limits depth only. At ceil(log₂ length), all leaves have length at most one. -/
def sort_counted : ℕ → List SweepEvent → List SweepEvent × ℕ
  | 0, xs => (xs, 0)
  | fuel + 1, xs =>
    if xs.length ≤ 1 then (xs, 0) else
      let halves := split_list xs
      let left := sort_counted fuel halves.1
      let right := sort_counted fuel halves.2
      let merged := merge_events left.1 right.1
      (merged.1, left.2 + right.2 + merged.2)

theorem sort_counted_length (fuel : ℕ) (xs : List SweepEvent) :
    (sort_counted fuel xs).1.length = xs.length := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    simp only [sort_counted]
    split_ifs
    · rfl
    · simp only [merge_events_length, ih, split_list, List.length_take, List.length_drop]
      omega

theorem sort_counted_bound (fuel : ℕ) (xs : List SweepEvent) :
    (sort_counted fuel xs).2 ≤ xs.length * fuel := by
  induction fuel generalizing xs with
  | zero => simp [sort_counted]
  | succ fuel ih =>
    simp only [sort_counted]
    split_ifs
    · simp
    · have hl := ih (split_list xs).1
      have hr := ih (split_list xs).2
      have hm := merge_events_count (sort_counted fuel (split_list xs).1).1
        (sort_counted fuel (split_list xs).2).1
      rw [sort_counted_length, sort_counted_length] at hm
      have hs : (split_list xs).1.length + (split_list xs).2.length = xs.length := by
        simp only [split_list, List.length_take, List.length_drop]
        omega
      dsimp only
      calc
        _ ≤ (split_list xs).1.length * fuel + (split_list xs).2.length * fuel +
            ((split_list xs).1.length + (split_list xs).2.length - 1) :=
          Nat.add_le_add (Nat.add_le_add hl hr) hm
        _ ≤ xs.length * (fuel + 1) := by rw [← Nat.add_mul, hs, Nat.mul_add, Nat.mul_one]; omega

theorem sort_counted_output (fuel : ℕ) (xs : List SweepEvent)
    (h : xs.length ≤ 2 ^ fuel) :
    (sort_counted fuel xs).1 = List.mergeSort xs event_cmp := by
  induction fuel generalizing xs with
  | zero =>
    have : xs.length ≤ 1 := by simpa using h
    match xs with
    | [] => simp [sort_counted]
    | [a] => simp [sort_counted]
    | a :: b :: tail => simp at this
  | succ fuel ih =>
    cases xs with
    | nil => simp [sort_counted]
    | cons a tail =>
      cases tail with
      | nil => simp [sort_counted]
      | cons b tail =>
        have hl : ((a :: b :: tail).length + 1) / 2 ≤ 2 ^ fuel := by
          simp only [pow_succ] at h
          omega
        have hr : (a :: b :: tail).length - ((a :: b :: tail).length + 1) / 2 ≤
            2 ^ fuel := by
          simp only [pow_succ] at h
          omega
        simp only [sort_counted, List.length_cons, Nat.succ_le_succ_iff,
          Nat.add_one_le_iff, Nat.not_lt_zero, ↓reduceIte]
        rw [merge_events_output]
        rw [ih _ (by
          simp only [split_list, List.length_take]
          exact (Nat.min_le_left _ _).trans hl),
          ih _ (by simpa [split_list] using hr)]
        simp only [List.mergeSort, split_list,
          List.MergeSort.Internal.splitInTwo, List.splitAt_eq]

def merge_sort_events (xs : List SweepEvent) : List SweepEvent :=
  (sort_counted (Nat.clog 2 xs.length) xs).1

def comparisons_count (xs : List SweepEvent) : ℕ :=
  (sort_counted (Nat.clog 2 xs.length) xs).2

theorem merge_sort_eq_library (xs : List SweepEvent) :
    merge_sort_events xs = List.mergeSort xs event_cmp :=
  sort_counted_output _ _ (Nat.le_pow_clog (by decide) _)

theorem comparisons_count_bound (xs : List SweepEvent) :
    comparisons_count xs ≤ xs.length * Nat.clog 2 xs.length :=
  sort_counted_bound _ _

theorem merge_sort_perm (xs : List SweepEvent) : (merge_sort_events xs).Perm xs := by
  rw [merge_sort_eq_library]
  exact List.mergeSort_perm _ _

theorem merge_sort_sorted (xs : List SweepEvent) :
    (merge_sort_events xs).Pairwise event_le := by
  rw [merge_sort_eq_library]
  simpa [event_cmp] using List.pairwise_mergeSort cmp_trans cmp_total xs

private theorem insert_at_boundary (a : SweepEvent) (pre post : List SweepEvent)
    (hp : ∀ b ∈ pre, ¬ event_le a b) (hq : ∀ b ∈ post, event_le a b) :
    List.orderedInsert event_le a (pre ++ post) = pre ++ a :: post := by
  induction pre with
  | nil =>
    cases post with
    | nil => rfl
    | cons b bs => simp [hq b (by simp)]
  | cons b bs ih =>
    simp only [List.cons_append, List.orderedInsert_cons,
      if_neg (hp b (by simp)), List.cons.injEq, true_and]
    exact ih (fun c hc => hp c (by simp [hc]))

/-- Equality for a total preorder needs stability, not antisymmetry of event labels. -/
theorem merge_sort_eq_insertion_sort (xs : List SweepEvent) :
    merge_sort_events xs = xs.insertionSort event_le := by
  rw [merge_sort_eq_library]
  induction xs with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨pre, post, hs, ht, hp⟩ := List.mergeSort_cons cmp_trans cmp_total a xs
    have hsorted := List.pairwise_mergeSort cmp_trans cmp_total (a :: xs)
    rw [hs] at hsorted
    have hpost : ∀ b ∈ post, event_le a b := by
      have h := (List.pairwise_append.mp hsorted).2.1
      simpa [event_cmp] using (List.pairwise_cons.mp h).1
    rw [List.insertionSort_cons, ← ih, ht, hs]
    exact (insert_at_boundary a pre post (by simpa [event_cmp] using hp) hpost).symm

/-- Every subsequence with one fixed key retains its entire original order. -/
theorem merge_sort_stable (xs ys : List SweepEvent) (x : ℚ) (k : BoundaryType)
    (hsub : ys.Sublist xs) (hkey : ∀ e ∈ ys, e.coord = x ∧ e.kind = k) :
    ys.Sublist (merge_sort_events xs) := by
  rw [merge_sort_eq_library]
  apply List.sublist_mergeSort cmp_trans cmp_total _ hsub
  apply List.pairwise_of_forall_mem_list
  intro a ha b hb
  have ha' := hkey a ha
  have hb' := hkey b hb
  simp [event_cmp, event_le, ha'.1, hb'.1, ha'.2, hb'.2]

/-- All occurrences of a key, including identical events, keep their order. -/
theorem merge_sort_filter_key (xs : List SweepEvent) (x : ℚ) (k : BoundaryType) :
    (merge_sort_events xs).filter (fun e => e.coord = x ∧ e.kind = k) =
      xs.filter (fun e => e.coord = x ∧ e.kind = k) := by
  let p : SweepEvent → Bool := fun e => decide (e.coord = x ∧ e.kind = k)
  have hsub := merge_sort_stable xs (xs.filter p) x k (List.filter_sublist)
    (fun e he => by simpa [p] using (List.mem_filter.mp he).2)
  have hf := hsub.filter p
  have hid : (xs.filter p).filter p = xs.filter p := by
    simp only [List.filter_filter, Bool.and_self]
  rw [hid] at hf
  have hp := (merge_sort_perm xs).filter p
  exact (hf.eq_of_length hp.length_eq.symm).symm

def merge_sorted_events (s : List RationalInterval) : List SweepEvent :=
  merge_sort_events (source_events s)

@[simp] theorem merge_sorted_events_eq (s : List RationalInterval) :
    merge_sorted_events s = sorted_events s := merge_sort_eq_insertion_sort _

def merge_sweep_counters (s : List RationalInterval) : List ℤ :=
  ((merge_sorted_events s).map event_delta).partialSums

/-- Query the accumulated counter after all starts at x and before any end at x.
The table is shared by the returned observation function. -/
def merge_sweep_overlap_count (s : List RationalInterval) : ℚ → ℤ :=
  let es := merge_sorted_events s
  let table := merge_sweep_counters s
  fun x => table[(es.takeWhile (before_observation x)).length]'(by
    have h := congrArg List.length (List.takeWhile_append_dropWhile
      (l := es) (p := before_observation x))
    simp only [List.length_append] at h
    dsimp [es] at h
    simp only [table, merge_sweep_counters, List.length_partialSums, List.length_map]
    dsimp [es]
    omega)


@[simp] theorem merge_sweep_eq (s : List RationalInterval) :
    merge_sweep_overlap_count s = sweep_overlap_count s := by
  simp only [merge_sweep_overlap_count, merge_sweep_counters, merge_sorted_events_eq,
    sweep_overlap_count, sweep_counters]

theorem sweep_count_invariant (s : List RationalInterval) (x : ℚ) :
    merge_sweep_overlap_count s x = (overlap_count s x : ℤ) := by
  rw [merge_sweep_eq, sweep_overlap_count_correct]

def merge_accepted_lows (s : List RationalInterval) (k : ℕ) : Finset ℚ :=
  (Finset.univ.image fun i : Fin s.length => s[i].left).filter
    fun x => k ≤ (merge_sweep_overlap_count s x).toNat


@[simp] theorem merge_accepted_lows_eq (s : List RationalInterval) (k : ℕ) :
    merge_accepted_lows s k = accepted_lows s k := by
  simp only [merge_accepted_lows, accepted_lows, merge_sweep_eq]

def merge_accepted_highs (s : List RationalInterval) (k : ℕ) : Finset ℚ :=
  (Finset.univ.image fun i : Fin s.length => s[i].right).filter
    fun x => k ≤ (merge_sweep_overlap_count s x).toNat


@[simp] theorem merge_accepted_highs_eq (s : List RationalInterval) (k : ℕ) :
    merge_accepted_highs s k = accepted_highs s k := by
  simp only [merge_accepted_highs, accepted_highs, merge_sweep_eq]

def merge_compute_threshold_hull (s : List RationalInterval) (k : ℕ) : Option RationalInterval :=
  if 0 < k then
    if h : (merge_accepted_lows s k).Nonempty ∧ (merge_accepted_highs s k).Nonempty then
      let l := (merge_accepted_lows s k).min' h.1
      let u := (merge_accepted_highs s k).max' h.2
      if hu : l ≤ u then some ⟨l, u, hu⟩ else none
    else none
  else none


@[simp] theorem merge_compute_threshold_hull_eq (s : List RationalInterval) (k : ℕ) :
    merge_compute_threshold_hull s k = compute_threshold_hull s k := by
  simp only [merge_compute_threshold_hull, compute_threshold_hull,
    merge_accepted_lows_eq, merge_accepted_highs_eq]

def merge_max_overlap (s : List RationalInterval) : ℕ :=
  (lower_endpoints s).sup fun x => (merge_sweep_overlap_count s x).toNat

@[simp] theorem merge_max_overlap_eq (s : List RationalInterval) :
    merge_max_overlap s = max_overlap s := by
  simp only [merge_max_overlap, max_overlap, merge_sweep_eq]

def merge_peak_components (s : List RationalInterval) : Finset RationalInterval :=
  if hm : 0 < merge_max_overlap s then
    (merge_accepted_lows s (merge_max_overlap s)).attach.image fun x =>
      support_span s x.val
        ((show 0 < max_overlap s by simpa only [merge_max_overlap_eq] using hm).trans_le
          ((mem_accepted_lows _ _ _).mp (by
            simpa only [merge_accepted_lows_eq, merge_max_overlap_eq] using x.property)).2)
  else ∅

@[simp] theorem merge_peak_components_eq (s : List RationalInterval) :
    merge_peak_components s = peak_components s := by
  simp only [merge_peak_components, peak_components, merge_max_overlap_eq]
  split_ifs with h
  · ext I
    simp only [Finset.mem_image, Finset.mem_attach, true_and, Subtype.exists]
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, by simpa only [merge_accepted_lows_eq, merge_max_overlap_eq] using hx, he⟩
    · rintro ⟨x, hx, he⟩
      exact ⟨x, by simpa only [merge_accepted_lows_eq, merge_max_overlap_eq] using hx, he⟩
  · rfl

def merge_select_best_peak_component (s : List RationalInterval) : Option RationalInterval :=
  if h : (merge_peak_components s).Nonempty then some ((merge_peak_components s).min' h) else none

@[simp] theorem merge_selection_eq (s : List RationalInterval) :
    merge_select_best_peak_component s = select_best_peak_component s := by
  simp only [merge_select_best_peak_component, select_best_peak_component, merge_peak_components_eq]

theorem consensus_permutation_invariance {s t : List RationalInterval} (h : s.Perm t) :
    merge_sweep_overlap_count s = merge_sweep_overlap_count t ∧
    merge_max_overlap s = merge_max_overlap t ∧
    merge_select_best_peak_component s = merge_select_best_peak_component t ∧
    ∀ k, merge_compute_threshold_hull s k = merge_compute_threshold_hull t k := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext x
    simp only [sweep_count_invariant, overlap_permutation h]
  · simpa only [merge_max_overlap_eq] using max_permutation h
  · simpa only [merge_selection_eq] using selection_permutation h
  · intro k
    simpa only [merge_compute_threshold_hull_eq] using hull_permutation h k

theorem merge_hull_real_bridge (s : List RationalInterval) (k : ℕ) :
    (merge_compute_threshold_hull s k).map embed =
      DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k := by
  rw [merge_compute_threshold_hull_eq, algorithmic_hull_matches_marzullo_hull]

theorem merge_peak_optimal (s : List RationalInterval) (I : RationalInterval)
    (h : merge_select_best_peak_component s = some I) :
    IsPeakComponent s I ∧ (∀ J, IsPeakComponent s J → I ≤ J) ∧
      ∀ J, IsPeakComponent s J → (∀ K, IsPeakComponent s K → J ≤ K) → J = I :=
  best_peak_uniquely_optimal s I (by simpa only [merge_selection_eq] using h)

theorem merge_peak_contained (s : List RationalInterval) (k : ℕ)
    (hk : 0 < k) (hkm : k ≤ merge_max_overlap s) (I : RationalInterval)
    (hi : merge_select_best_peak_component s = some I) :
    ∃ H, merge_compute_threshold_hull s k = some H ∧ H.left ≤ I.left ∧ I.right ≤ H.right := by
  simpa only [merge_compute_threshold_hull_eq] using
    peak_component_subset_threshold_hull s k hk
      (by simpa only [merge_max_overlap_eq] using hkm) I
      (by simpa only [merge_selection_eq] using hi)



/-- One more unit of fuel cannot change a completed sorting computation. -/
theorem sort_counted_depth_stable (fuel : ℕ) (xs : List SweepEvent)
    (h : xs.length ≤ 2 ^ fuel) :
    sort_counted (fuel + 1) xs = sort_counted fuel xs := by
  induction fuel generalizing xs with
  | zero =>
    have hl : xs.length ≤ 1 := by simpa using h
    simp [sort_counted, hl]
  | succ fuel ih =>
    by_cases hs : xs.length ≤ 1
    · simp [sort_counted, hs]
    · have hl : (split_list xs).1.length ≤ 2 ^ fuel := by
        simp only [split_list, List.length_take]
        simp only [pow_succ] at h
        omega
      have hr : (split_list xs).2.length ≤ 2 ^ fuel := by
        simp only [split_list, List.length_drop]
        simp only [pow_succ] at h
        omega
      conv_lhs => rw [sort_counted]
      conv_rhs => rw [sort_counted]
      simp only [if_neg hs]
      rw [ih _ hl, ih _ hr]

theorem sort_counted_depth_irrelevant (xs : List SweepEvent) (fuel : ℕ)
    (h : xs.length ≤ 2 ^ fuel) :
    sort_counted fuel xs = sort_counted (Nat.clog 2 xs.length) xs := by
  have hl : Nat.clog 2 xs.length ≤ fuel := Nat.clog_le_of_le_pow h
  induction fuel, hl using Nat.le_induction with
  | base => rfl
  | succ fuel hl ih =>
    rw [sort_counted_depth_stable fuel xs ((Nat.clog_le_iff_le_pow (by decide)).mp hl)]
    exact ih ((Nat.clog_le_iff_le_pow (by decide)).mp hl)

/-- Recurrence uses the actual counts on the two contiguous halves. -/
theorem comparisons_count_recurrence (xs : List SweepEvent) (h : 2 ≤ xs.length) :
    comparisons_count xs ≤ comparisons_count (split_list xs).1 +
      comparisons_count (split_list xs).2 + xs.length - 1 := by
  have hc : 0 < Nat.clog 2 xs.length := by
    apply (Nat.lt_clog_iff_pow_lt (by decide)).mpr
    simpa using (show 1 < xs.length by omega)
  obtain ⟨fuel, hf⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hc)
  have hn := Nat.le_pow_clog (by decide : 1 < 2) xs.length
  rw [hf, pow_succ] at hn
  have hl : (split_list xs).1.length ≤ 2 ^ fuel := by
    simp only [split_list, List.length_take]; omega
  have hr : (split_list xs).2.length ≤ 2 ^ fuel := by
    simp only [split_list, List.length_drop]; omega
  have hs : (split_list xs).1.length + (split_list xs).2.length = xs.length := by
    simp only [split_list, List.length_take, List.length_drop]; omega
  unfold comparisons_count
  rw [hf, sort_counted, if_neg (by omega)]
  dsimp only
  rw [sort_counted_depth_irrelevant _ fuel hl, sort_counted_depth_irrelevant _ fuel hr]
  have hm := merge_events_count
    (sort_counted (Nat.clog 2 (split_list xs).1.length) (split_list xs).1).1
    (sort_counted (Nat.clog 2 (split_list xs).2.length) (split_list xs).2).1
  rw [sort_counted_length, sort_counted_length, hs] at hm
  omega

theorem split_list_lengths (xs : List SweepEvent) :
    (split_list xs).1.length = (xs.length + 1) / 2 ∧
    (split_list xs).2.length = xs.length / 2 := by
  simp only [split_list, List.length_take, List.length_drop]
  omega

theorem source_events_length (s : List RationalInterval) :
    (source_events s).length = 2 * s.length := by
  simp [source_events, List.length_flatMap, Nat.mul_comm]

theorem source_comparisons_bound (s : List RationalInterval) :
    comparisons_count (source_events s) ≤ (2 * s.length) * Nat.clog 2 (2 * s.length) := by
  simpa only [source_events_length] using comparisons_count_bound (source_events s)



theorem merge_fault_bound (s : List RationalInterval) (f : ℕ) (t : ℝ)
    (h : DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t) :
    s.length - f ≤ merge_max_overlap s := by
  rw [merge_max_overlap_eq]
  exact max_overlap_ge_fault_bound s f t h

theorem merge_hull_safe (s : List RationalInterval) (f : ℕ) (t : ℝ)
    (h : DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t) :
    ∃ I, merge_compute_threshold_hull s (s.length - f) = some I ∧
      DistributedMarzulloAlgorithm.containsTime (embed I) t := by
  simpa only [merge_compute_threshold_hull_eq] using algorithmic_hull_contains_true_time s f t h

/-- End-to-end contracts for the replacement backend, including its counted recursion. -/
structure DistributedMarzulloEventSortingSuite : Prop where
  permutation : ∀ xs, (merge_sort_events xs).Perm xs
  sorted : ∀ xs, (merge_sort_events xs).Pairwise event_le
  stability : ∀ xs x k,
    (merge_sort_events xs).filter (fun e => e.coord = x ∧ e.kind = k) =
      xs.filter (fun e => e.coord = x ∧ e.kind = k)
  equivalence : ∀ xs, merge_sort_events xs = xs.insertionSort event_le
  recurrence : ∀ xs, 2 ≤ xs.length →
    comparisons_count xs ≤ comparisons_count (split_list xs).1 +
      comparisons_count (split_list xs).2 + xs.length - 1
  comparisons : ∀ xs, comparisons_count xs ≤ xs.length * Nat.clog 2 xs.length
  event_count : ∀ s, (source_events s).length = 2 * s.length
  counter : ∀ s x, merge_sweep_overlap_count s x = (overlap_count s x : ℤ)
  peak_equivalence : ∀ s, merge_select_best_peak_component s = select_best_peak_component s
  hull_equivalence : ∀ s k, merge_compute_threshold_hull s k = compute_threshold_hull s k
  source_permutation : ∀ s t, s.Perm t →
    merge_sweep_overlap_count s = merge_sweep_overlap_count t ∧
    merge_max_overlap s = merge_max_overlap t ∧
    merge_select_best_peak_component s = merge_select_best_peak_component t ∧
    ∀ k, merge_compute_threshold_hull s k = merge_compute_threshold_hull t k
  optimality : ∀ s I, merge_select_best_peak_component s = some I →
    IsPeakComponent s I ∧ (∀ J, IsPeakComponent s J → I ≤ J) ∧
      ∀ J, IsPeakComponent s J → (∀ K, IsPeakComponent s K → J ≤ K) → J = I
  containment : ∀ s k, 0 < k → k ≤ merge_max_overlap s → ∀ I,
    merge_select_best_peak_component s = some I →
    ∃ H, merge_compute_threshold_hull s k = some H ∧ H.left ≤ I.left ∧ I.right ≤ H.right
  real_bridge : ∀ s k, (merge_compute_threshold_hull s k).map embed =
    DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k
  safety : ∀ s f t, DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t →
    ∃ I, merge_compute_threshold_hull s (s.length - f) = some I ∧
      DistributedMarzulloAlgorithm.containsTime (embed I) t

theorem verification_suite : DistributedMarzulloEventSortingSuite := {
  permutation := merge_sort_perm
  sorted := merge_sort_sorted
  stability := merge_sort_filter_key
  equivalence := merge_sort_eq_insertion_sort
  recurrence := comparisons_count_recurrence
  comparisons := comparisons_count_bound
  event_count := source_events_length
  counter := sweep_count_invariant
  peak_equivalence := merge_selection_eq
  hull_equivalence := merge_compute_threshold_hull_eq
  source_permutation := fun _ _ h => consensus_permutation_invariance h
  optimality := merge_peak_optimal
  containment := merge_peak_contained
  real_bridge := merge_hull_real_bridge
  safety := merge_hull_safe
}

end DistributedMarzulloEventSorting
