/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedMarzulloAlgorithm
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Prod.Lex
import Batteries.Data.List.Scan
import Mathlib.Tactic.Linarith

/-!
# Executable rational interval agreement

Rational intervals are order-convex intervals, not connected components in the
usual topology on the rationals. Source multiplicity is retained. Endpoint
observations occur after starts and before ends. No NTP implementation or
physical-clock dynamics are assumed.
-/
namespace DistributedMarzulloIntervalConsensus

structure RationalInterval where
  left : ℚ
  right : ℚ
  valid : left ≤ right
  deriving DecidableEq

def contains (I : RationalInterval) (x : ℚ) : Prop := I.left ≤ x ∧ x ≤ I.right
instance (I : RationalInterval) (x : ℚ) : Decidable (contains I x) :=
  inferInstanceAs (Decidable (_ ∧ _))

def overlap_count (s : List RationalInterval) (x : ℚ) : ℕ :=
  (s.filter fun I => decide (contains I x)).length

@[simp] theorem overlap_nil (x : ℚ) : overlap_count [] x = 0 := rfl
@[simp] theorem overlap_cons (I : RationalInterval) (s : List RationalInterval) (x : ℚ) :
    overlap_count (I :: s) x = (if contains I x then 1 else 0) + overlap_count s x := by
  by_cases h : contains I x <;> simp [overlap_count, h, Nat.add_comm]

def embed (I : RationalInterval) : DistributedMarzulloAlgorithm.TimeInterval :=
  ⟨I.left, I.right, by exact_mod_cast I.valid⟩

theorem rat_to_real_embedding_preserves_membership (I : RationalInterval) (x : ℚ) :
    contains I x ↔ DistributedMarzulloAlgorithm.containsTime (embed I) (x : ℝ) := by
  simp [contains, DistributedMarzulloAlgorithm.containsTime, embed]

theorem embedding_preserves_overlap (s : List RationalInterval) (x : ℚ) :
    DistributedMarzulloAlgorithm.overlapCount (s.map embed) (x : ℝ) = overlap_count s x := by
  induction s with
  | nil => simp
  | cons I s ih =>
    simp only [List.map_cons, DistributedMarzulloAlgorithm.overlapCount_cons, overlap_cons, ih]
    by_cases h : contains I x
    · simp [h, (rat_to_real_embedding_preserves_membership I x).mp h, Nat.add_comm]
    · simp [h, mt (rat_to_real_embedding_preserves_membership I x).mpr h]

inductive BoundaryType where
  | startPoint
  | endPoint
  deriving DecidableEq

structure SweepEvent where
  coord : ℚ
  kind : BoundaryType
  sourceId : ℕ
  deriving DecidableEq

def BoundaryType.rank : BoundaryType → ℕ
  | .startPoint => 0
  | .endPoint => 1

def event_le (a b : SweepEvent) : Prop :=
  a.coord < b.coord ∨ (a.coord = b.coord ∧ a.kind.rank ≤ b.kind.rank)
instance (a b : SweepEvent) : Decidable (event_le a b) :=
  inferInstanceAs (Decidable (_ ∨ _))

def source_events (s : List RationalInterval) : List SweepEvent :=
  s.zipIdx.flatMap fun (I, i) => [⟨I.left, .startPoint, i⟩, ⟨I.right, .endPoint, i⟩]

def sorted_events (s : List RationalInterval) : List SweepEvent :=
  (source_events s).insertionSort event_le

/-- Each event contributes to the closed-interval count at x. End events at x
are deliberately excluded until after the point observation. -/
def event_contribution (x : ℚ) (e : SweepEvent) : ℤ :=
  match e.kind with
  | .startPoint => if e.coord ≤ x then 1 else 0
  | .endPoint => if e.coord < x then -1 else 0

/-- Integer accumulation prevents truncated subtraction from hiding errors. -/
def event_count_spec (s : List RationalInterval) (x : ℚ) : ℤ :=
  ((sorted_events s).map (event_contribution x)).sum

private theorem interval_event_count (I : RationalInterval) (x : ℚ) :
    (if I.left ≤ x then (1 : ℤ) else 0) + (if I.right < x then -1 else 0) =
      if contains I x then 1 else 0 := by
  by_cases hl : I.left ≤ x <;> by_cases hr : I.right < x
  · simp [hl, hr, contains, not_le.mpr hr]
  · simp [hl, hr, contains, le_of_not_gt hr]
  · exact False.elim (hl (I.valid.trans (le_of_lt hr)))
  · simp [hl, hr, contains]

theorem event_count_spec_correct (s : List RationalInterval) (x : ℚ) :
    event_count_spec s x = (overlap_count s x : ℤ) := by
  unfold event_count_spec sorted_events
  rw [((List.perm_insertionSort _ _).map _).sum_eq]
  suffices h : ∀ (s : List RationalInterval) (offset : ℕ),
      ((s.zipIdx offset).flatMap (fun (I, i) =>
        [event_contribution x ⟨I.left, .startPoint, i⟩,
         event_contribution x ⟨I.right, .endPoint, i⟩])).sum = (overlap_count s x : ℤ) by
    simpa [source_events, List.map_flatMap] using h s 0
  intro s
  induction s with
  | nil => intro offset; simp
  | cons I s ih =>
    intro offset
    simp only [event_contribution] at ih
    simp only [List.zipIdx_cons, List.flatMap_cons, List.sum_append, List.sum_cons,
      List.sum_nil, add_zero, event_contribution, ih, interval_event_count,
      overlap_cons, Nat.cast_add]
    split <;> simp

/-- Closed endpoints and singleton sources have their intended multiplicities. -/
theorem closed_interval_boundary_correct (a b c : ℚ) (hab : a ≤ b) (hbc : b ≤ c) :
    overlap_count [⟨a, b, hab⟩, ⟨b, c, hbc⟩] b = 2 ∧
    overlap_count [⟨b, b, le_rfl⟩] b = 1 := by
  simp [contains, hab, hbc]

private theorem event_le_trans {a b c : SweepEvent} (hab : event_le a b)
    (hbc : event_le b c) : event_le a c := by
  rcases hab with hab | ⟨hab, hkr⟩ <;> rcases hbc with hbc | ⟨hbc, hks⟩
  · exact Or.inl (hab.trans hbc)
  · exact Or.inl (hab.trans_eq hbc)
  · exact Or.inl (hab.symm ▸ hbc)
  · exact Or.inr ⟨hab.trans hbc, hkr.trans hks⟩

private instance : IsTrans SweepEvent event_le := ⟨fun _ _ _ => event_le_trans⟩
private instance : Std.Total event_le := ⟨by
  intro a b
  rcases lt_trichotomy a.coord b.coord with h | h | h
  · exact Or.inl (Or.inl h)
  · rcases le_total a.kind.rank b.kind.rank with hk | hk
    · exact Or.inl (Or.inr ⟨h, hk⟩)
    · exact Or.inr (Or.inr ⟨h.symm, hk⟩)
  · exact Or.inr (Or.inl h)⟩

theorem events_sorted (s : List RationalInterval) :
    (sorted_events s).Pairwise event_le := List.pairwise_insertionSort _ _

def event_delta (e : SweepEvent) : ℤ :=
  match e.kind with | .startPoint => 1 | .endPoint => -1

def before_observation (x : ℚ) (e : SweepEvent) : Bool :=
  match e.kind with | .startPoint => decide (e.coord ≤ x) | .endPoint => decide (e.coord < x)

private theorem observation_downward (x : ℚ) {a b : SweepEvent}
    (hab : event_le a b) (hb : before_observation x b = true) :
    before_observation x a = true := by
  cases ha : a.kind <;> cases hb' : b.kind <;>
    simp only [before_observation, ha, hb', decide_eq_true_eq] at hb ⊢ <;>
    rcases hab with hc | ⟨hc, hr⟩
  all_goals try simp_all [BoundaryType.rank]
  all_goals linarith

private theorem filter_eq_prefix (es : List SweepEvent) (x : ℚ)
    (h : es.Pairwise event_le) :
    es.filter (before_observation x) = es.takeWhile (before_observation x) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨hall, htail⟩ := List.pairwise_cons.mp h
    by_cases he : before_observation x e = true
    · simp [he, ih htail]
    · have hf : es.filter (before_observation x) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro a ha hobs
        exact he (observation_downward x (hall a ha) hobs)
      simp [he, hf]

/-- One accumulating pass over sorted events. The entry at index j is the
counter after the first j events; starts precede ends at a shared coordinate. -/
def sweep_counters (s : List RationalInterval) : List ℤ :=
  ((sorted_events s).map event_delta).partialSums

/-- Query the accumulated counter after all starts at x and before any end at x.
The table is shared by the returned observation function. -/
def sweep_overlap_count (s : List RationalInterval) : ℚ → ℤ :=
  let es := sorted_events s
  let table := sweep_counters s
  fun x => table[(es.takeWhile (before_observation x)).length]'(by
    have h := congrArg List.length (List.takeWhile_append_dropWhile
      (l := es) (p := before_observation x))
    simp only [List.length_append] at h
    dsimp [es] at h
    simp only [table, sweep_counters, List.length_partialSums, List.length_map]
    dsimp [es]
    omega)

theorem sweep_overlap_count_correct (s : List RationalInterval) (x : ℚ) :
    sweep_overlap_count s x = (overlap_count s x : ℤ) := by
  rw [← event_count_spec_correct]
  simp only [sweep_overlap_count, sweep_counters, event_count_spec, List.getElem_partialSums]
  rw [← List.map_take]
  have ht : (sorted_events s).take ((sorted_events s).takeWhile (before_observation x)).length =
      (sorted_events s).takeWhile (before_observation x) := by
    exact (List.prefix_iff_eq_take.mp (List.takeWhile_prefix (before_observation x))).symm
  rw [ht, ← filter_eq_prefix _ _ (events_sorted s)]
  generalize sorted_events s = es
  induction es with
  | nil => rfl
  | cons e es ih =>
    cases hk : e.kind
    · by_cases he : e.coord ≤ x <;>
        simp [before_observation, event_delta, event_contribution, hk, he, ih]
    · by_cases he : e.coord < x <;>
        simp [before_observation, event_delta, event_contribution, hk, he, ih]

/-- All observations at a shared coordinate use the same table position. -/
def grouped_observations (s : List RationalInterval) : List (ℚ × ℤ) :=
  let observe := sweep_overlap_count s
  ((sorted_events s).map SweepEvent.coord).dedup.map fun x => (x, observe x)

theorem grouped_observation_correct (s : List RationalInterval) (x : ℚ) (c : ℤ)
    (h : (x, c) ∈ grouped_observations s) : c = (overlap_count s x : ℤ) := by
  obtain ⟨y, _, he⟩ := List.mem_map.mp h
  have hxy : y = x := congrArg Prod.fst he
  subst y
  have hc := congrArg Prod.snd he
  exact hc.symm.trans (sweep_overlap_count_correct s x)

/-- Candidate boundaries are finite and all comparisons are executable. -/
def accepted_lows (s : List RationalInterval) (k : ℕ) : Finset ℚ :=
  (Finset.univ.image fun i : Fin s.length => s[i].left).filter
    fun x => k ≤ (sweep_overlap_count s x).toNat

def accepted_highs (s : List RationalInterval) (k : ℕ) : Finset ℚ :=
  (Finset.univ.image fun i : Fin s.length => s[i].right).filter
    fun x => k ≤ (sweep_overlap_count s x).toNat

@[simp] theorem mem_accepted_lows (s : List RationalInterval) (k : ℕ) (x : ℚ) :
    x ∈ accepted_lows s k ↔ (∃ i : Fin s.length, s[i].left = x) ∧ k ≤ overlap_count s x := by
  simp only [accepted_lows, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and, sweep_overlap_count_correct, Int.toNat_natCast]

@[simp] theorem mem_accepted_highs (s : List RationalInterval) (k : ℕ) (x : ℚ) :
    x ∈ accepted_highs s k ↔ (∃ i : Fin s.length, s[i].right = x) ∧ k ≤ overlap_count s x := by
  simp only [accepted_highs, Finset.mem_filter, Finset.mem_image, Finset.mem_univ,
    true_and, sweep_overlap_count_correct, Int.toNat_natCast]

/-- Positive thresholds only: the zero threshold has an unbounded feasible set. -/
def compute_threshold_hull (s : List RationalInterval) (k : ℕ) : Option RationalInterval :=
  if 0 < k then
    if h : (accepted_lows s k).Nonempty ∧ (accepted_highs s k).Nonempty then
      let l := (accepted_lows s k).min' h.1
      let u := (accepted_highs s k).max' h.2
      if hu : l ≤ u then some ⟨l, u, hu⟩ else none
    else none
  else none

private theorem accepted_lows_embed (s : List RationalInterval) (k : ℕ) :
    DistributedMarzulloAlgorithm.acceptedLows (s.map embed) k =
      (accepted_lows s k).image (fun x : ℚ => (x : ℝ)) := by
  classical
  ext x
  simp only [DistributedMarzulloAlgorithm.acceptedLows, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hc⟩
    let j : Fin s.length := ⟨i.val, by simpa using i.isLt⟩
    have he : (s[j].left : ℝ) = x := by simpa [embed, j] using hi
    refine ⟨s[j].left, (mem_accepted_lows _ _ _).mpr ⟨⟨j, rfl⟩, ?_⟩, he⟩
    rw [← he, embedding_preserves_overlap] at hc
    exact hc
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨i, hi⟩, hc⟩ := (mem_accepted_lows _ _ _).mp ha
    refine ⟨⟨⟨i.val, by simp⟩, ?_⟩, ?_⟩
    · simpa [embed] using congrArg (fun x : ℚ => (x : ℝ)) hi
    · simpa [embedding_preserves_overlap] using hc

private theorem accepted_highs_embed (s : List RationalInterval) (k : ℕ) :
    DistributedMarzulloAlgorithm.acceptedHighs (s.map embed) k =
      (accepted_highs s k).image (fun x : ℚ => (x : ℝ)) := by
  classical
  ext x
  simp only [DistributedMarzulloAlgorithm.acceptedHighs, Finset.mem_filter,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i, hi⟩, hc⟩
    let j : Fin s.length := ⟨i.val, by simpa using i.isLt⟩
    have he : (s[j].right : ℝ) = x := by simpa [embed, j] using hi
    refine ⟨s[j].right, (mem_accepted_highs _ _ _).mpr ⟨⟨j, rfl⟩, ?_⟩, he⟩
    rw [← he, embedding_preserves_overlap] at hc
    exact hc
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨⟨i, hi⟩, hc⟩ := (mem_accepted_highs _ _ _).mp ha
    refine ⟨⟨⟨i.val, by simp⟩, ?_⟩, ?_⟩
    · simpa [embed] using congrArg (fun x : ℚ => (x : ℝ)) hi
    · simpa [embedding_preserves_overlap] using hc

theorem algorithmic_hull_matches_marzullo_hull (s : List RationalInterval) (k : ℕ) :
    (compute_threshold_hull s k).map embed =
      DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k := by
  classical
  unfold compute_threshold_hull DistributedMarzulloAlgorithm.thresholdHull
  have hm : Monotone (fun x : ℚ => (x : ℝ)) := fun _ _ h => Rat.cast_le.mpr h
  simp only [accepted_lows_embed, accepted_highs_embed, Finset.image_nonempty,
    Finset.min'_image hm, Finset.max'_image hm, Rat.cast_le]
  split_ifs <;> rfl

/-- Every real feasible point has a rational source boundary below it with
at least as much support. This also covers irrational true times. -/
theorem real_point_has_rational_witness (s : List RationalInterval) (k : ℕ)
    (hk : 0 < k) (t : ℝ)
    (ht : k ≤ DistributedMarzulloAlgorithm.overlapCount (s.map embed) t) :
    ∃ x ∈ accepted_lows s k, (x : ℝ) ≤ t := by
  classical
  obtain ⟨x, hx, hxt⟩ := DistributedMarzulloAlgorithm.accepted_lower_endpoint hk ht
  rw [accepted_lows_embed] at hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
  exact ⟨a, ha, hxt⟩

def lower_endpoints (s : List RationalInterval) : Finset ℚ :=
  Finset.univ.image fun i : Fin s.length => s[i].left

def max_overlap (s : List RationalInterval) : ℕ :=
  (lower_endpoints s).sup fun x => (sweep_overlap_count s x).toNat

theorem real_overlap_le_max (s : List RationalInterval) (t : ℝ) :
    DistributedMarzulloAlgorithm.overlapCount (s.map embed) t ≤ max_overlap s := by
  by_cases hp : 0 < DistributedMarzulloAlgorithm.overlapCount (s.map embed) t
  · obtain ⟨x, hx, _⟩ := real_point_has_rational_witness s _ hp t le_rfl
    obtain ⟨⟨i, hi⟩, hc⟩ := (mem_accepted_lows _ _ _).mp hx
    have hm : x ∈ lower_endpoints s := Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
    have hsup := Finset.le_sup (f := fun x => (sweep_overlap_count s x).toNat) hm
    simp only [sweep_overlap_count_correct, Int.toNat_natCast] at hsup
    exact hc.trans (by simpa [max_overlap, sweep_overlap_count_correct] using hsup)
  · omega

theorem overlap_le_max (s : List RationalInterval) (x : ℚ) :
    overlap_count s x ≤ max_overlap s := by
  simpa [embedding_preserves_overlap] using real_overlap_le_max s (x : ℝ)

theorem max_overlap_ge_fault_bound (s : List RationalInterval) (f : ℕ) (t : ℝ)
    (h : DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t) :
    s.length - f ≤ max_overlap s := by
  have hbound := DistributedMarzulloAlgorithm.true_time_overlap_lower_bound h
  simpa using hbound.trans (real_overlap_le_max s t)

theorem algorithmic_hull_contains_true_time (s : List RationalInterval) (f : ℕ) (t : ℝ)
    (h : DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t) :
    ∃ I, compute_threshold_hull s (s.length - f) = some I ∧
      DistributedMarzulloAlgorithm.containsTime (embed I) t := by
  obtain ⟨J, hJ, ht⟩ := DistributedMarzulloAlgorithm.marzullo_fault_tolerance_soundness h
  simp only [List.length_map] at hJ
  rw [← algorithmic_hull_matches_marzullo_hull] at hJ
  cases he : compute_threshold_hull s (s.length - f) with
  | none => simp [he] at hJ
  | some I =>
    have hIJ : embed I = J := by simpa [he] using hJ
    exact ⟨I, rfl, hIJ.symm ▸ ht⟩

def supporters (s : List RationalInterval) (x : ℚ) : Finset (Fin s.length) :=
  Finset.univ.filter fun i => contains s[i] x

@[simp] theorem mem_supporters (s : List RationalInterval) (x : ℚ) (i : Fin s.length) :
    i ∈ supporters s x ↔ contains s[i] x := by simp [supporters]

theorem supporters_card (s : List RationalInterval) (x : ℚ) :
    (supporters s x).card = overlap_count s x := by
  rw [← embedding_preserves_overlap]
  unfold DistributedMarzulloAlgorithm.overlapCount
  apply Finset.card_bij (fun i _ => (⟨i.val, by simp⟩ : Fin (s.map embed).length))
  · intro i hi
    apply (DistributedMarzulloAlgorithm.mem_supporters _ _ _).mpr
    have h := (rat_to_real_embedding_preserves_membership s[i] x).mp
      ((mem_supporters _ _ _).mp hi)
    simpa using h
  · intro i hi j hj hij
    exact Fin.ext (congrArg (fun z : Fin (s.map embed).length => z.val) hij)
  · intro j hj
    let i : Fin s.length := ⟨j.val, by simpa using j.isLt⟩
    refine ⟨i, ?_, Fin.ext rfl⟩
    apply (mem_supporters _ _ _).mpr
    apply (rat_to_real_embedding_preserves_membership s[i] x).mpr
    simpa [i] using (DistributedMarzulloAlgorithm.mem_supporters _ _ _).mp hj

def support_lefts (s : List RationalInterval) (x : ℚ) : Finset ℚ :=
  (supporters s x).image fun i => s[i].left

def support_rights (s : List RationalInterval) (x : ℚ) : Finset ℚ :=
  (supporters s x).image fun i => s[i].right

private theorem supports_nonempty {s : List RationalInterval} {x : ℚ}
    (h : 0 < overlap_count s x) : (supporters s x).Nonempty :=
  Finset.card_pos.mp (by simpa [supporters_card] using h)

/-- Intersection of exactly the sources supporting x. -/
def support_span (s : List RationalInterval) (x : ℚ) (h : 0 < overlap_count s x) :
    RationalInterval where
  left := (support_lefts s x).max' ((supports_nonempty h).image _)
  right := (support_rights s x).min' ((supports_nonempty h).image _)
  valid := by
    have hl : (support_lefts s x).max' ((supports_nonempty h).image _) ≤ x := by
      apply Finset.max'_le
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact ((mem_supporters _ _ _).mp hi).1
    have hr : x ≤ (support_rights s x).min' ((supports_nonempty h).image _) := by
      apply Finset.le_min'
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact ((mem_supporters _ _ _).mp hi).2
    exact hl.trans hr

theorem support_span_membership (s : List RationalInterval) (x : ℚ)
    (h : 0 < overlap_count s x) (y : ℚ) :
    contains (support_span s x h) y ↔ supporters s x ⊆ supporters s y := by
  constructor
  · intro hy i hi
    apply (mem_supporters _ _ _).mpr
    exact ⟨(Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)).trans hy.1,
      hy.2.trans (Finset.min'_le _ _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))⟩
  · intro hsub
    change (support_lefts s x).max' ((supports_nonempty h).image _) ≤ y ∧
      y ≤ (support_rights s x).min' ((supports_nonempty h).image _)
    constructor
    · apply Finset.max'_le
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact ((mem_supporters _ _ _).mp (hsub hi)).1
    · apply Finset.le_min'
      intro a ha
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
      exact ((mem_supporters _ _ _).mp (hsub hi)).2

theorem support_span_contains (s : List RationalInterval) (x : ℚ)
    (h : 0 < overlap_count s x) : contains (support_span s x h) x :=
  (support_span_membership s x h x).mpr (Finset.Subset.refl _)

theorem support_span_peak (s : List RationalInterval) (x : ℚ)
    (hp : 0 < overlap_count s x) (hx : overlap_count s x = max_overlap s)
    (y : ℚ) (hy : contains (support_span s x hp) y) : overlap_count s y = max_overlap s := by
  have hc := Finset.card_le_card ((support_span_membership s x hp y).mp hy)
  rw [supporters_card, supporters_card, hx] at hc
  exact le_antisymm (overlap_le_max s y) hc

/-- Immediately to the right of an ending source, before the next start, the
support count strictly falls. The witness is rational even for tiny gaps. -/
private theorem right_escape (s : List RationalInterval) (b y : ℚ) (hby : b < y)
    (i : Fin s.length) (hi : i ∈ supporters s b) (hend : s[i].right = b) :
    ∃ z, b < z ∧ z ≤ y ∧ overlap_count s z < overlap_count s b := by
  let next := (lower_endpoints s).filter fun a => b < a
  let bounds := insert y next
  have hn : bounds.Nonempty := Finset.insert_nonempty _ _
  let a := bounds.min' hn
  have ha : a ∈ bounds := bounds.min'_mem hn
  have hba : b < a := by
    rcases Finset.mem_insert.mp ha with he | he
    · exact he ▸ hby
    · exact (Finset.mem_filter.mp he).2
  have hay : a ≤ y := bounds.min'_le _ (Finset.mem_insert_self _ _)
  let z := (b + a) / 2
  have hbz : b < z := by dsimp [z]; linarith
  have hza : z < a := by dsimp [z]; linarith
  have hs : supporters s z ⊆ supporters s b := by
    intro j hj
    obtain ⟨hl, hr⟩ := (mem_supporters _ _ _).mp hj
    apply (mem_supporters _ _ _).mpr
    refine ⟨?_, hbz.le.trans hr⟩
    by_contra h
    have hm : s[j].left ∈ next := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, lt_of_not_ge h⟩
    have ham := bounds.min'_le _ (Finset.mem_insert_of_mem hm)
    linarith
  have hnot : i ∉ supporters s z := by
    intro hm
    have hr := ((mem_supporters _ _ _).mp hm).2
    rw [hend] at hr
    linarith
  have hstrict : supporters s z ⊂ supporters s b :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun he => hnot (he.symm ▸ hi)⟩
  exact ⟨z, hbz, hza.le.trans hay, by
    simpa [supporters_card] using Finset.card_lt_card hstrict⟩

/-- Symmetric gap witness to the left of a starting source. -/
private theorem left_escape (s : List RationalInterval) (b y : ℚ) (hyb : y < b)
    (i : Fin s.length) (hi : i ∈ supporters s b) (hstart : s[i].left = b) :
    ∃ z, y ≤ z ∧ z < b ∧ overlap_count s z < overlap_count s b := by
  let ends := Finset.univ.image fun j : Fin s.length => s[j].right
  let prev := ends.filter fun a => a < b
  let bounds := insert y prev
  have hn : bounds.Nonempty := Finset.insert_nonempty _ _
  let a := bounds.max' hn
  have ha : a ∈ bounds := bounds.max'_mem hn
  have hab : a < b := by
    rcases Finset.mem_insert.mp ha with he | he
    · exact he ▸ hyb
    · exact (Finset.mem_filter.mp he).2
  have hya : y ≤ a := bounds.le_max' _ (Finset.mem_insert_self _ _)
  let z := (b + a) / 2
  have hzb : z < b := by dsimp [z]; linarith
  have haz : a < z := by dsimp [z]; linarith
  have hs : supporters s z ⊆ supporters s b := by
    intro j hj
    obtain ⟨hl, hr⟩ := (mem_supporters _ _ _).mp hj
    apply (mem_supporters _ _ _).mpr
    refine ⟨hl.trans hzb.le, ?_⟩
    by_contra h
    have hm : s[j].right ∈ prev := Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩, lt_of_not_ge h⟩
    have hma := bounds.le_max' _ (Finset.mem_insert_of_mem hm)
    linarith
  have hnot : i ∉ supporters s z := by
    intro hm
    have hl := ((mem_supporters _ _ _).mp hm).1
    rw [hstart] at hl
    linarith
  have hstrict : supporters s z ⊂ supporters s b :=
    Finset.ssubset_iff_subset_ne.mpr ⟨hs, fun he => hnot (he.symm ▸ hi)⟩
  exact ⟨z, hya.trans haz.le, hzb, by
    simpa [supporters_card] using Finset.card_lt_card hstrict⟩

/-- Maximal order interval of global peak points. Empty input has no such
component; the everywhere-zero count is not represented by a bounded interval. -/
def IsPeakComponent (s : List RationalInterval) (I : RationalInterval) : Prop :=
  0 < max_overlap s ∧
  (∀ x, contains I x → overlap_count s x = max_overlap s) ∧
  ∀ J : RationalInterval, (∀ x, contains J x → overlap_count s x = max_overlap s) →
    (∃ x, contains I x ∧ contains J x) → I.left ≤ J.left ∧ J.right ≤ I.right

theorem support_span_is_component (s : List RationalInterval) (x : ℚ)
    (hp : 0 < overlap_count s x) (hx : overlap_count s x = max_overlap s) :
    IsPeakComponent s (support_span s x hp) := by
  let I := support_span s x hp
  have hxI : contains I x := support_span_contains s x hp
  have peak : ∀ y, contains I y → overlap_count s y = max_overlap s :=
    support_span_peak s x hp hx
  refine ⟨hx ▸ hp, peak, ?_⟩
  intro J hJ hover
  obtain ⟨w, hwI, hwJ⟩ := hover
  constructor
  · by_contra h
    have hlt : J.left < I.left := lt_of_not_ge h
    have hmem := (support_lefts s x).max'_mem ((supports_nonempty hp).image _)
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
    have hbase : contains I I.left := ⟨le_rfl, I.valid⟩
    have hib := ((support_span_membership s x hp I.left).mp hbase) hi
    obtain ⟨z, hlz, hzb, hdrop⟩ := left_escape s I.left J.left hlt i hib he
    have hzJ : contains J z := ⟨hlz, hzb.le.trans (hwI.1.trans hwJ.2)⟩
    rw [peak _ hbase, hJ _ hzJ] at hdrop
    exact (lt_irrefl _ hdrop)
  · by_contra h
    have hlt : I.right < J.right := lt_of_not_ge h
    have hmem := (support_rights s x).min'_mem ((supports_nonempty hp).image _)
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
    have hbase : contains I I.right := ⟨I.valid, le_rfl⟩
    have hib := ((support_span_membership s x hp I.right).mp hbase) hi
    obtain ⟨z, hbz, hzr, hdrop⟩ := right_escape s I.right J.right hlt i hib he
    have hzJ : contains J z := ⟨(hwJ.1.trans hwI.2).trans hbz.le, hzr⟩
    rw [peak _ hbase, hJ _ hzJ] at hdrop
    exact (lt_irrefl _ hdrop)

@[ext] theorem RationalInterval.ext {I J : RationalInterval}
    (hl : I.left = J.left) (hr : I.right = J.right) : I = J := by
  cases I; cases J; simp_all

theorem peak_components_equal_of_overlap {s : List RationalInterval} {I J : RationalInterval}
    (hi : IsPeakComponent s I) (hj : IsPeakComponent s J)
    (h : ∃ x, contains I x ∧ contains J x) : I = J := by
  obtain ⟨hl, hr⟩ := hi.2.2 J hj.2.1 h
  obtain ⟨hl', hr'⟩ := hj.2.2 I hi.2.1 (by obtain ⟨x, hx, hy⟩ := h; exact ⟨x, hy, hx⟩)
  exact RationalInterval.ext (le_antisymm hl hl') (le_antisymm hr' hr)

/-- The finite set removes repeated presentations of the same component. -/
def peak_components (s : List RationalInterval) : Finset RationalInterval :=
  if hm : 0 < max_overlap s then
    (accepted_lows s (max_overlap s)).attach.image fun x =>
      support_span s x.val (hm.trans_le ((mem_accepted_lows _ _ _).mp x.property).2)
  else ∅

theorem mem_peak_components_iff (s : List RationalInterval) (I : RationalInterval) :
    I ∈ peak_components s ↔ IsPeakComponent s I := by
  constructor
  · intro h
    unfold peak_components at h
    split_ifs at h with hm
    · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
      have hc := ((mem_accepted_lows _ _ _).mp x.property).2
      exact support_span_is_component s x.val _ (le_antisymm (overlap_le_max _ _) hc)
    · simp at h
  · intro h
    have hc : overlap_count s I.left = max_overlap s := h.2.1 _ ⟨le_rfl, I.valid⟩
    have hp : 0 < overlap_count s I.left := hc.symm ▸ h.1
    let J := support_span s I.left hp
    have hJ : IsPeakComponent s J := support_span_is_component s I.left hp hc
    have he : J = I := peak_components_equal_of_overlap hJ h
      ⟨I.left, support_span_contains s I.left hp, ⟨le_rfl, I.valid⟩⟩
    have hstart : I.left ∈ accepted_lows s (max_overlap s) := by
      apply (mem_accepted_lows _ _ _).mpr
      refine ⟨?_, hc.ge⟩
      have hm := (support_lefts s I.left).max'_mem ((supports_nonempty hp).image _)
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
      exact ⟨i, hi.trans (congrArg RationalInterval.left he)⟩
    unfold peak_components
    rw [dif_pos h.1]
    apply Finset.mem_image.mpr
    refine ⟨⟨I.left, hstart⟩, Finset.mem_attach _ _, ?_⟩
    exact he

/-- Every peak point belongs to a computed maximal interval. -/
theorem peak_components_cover (s : List RationalInterval) (x : ℚ)
    (hm : 0 < max_overlap s) (hx : overlap_count s x = max_overlap s) :
    ∃ I ∈ peak_components s, contains I x := by
  have hp : 0 < overlap_count s x := hx.symm ▸ hm
  exact ⟨support_span s x hp, (mem_peak_components_iff _ _).mpr
    (support_span_is_component s x hp hx), support_span_contains s x hp⟩

def interval_key (I : RationalInterval) : Lex (ℚ × ℚ) := toLex (I.right - I.left, I.left)

private theorem interval_key_injective : Function.Injective interval_key := by
  intro I J h
  have he := congrArg ofLex h
  have hl := congrArg Prod.snd he
  have hr := congrArg Prod.fst he
  change I.left = J.left at hl
  apply RationalInterval.ext hl
  change I.right - I.left = J.right - J.left at hr
  linarith

instance : LinearOrder RationalInterval := LinearOrder.lift' interval_key interval_key_injective

/-- Executable list presentation, sorted by length and then left boundary. -/
def peak_component_list (s : List RationalInterval) : List RationalInterval :=
  (peak_components s).sort (· ≤ ·)

def select_best_peak_component (s : List RationalInterval) : Option RationalInterval :=
  if h : (peak_components s).Nonempty then some ((peak_components s).min' h) else none

theorem best_peak_uniquely_optimal (s : List RationalInterval) (I : RationalInterval)
    (h : select_best_peak_component s = some I) :
    IsPeakComponent s I ∧ (∀ J, IsPeakComponent s J → I ≤ J) ∧
      ∀ J, IsPeakComponent s J → (∀ K, IsPeakComponent s K → J ≤ K) → J = I := by
  unfold select_best_peak_component at h
  split_ifs at h with hn
  · have he : (peak_components s).min' hn = I := Option.some.inj h
    subst I
    have hm := (peak_components s).min'_mem hn
    refine ⟨(mem_peak_components_iff _ _).mp hm, ?_, ?_⟩
    · intro J hj
      exact (peak_components s).min'_le _ ((mem_peak_components_iff _ _).mpr hj)
    · intro J hj hmin
      exact le_antisymm (hmin _ ((mem_peak_components_iff _ _).mp hm))
        ((peak_components s).min'_le _ ((mem_peak_components_iff _ _).mpr hj))

/-- Any positive threshold at most the peak encloses every selected peak point. -/
theorem peak_component_subset_threshold_hull (s : List RationalInterval) (k : ℕ)
    (hk : 0 < k) (hkm : k ≤ max_overlap s) (I : RationalInterval)
    (hi : select_best_peak_component s = some I) :
    ∃ H, compute_threshold_hull s k = some H ∧ H.left ≤ I.left ∧ I.right ≤ H.right := by
  have hp := (best_peak_uniquely_optimal s I hi).1
  have hl : k ≤ overlap_count s I.left := hkm.trans_eq (hp.2.1 _ ⟨le_rfl, I.valid⟩).symm
  have hr : k ≤ overlap_count s I.right := hkm.trans_eq (hp.2.1 _ ⟨I.valid, le_rfl⟩).symm
  obtain ⟨H, hH, hall, _⟩ := DistributedMarzulloAlgorithm.thresholdHull_spec
    (sources := s.map embed) hk ⟨(I.left : ℝ), by simpa [embedding_preserves_overlap] using hl⟩
  rw [← algorithmic_hull_matches_marzullo_hull] at hH
  cases he : compute_threshold_hull s k with
  | none => simp [he] at hH
  | some J =>
    have hJ : embed J = H := by simpa [he] using hH
    have hlJ := hall (I.left : ℝ) (by simpa [embedding_preserves_overlap] using hl)
    have hrJ := hall (I.right : ℝ) (by simpa [embedding_preserves_overlap] using hr)
    rw [← hJ] at hlJ hrJ
    refine ⟨J, rfl, ?_, ?_⟩
    · exact_mod_cast (show (J.left : ℝ) ≤ (I.left : ℝ) from hlJ.1)
    · exact_mod_cast (show (I.right : ℝ) ≤ (J.right : ℝ) from hrJ.2)

theorem interval_order_iff (I J : RationalInterval) :
    I ≤ J ↔ I.right - I.left < J.right - J.left ∨
      (I.right - I.left = J.right - J.left ∧ I.left ≤ J.left) := by
  change interval_key I ≤ interval_key J ↔ _
  simp [interval_key, Prod.Lex.toLex_le_toLex]

theorem max_positive_of_nonempty (s : List RationalInterval) (h : s ≠ []) :
    0 < max_overlap s := by
  cases s with
  | nil => exact False.elim (h rfl)
  | cons I s =>
    have hc : 0 < overlap_count (I :: s) I.left := by simp [contains, I.valid]
    exact hc.trans_le (overlap_le_max _ _)

theorem max_attained (s : List RationalInterval) (h : s ≠ []) :
    ∃ x, overlap_count s x = max_overlap s := by
  have hn : (lower_endpoints s).Nonempty := by
    cases s with
    | nil => exact False.elim (h rfl)
    | cons I s => exact ⟨I.left, Finset.mem_image.mpr ⟨⟨0, by simp⟩, Finset.mem_univ _, rfl⟩⟩
  obtain ⟨x, _, hx⟩ := Finset.exists_mem_eq_sup (lower_endpoints s) hn
    (fun x => (sweep_overlap_count s x).toNat)
  exact ⟨x, by simpa [sweep_overlap_count_correct, max_overlap] using hx.symm⟩

theorem best_peak_exists (s : List RationalInterval) (h : s ≠ []) :
    ∃ I, select_best_peak_component s = some I := by
  obtain ⟨x, hx⟩ := max_attained s h
  obtain ⟨I, hi, _⟩ := peak_components_cover s x (max_positive_of_nonempty s h) hx
  simp only [select_best_peak_component, dif_pos (show (peak_components s).Nonempty from ⟨I, hi⟩)]
  exact ⟨_, rfl⟩

theorem overlap_permutation {s t : List RationalInterval} (h : s.Perm t) (x : ℚ) :
    overlap_count s x = overlap_count t x :=
  (h.filter _).length_eq

theorem max_permutation {s t : List RationalInterval} (h : s.Perm t) :
    max_overlap s = max_overlap t := by
  have hl : lower_endpoints s = lower_endpoints t := by
    ext x
    simp only [lower_endpoints, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      have hm := h.mem_iff.mp (List.getElem_mem i.isLt)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      exact ⟨j, (congrArg RationalInterval.left hj).trans hi⟩
    · rintro ⟨i, hi⟩
      have hm := h.mem_iff.mpr (List.getElem_mem i.isLt)
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hm
      exact ⟨j, (congrArg RationalInterval.left hj).trans hi⟩
  simp only [max_overlap, sweep_overlap_count_correct, Int.toNat_natCast, hl,
    overlap_permutation h]

theorem peak_permutation {s t : List RationalInterval} (h : s.Perm t) :
    peak_components s = peak_components t := by
  ext I
  simp only [mem_peak_components_iff, IsPeakComponent, max_permutation h, overlap_permutation h]

theorem selection_permutation {s t : List RationalInterval} (h : s.Perm t) :
    select_best_peak_component s = select_best_peak_component t := by
  simp only [select_best_peak_component, peak_permutation h]

/-- Two separated peaks of height two, of lengths one and two. The first wins
although the true time is in the second peak. -/
def misleading_sources : List RationalInterval :=
  [⟨0, 10, by norm_num⟩, ⟨0, 1, by norm_num⟩, ⟨8, 10, by norm_num⟩]

def misleading_peak : RationalInterval := ⟨0, 1, by norm_num⟩
def misleading_hull : RationalInterval := ⟨0, 10, by norm_num⟩

theorem peak_not_necessarily_true_time_counterexample :
    DistributedMarzulloAlgorithm.FaultModel (misleading_sources.map embed) 1 9 ∧
    max_overlap misleading_sources = 2 ∧
    select_best_peak_component misleading_sources = some misleading_peak ∧
    ¬ contains misleading_peak 9 ∧
    compute_threshold_hull misleading_sources 2 = some misleading_hull ∧
    contains misleading_hull 9 := by
  refine ⟨⟨by norm_num [misleading_sources], ?_⟩, by decide, ?_,
    by decide, by decide, by decide⟩
  · refine ⟨DistributedMarzulloAlgorithm.supporters (misleading_sources.map embed) 9, ?_, ?_⟩
    · change 2 ≤ DistributedMarzulloAlgorithm.overlapCount (misleading_sources.map embed) (9 : ℝ)
      rw [show (9 : ℝ) = ((9 : ℚ) : ℝ) by norm_num, embedding_preserves_overlap]
      decide
    · intro i hi
      exact (DistributedMarzulloAlgorithm.mem_supporters _ _ _).mp hi
  · have hc : peak_components misleading_sources =
        {misleading_peak, (⟨8, 10, by norm_num⟩ : RationalInterval)} := by decide
    obtain ⟨J, hJ⟩ := best_peak_exists misleading_sources (by decide)
    have hopt := best_peak_uniquely_optimal misleading_sources J hJ
    have hm : IsPeakComponent misleading_sources misleading_peak := by
      apply (mem_peak_components_iff _ _).mp
      rw [hc]
      exact Finset.mem_insert_self _ _
    have hmin : ∀ K, IsPeakComponent misleading_sources K → misleading_peak ≤ K := by
      intro K hK
      have hmem := (mem_peak_components_iff _ _).mpr hK
      rw [hc] at hmem
      rcases Finset.mem_insert.mp hmem with rfl | hmem
      · exact le_rfl
      · have he := Finset.mem_singleton.mp hmem
        subst K
        apply (interval_order_iff _ _).mpr
        left
        norm_num [misleading_peak]
    have he := hopt.2.2 misleading_peak hm hmin
    exact he.symm ▸ hJ

private theorem endpoint_witness_perm {s t : List RationalInterval} (h : s.Perm t)
    (field : RationalInterval → ℚ) (x : ℚ) :
    (∃ i : Fin s.length, field s[i] = x) ↔ ∃ i : Fin t.length, field t[i] = x := by
  constructor
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (h.mem_iff.mp (List.getElem_mem i.isLt))
    exact ⟨j, (congrArg field hj).trans hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp (h.mem_iff.mpr (List.getElem_mem i.isLt))
    exact ⟨j, (congrArg field hj).trans hi⟩

theorem hull_permutation {s t : List RationalInterval} (h : s.Perm t) (k : ℕ) :
    compute_threshold_hull s k = compute_threshold_hull t k := by
  have hl : accepted_lows s k = accepted_lows t k := by
    ext x
    simp only [mem_accepted_lows, endpoint_witness_perm h, overlap_permutation h]
  have hr : accepted_highs s k = accepted_highs t k := by
    ext x
    simp only [mem_accepted_highs, endpoint_witness_perm h, overlap_permutation h]
  simp only [compute_threshold_hull, hl, hr]

/-- One step really adds a start or subtracts an end; grouping only determines
where the observation is made, not the arithmetic of the accumulator. -/
theorem sweep_counter_step (s : List RationalInterval) (j : ℕ)
    (hj : j < (sorted_events s).length) :
    (sweep_counters s)[j + 1]'(by simp [sweep_counters]; omega) =
      (sweep_counters s)[j]'(by simp [sweep_counters]; omega) +
        event_delta ((sorted_events s)[j]) := by
  simp only [sweep_counters, List.getElem_partialSums]
  rw [List.take_succ_eq_append_getElem (by simpa using hj)]
  simp

/-- Finite, bounded outputs are intentionally absent on empty input. -/
theorem empty_input :
    max_overlap [] = 0 ∧ select_best_peak_component [] = none ∧
      ∀ k, compute_threshold_hull [] k = none := by
  refine ⟨by decide, by decide, ?_⟩
  intro k
  simp [compute_threshold_hull, accepted_lows, accepted_highs]

/-- Reviewed executable and mathematical contracts. No fault hypothesis is
needed for exact overlap, component optimality or the real specification bridge. -/
structure DistributedMarzulloIntervalConsensusSuite : Prop where
  counter : ∀ s x, sweep_overlap_count s x = (overlap_count s x : ℤ)
  grouping : ∀ s x c, (x, c) ∈ grouped_observations s → c = (overlap_count s x : ℤ)
  components : ∀ s I, I ∈ peak_components s ↔ IsPeakComponent s I
  coverage : ∀ s x, 0 < max_overlap s → overlap_count s x = max_overlap s →
    ∃ I ∈ peak_components s, contains I x
  existence : ∀ s, s ≠ [] → ∃ I, select_best_peak_component s = some I
  optimality : ∀ s I, select_best_peak_component s = some I →
    IsPeakComponent s I ∧ (∀ J, IsPeakComponent s J → I ≤ J) ∧
      ∀ J, IsPeakComponent s J → (∀ K, IsPeakComponent s K → J ≤ K) → J = I
  bridge : ∀ s k, (compute_threshold_hull s k).map embed =
    DistributedMarzulloAlgorithm.thresholdHull (s.map embed) k
  fault_bound : ∀ s f t, DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t →
    s.length - f ≤ max_overlap s
  safety : ∀ s f t, DistributedMarzulloAlgorithm.FaultModel (s.map embed) f t →
    ∃ I, compute_threshold_hull s (s.length - f) = some I ∧
      DistributedMarzulloAlgorithm.containsTime (embed I) t
  containment : ∀ s k, 0 < k → k ≤ max_overlap s → ∀ I,
    select_best_peak_component s = some I →
    ∃ H, compute_threshold_hull s k = some H ∧ H.left ≤ I.left ∧ I.right ≤ H.right
  permutation : ∀ s t, s.Perm t → select_best_peak_component s = select_best_peak_component t
  hull_permutation : ∀ s t, s.Perm t → ∀ k, compute_threshold_hull s k = compute_threshold_hull t k

theorem verification_suite : DistributedMarzulloIntervalConsensusSuite := {
  counter := sweep_overlap_count_correct
  grouping := grouped_observation_correct
  components := mem_peak_components_iff
  coverage := peak_components_cover
  existence := best_peak_exists
  optimality := best_peak_uniquely_optimal
  bridge := algorithmic_hull_matches_marzullo_hull
  fault_bound := max_overlap_ge_fault_bound
  safety := algorithmic_hull_contains_true_time
  containment := peak_component_subset_threshold_hull
  permutation := fun _ _ h => selection_permutation h
  hull_permutation := fun _ _ h => hull_permutation h
}

end DistributedMarzulloIntervalConsensus
