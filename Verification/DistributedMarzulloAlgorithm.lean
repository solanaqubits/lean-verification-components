/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Static interval agreement with a fixed fault budget

This is an exact-real specification of a threshold envelope, not the NTP event
sweep. A maximum-overlap component need not contain the true time. The safe
output is the smallest closed interval enclosing every point supported by at
least `n - f` indexed sources; it may contain gaps of insufficient support.
-/

namespace DistributedMarzulloAlgorithm

noncomputable section

/-- Closed, valid source interval. Singleton intervals are permitted. -/
structure TimeInterval where
  low : ℝ
  high : ℝ
  h_valid : low ≤ high

/-- Containment includes both endpoints. -/
def containsTime (I : TimeInterval) (t : ℝ) : Prop :=
  I.low ≤ t ∧ t ≤ I.high

instance (I : TimeInterval) (t : ℝ) : Decidable (containsTime I t) :=
  inferInstanceAs (Decidable (I.low ≤ t ∧ t ≤ I.high))

/-- Source identity is its list position: equal interval values remain distinct votes. -/
def supporters (sources : List TimeInterval) (t : ℝ) : Finset (Fin sources.length) := by
  classical
  exact Finset.univ.filter fun i => containsTime sources[i] t

/-- Number of source intervals containing a point, with list multiplicity. -/
def overlapCount (sources : List TimeInterval) (t : ℝ) : ℕ :=
  (supporters sources t).card

theorem overlapCount_le_length (sources : List TimeInterval) (t : ℝ) :
    overlapCount sources t ≤ sources.length := by
  classical
  simpa [overlapCount] using Finset.card_le_univ (supporters sources t)

@[simp] theorem overlapCount_nil (t : ℝ) : overlapCount [] t = 0 := by
  classical
  simp [overlapCount, supporters]

@[simp] theorem overlapCount_cons (I : TimeInterval) (sources : List TimeInterval) (t : ℝ) :
    overlapCount (I :: sources) t =
      if containsTime I t then overlapCount sources t + 1 else overlapCount sources t := by
  classical
  simp only [overlapCount, supporters, List.length_cons]
  rw [Fin.card_filter_univ_succ]
  rfl

/-- Agreement with the literal list-filter count, including repeated interval values. -/
theorem overlapCount_eq_filter_length (sources : List TimeInterval) (t : ℝ) :
    overlapCount sources t = (sources.filter fun I => decide (containsTime I t)).length := by
  classical
  induction sources with
  | nil => simp
  | cons I sources ih =>
    by_cases h : containsTime I t <;> simp [overlapCount_cons, h, ih]

@[simp] theorem mem_supporters (sources : List TimeInterval) (t : ℝ)
    (i : Fin sources.length) :
    i ∈ supporters sources t ↔ containsTime sources[i] t := by
  classical
  simp [supporters]

/-- At least `n-f` specified honest sources, each enclosing the true time. -/
structure FaultModel (sources : List TimeInterval) (f : ℕ) (t_true : ℝ) : Prop where
  fault_bound : f < sources.length
  honest : ∃ H : Finset (Fin sources.length),
    sources.length - f ≤ H.card ∧ ∀ i ∈ H, containsTime sources[i] t_true

theorem true_time_overlap_lower_bound {sources : List TimeInterval} {f : ℕ} {t_true : ℝ}
    (h : FaultModel sources f t_true) :
    sources.length - f ≤ overlapCount sources t_true := by
  classical
  obtain ⟨H, hcard, hhonest⟩ := h.honest
  exact hcard.trans (Finset.card_le_card fun i hi => (mem_supporters _ _ _).mpr (hhonest i hi))

/-- The actual honest intervals have nonempty common intersection. -/
theorem marzullo_intersection_nonempty {sources : List TimeInterval}
    (H : Finset (Fin sources.length)) (t_true : ℝ)
    (h : ∀ i ∈ H, containsTime sources[i] t_true) :
    ∃ t, ∀ i ∈ H, containsTime sources[i] t := ⟨t_true, h⟩

/-- A threshold exceeding the faulty budget shares an honest source with the truth.
This does not say that the tested point equals the true time. -/
theorem threshold_shares_honest_source {sources : List TimeInterval} {f k : ℕ}
    {t t_true : ℝ} (H : Finset (Fin sources.length))
    (hcard : sources.length - f ≤ H.card)
    (hhonest : ∀ i ∈ H, containsTime sources[i] t_true)
    (hk : f < k) (ht : k ≤ overlapCount sources t) :
    ∃ i ∈ H, containsTime sources[i] t ∧ containsTime sources[i] t_true := by
  classical
  by_contra h
  have hdisj : Disjoint (supporters sources t) H := by
    classical
    apply Finset.disjoint_left.mpr
    intro i hi hiH
    exact h ⟨i, hiH, (mem_supporters _ _ _).mp hi, hhonest i hiH⟩
  have htotal : (supporters sources t ∪ H).card ≤ sources.length := by
    classical
    simpa using (Finset.card_le_univ (supporters sources t ∪ H))
  rw [Finset.card_union_of_disjoint hdisj] at htotal
  dsimp [overlapCount] at ht
  omega

/-- Accepted source endpoints; no ordering/sweep implementation is assumed. -/
def acceptedLows (sources : List TimeInterval) (k : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ.image fun i : Fin sources.length => sources[i].low).filter
    fun t => k ≤ overlapCount sources t

def acceptedHighs (sources : List TimeInterval) (k : ℕ) : Finset ℝ := by
  classical
  exact (Finset.univ.image fun i : Fin sources.length => sources[i].high).filter
    fun t => k ≤ overlapCount sources t

/-- Every positive-threshold feasible point has an accepted lower endpoint below it. -/
theorem accepted_lower_endpoint {sources : List TimeInterval} {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht : k ≤ overlapCount sources t) :
    ∃ l ∈ acceptedLows sources k, l ≤ t := by
  classical
  have hs : (supporters sources t).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk ht)
  let lows := (supporters sources t).image fun i => sources[i].low
  have hl : lows.Nonempty := hs.image _
  let l := lows.max' hl
  have hlmem : l ∈ lows := lows.max'_mem hl
  obtain ⟨i, hi, hil⟩ := Finset.mem_image.mp hlmem
  have hlt : l ≤ t := hil ▸ ((mem_supporters _ _ _).mp hi).1
  have hsub : supporters sources t ⊆ supporters sources l := by
    classical
    intro j hj
    apply (mem_supporters _ _ _).mpr
    exact ⟨lows.le_max' _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩),
      hlt.trans ((mem_supporters _ _ _).mp hj).2⟩
  refine ⟨l, Finset.mem_filter.mpr ⟨?_, ht.trans (Finset.card_le_card hsub)⟩, hlt⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hil⟩

/-- Dual endpoint witness above the feasible point. -/
theorem accepted_upper_endpoint {sources : List TimeInterval} {k : ℕ} {t : ℝ}
    (hk : 0 < k) (ht : k ≤ overlapCount sources t) :
    ∃ u ∈ acceptedHighs sources k, t ≤ u := by
  classical
  have hs : (supporters sources t).Nonempty := Finset.card_pos.mp (lt_of_lt_of_le hk ht)
  let highs := (supporters sources t).image fun i => sources[i].high
  have hu : highs.Nonempty := hs.image _
  let u := highs.min' hu
  have humem : u ∈ highs := highs.min'_mem hu
  obtain ⟨i, hi, hiu⟩ := Finset.mem_image.mp humem
  have htu : t ≤ u := hiu ▸ ((mem_supporters _ _ _).mp hi).2
  have hsub : supporters sources t ⊆ supporters sources u := by
    classical
    intro j hj
    apply (mem_supporters _ _ _).mpr
    exact ⟨((mem_supporters _ _ _).mp hj).1.trans htu,
      highs.min'_le _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)⟩
  refine ⟨u, Finset.mem_filter.mpr ⟨?_, ht.trans (Finset.card_le_card hsub)⟩, htu⟩
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hiu⟩

/-- Finite endpoint envelope. `none` denotes no valid positive-threshold envelope.
Real comparisons use classical decidability; no executable numeric implementation is certified. -/
def thresholdHull (sources : List TimeInterval) (k : ℕ) : Option TimeInterval := by
  classical
  exact if 0 < k then
    if h : (acceptedLows sources k).Nonempty ∧ (acceptedHighs sources k).Nonempty then
      let l := (acceptedLows sources k).min' h.1
      let u := (acceptedHighs sources k).max' h.2
      if horder : l ≤ u then some ⟨l, u, horder⟩ else none
    else none
  else none

/-- Positive-threshold feasibility implies success, and the output contains every feasible point. -/
theorem thresholdHull_spec {sources : List TimeInterval} {k : ℕ}
    (hk : 0 < k) (hne : ∃ t, k ≤ overlapCount sources t) :
    ∃ I, thresholdHull sources k = some I ∧
      (∀ t, k ≤ overlapCount sources t → containsTime I t) ∧
      k ≤ overlapCount sources I.low ∧ k ≤ overlapCount sources I.high := by
  classical
  obtain ⟨t, ht⟩ := hne
  obtain ⟨l, hl, hlt⟩ := accepted_lower_endpoint hk ht
  obtain ⟨u, hu, htu⟩ := accepted_upper_endpoint hk ht
  have hneL : (acceptedLows sources k).Nonempty := ⟨l, hl⟩
  have hneU : (acceptedHighs sources k).Nonempty := ⟨u, hu⟩
  have horder : (acceptedLows sources k).min' hneL ≤
      (acceptedHighs sources k).max' hneU :=
    ((acceptedLows sources k).min'_le _ hl).trans
      (hlt.trans (htu.trans ((acceptedHighs sources k).le_max' _ hu)))
  refine ⟨⟨_, _, horder⟩, ?_, ?_, ?_, ?_⟩
  · simp [thresholdHull, hk, hneL, hneU, horder]
  · intro x hx
    obtain ⟨a, ha, hax⟩ := accepted_lower_endpoint hk hx
    obtain ⟨b, hb, hxb⟩ := accepted_upper_endpoint hk hx
    exact ⟨((acceptedLows sources k).min'_le _ ha).trans hax,
      hxb.trans ((acceptedHighs sources k).le_max' _ hb)⟩
  · exact (Finset.mem_filter.mp ((acceptedLows sources k).min'_mem hneL)).2
  · exact (Finset.mem_filter.mp ((acceptedHighs sources k).max'_mem hneU)).2

/-- Sound localization is the envelope of all feasible points, not a maximum component. -/
theorem marzullo_fault_tolerance_soundness {sources : List TimeInterval} {f : ℕ}
    {t_true : ℝ} (h : FaultModel sources f t_true) :
    ∃ I, thresholdHull sources (sources.length - f) = some I ∧ containsTime I t_true := by
  classical
  have hk : 0 < sources.length - f := Nat.sub_pos_of_lt h.fault_bound
  have ht := true_time_overlap_lower_bound h
  obtain ⟨I, hI, hall, _, _⟩ := thresholdHull_spec hk ⟨t_true, ht⟩
  exact ⟨I, hI, hall _ ht⟩

/-- The output is the smallest closed interval containing every feasible point.
Points in gaps inside this envelope need not themselves meet the threshold. -/
theorem thresholdHull_minimal {sources : List TimeInterval} {k : ℕ}
    (hk : 0 < k) (hne : ∃ t, k ≤ overlapCount sources t)
    {I : TimeInterval} (hI : thresholdHull sources k = some I)
    (J : TimeInterval) (hJ : ∀ t, k ≤ overlapCount sources t → containsTime J t) :
    J.low ≤ I.low ∧ I.high ≤ J.high := by
  classical
  obtain ⟨I', hI', _, hlo, hhi⟩ := thresholdHull_spec hk hne
  have heq : I' = I := Option.some.inj (hI'.symm.trans hI)
  subst I'
  exact ⟨(hJ _ hlo).1, (hJ _ hhi).2⟩


/-- A finite endpoint envelope succeeds exactly for a positive, feasible threshold. -/
theorem thresholdHull_success_iff (sources : List TimeInterval) (k : ℕ) :
    (∃ I, thresholdHull sources k = some I) ↔
      0 < k ∧ ∃ t, k ≤ overlapCount sources t := by
  classical
  constructor
  · rintro ⟨I, hI⟩
    unfold thresholdHull at hI
    split_ifs at hI with hk he
    · exact ⟨hk, _, (Finset.mem_filter.mp ((acceptedLows sources k).min'_mem he.1)).2⟩
  · rintro ⟨hk, hne⟩
    obtain ⟨I, hI, _⟩ := thresholdHull_spec hk hne
    exact ⟨I, hI⟩

/-- Two honest wide intervals and one misleading narrow interval. -/
def misleadingSources : List TimeInterval :=
  [⟨0, 10, by norm_num⟩, ⟨0, 10, by norm_num⟩, ⟨8, 9, by norm_num⟩]

/-- The true time has a strict honest majority but is outside the unique
maximum-overlap region. Maximum overlap is therefore not a truth certificate. -/
theorem maximum_overlap_can_exclude_truth :
    FaultModel misleadingSources 1 1 ∧
    1 < misleadingSources.length - 1 ∧
    overlapCount misleadingSources 1 = 2 ∧
    (∀ t, overlapCount misleadingSources t = 3 ↔ 8 ≤ t ∧ t ≤ 9) := by
  classical
  refine ⟨⟨by norm_num [misleadingSources], ?_⟩, by norm_num [misleadingSources], ?_, ?_⟩
  · let H : Finset (Fin 3) := {0, 1}
    refine ⟨H, ?_, ?_⟩
    · change 2 ≤ ({0, 1} : Finset (Fin 3)).card
      decide
    · intro i hi
      change i ∈ ({0, 1} : Finset (Fin 3)) at hi
      fin_cases i
      · norm_num [misleadingSources, containsTime]
      · norm_num [misleadingSources, containsTime]
      · exact False.elim ((by decide :
          (2 : Fin 3) ∉ ({0, 1} : Finset (Fin 3))) hi)
  · norm_num [misleadingSources, containsTime]
  · intro t
    simp only [misleadingSources, overlapCount_cons, overlapCount_nil, containsTime]
    by_cases hwide : 0 ≤ t ∧ t ≤ 10
    · simp only [hwide]
      by_cases hnarrow : 8 ≤ t ∧ t ≤ 9 <;> simp [hnarrow]
    · have hnarrow : ¬ (8 ≤ t ∧ t ≤ 9) := by
        classical
        intro h
        apply hwide
        exact ⟨le_trans (by norm_num) h.1, le_trans h.2 (by norm_num)⟩
      simp [hwide, hnarrow]

/-- Reviewed static-interval guarantees; no maximum-overlap truth claim. -/
structure MarzulloAlgorithmFormalSuite : Prop where
  h_overlap : ∀ {sources f t}, FaultModel sources f t →
    sources.length - f ≤ overlapCount sources t
  h_intersection : ∀ {sources : List TimeInterval}
    (H : Finset (Fin sources.length)) (t : ℝ),
    (∀ i ∈ H, containsTime sources[i] t) → ∃ x, ∀ i ∈ H, containsTime sources[i] x
  h_soundness : ∀ {sources f t}, FaultModel sources f t →
    ∃ I, thresholdHull sources (sources.length - f) = some I ∧ containsTime I t
  h_spec : ∀ {sources k}, 0 < k → (∃ t, k ≤ overlapCount sources t) →
    ∃ I, thresholdHull sources k = some I ∧
      (∀ t, k ≤ overlapCount sources t → containsTime I t) ∧
      k ≤ overlapCount sources I.low ∧ k ≤ overlapCount sources I.high
  h_honest_witness : ∀ {sources : List TimeInterval} {f k : ℕ} {t t_true : ℝ}
    (H : Finset (Fin sources.length)),
    sources.length - f ≤ H.card → (∀ i ∈ H, containsTime sources[i] t_true) →
    f < k → k ≤ overlapCount sources t →
    ∃ i ∈ H, containsTime sources[i] t ∧ containsTime sources[i] t_true
  h_minimal : ∀ {sources k}, 0 < k → (∃ t, k ≤ overlapCount sources t) →
    ∀ {I}, thresholdHull sources k = some I → ∀ J,
    (∀ t, k ≤ overlapCount sources t → containsTime J t) →
    J.low ≤ I.low ∧ I.high ≤ J.high

theorem marzullo_algorithm_master_suite : MarzulloAlgorithmFormalSuite := {
  h_overlap := true_time_overlap_lower_bound
  h_intersection := marzullo_intersection_nonempty
  h_soundness := marzullo_fault_tolerance_soundness
  h_spec := thresholdHull_spec
  h_honest_witness := threshold_shares_honest_source
  h_minimal := thresholdHull_minimal
}

end
end DistributedMarzulloAlgorithm
