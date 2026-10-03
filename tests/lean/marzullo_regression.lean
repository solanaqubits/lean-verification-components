import Verification.DistributedMarzulloAlgorithm
import Mathlib.Tactic.Linarith

open DistributedMarzulloAlgorithm
open scoped Classical

noncomputable section

private def touching : List TimeInterval := [⟨0, 1, by norm_num⟩, ⟨1, 2, by norm_num⟩]
private def disconnected : List TimeInterval :=
  [⟨0, 1, by norm_num⟩, ⟨0, 3, by norm_num⟩, ⟨2, 3, by norm_num⟩]

-- Closed endpoints produce a genuine singleton output.
example : ∃ I, thresholdHull touching 2 = some I ∧ I.low = 1 ∧ I.high = 1 := by
  have hchar (t : ℝ) : 2 ≤ overlapCount touching t ↔ t = 1 := by
    simp only [touching, overlapCount_cons, overlapCount_nil, containsTime]
    constructor
    · intro h
      split_ifs at h with h1 h2 h2 <;> first | omega | linarith [h1.2, h2.1]
    · rintro rfl
      norm_num
  obtain ⟨I, hI, _, hlo, hhi⟩ := thresholdHull_spec (by norm_num : 0 < 2)
    ⟨1, (hchar 1).mpr rfl⟩
  exact ⟨I, hI, (hchar _).mp hlo, (hchar _).mp hhi⟩

-- A minimal interval envelope can contain an unsupported gap.
example : ∃ I, thresholdHull disconnected 2 = some I ∧
    I.low = 0 ∧ I.high = 3 ∧ containsTime I (3 / 2) ∧
    overlapCount disconnected (3 / 2) = 1 := by
  have hzero : 2 ≤ overlapCount disconnected 0 := by norm_num [disconnected, containsTime]
  have hthree : 2 ≤ overlapCount disconnected 3 := by norm_num [disconnected, containsTime]
  have hbound (t : ℝ) (h : 2 ≤ overlapCount disconnected t) : 0 ≤ t ∧ t ≤ 3 := by
    by_contra hn
    have hnone1 : ¬ (0 ≤ t ∧ t ≤ 1) := by intro h; apply hn; constructor <;> linarith [h.1, h.2]
    have hnone2 : ¬ (2 ≤ t ∧ t ≤ 3) := by intro h; apply hn; constructor <;> linarith [h.1, h.2]
    simp [disconnected, containsTime, hn, hnone1, hnone2] at h
  obtain ⟨I, hI, hall, hlo, hhi⟩ := thresholdHull_spec (by norm_num : 0 < 2) ⟨0, hzero⟩
  have hlow : I.low = 0 := le_antisymm (hall 0 hzero).1 (hbound _ hlo).1
  have hhigh : I.high = 3 := le_antisymm (hbound _ hhi).2 (hall 3 hthree).2
  refine ⟨I, hI, hlow, hhigh, ?_, ?_⟩
  · norm_num [containsTime, hlow, hhigh]
  · norm_num [disconnected, containsTime]

-- The advertised maximum can miss the truth despite an honest majority.
example : overlapCount misleadingSources 1 = 2 ∧
    overlapCount misleadingSources 8 = 3 ∧
    ¬ (8 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 9) := by
  norm_num [misleadingSources, containsTime]

-- Empty lists, zero thresholds, and impossible thresholds do not succeed.
example : thresholdHull [] 1 = none := by
  cases h : thresholdHull [] 1 with
  | none => rfl
  | some I =>
    have := (thresholdHull_success_iff [] 1).mp ⟨I, h⟩
    simp at this

example (sources : List TimeInterval) : thresholdHull sources 0 = none := by
  simp [thresholdHull]

example (sources : List TimeInterval) : thresholdHull sources (sources.length + 1) = none := by
  cases h : thresholdHull sources (sources.length + 1) with
  | none => rfl
  | some I =>
    obtain ⟨_, t, ht⟩ := (thresholdHull_success_iff _ _).mp ⟨I, h⟩
    have hb := overlapCount_le_length sources t
    omega

-- Equal intervals are separate sources, not a deduplicated vote.
example : overlapCount [⟨0, 1, by norm_num⟩, ⟨0, 1, by norm_num⟩] (1 / 2) = 2 := by
  norm_num [containsTime]
