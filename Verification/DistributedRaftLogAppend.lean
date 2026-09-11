import Verification.DistributedRaftConsensus

set_option linter.style.header false

namespace DistributedRaftLogAppend

/-- Reuse the entry type of the existing conditional Raft model. -/
abbrev LogEntry := DistributedRaftConsensus.LogEntry

/-- Equality of optional entries at positions strictly below k. -/
def LogsMatchUpTo (log1 log2 : List LogEntry) (k : ℕ) : Prop :=
  ∀ (i : ℕ), i < k → log1[i]? = log2[i]?

/-- A local list operation, without network or term-validation semantics. -/
def appendEntry (log : List LogEntry) (e : LogEntry) : List LogEntry :=
  log ++ [e]

theorem append_length (log : List LogEntry) (e : LogEntry) :
    (appendEntry log e).length = log.length + 1 := by
  simp [appendEntry]

theorem get_append_old (log : List LogEntry) (e : LogEntry) (i : ℕ)
    (hi : i < log.length) : (appendEntry log e)[i]? = log[i]? :=
  List.getElem?_append_left hi

theorem get_append_last (log : List LogEntry) (e : LogEntry) :
    (appendEntry log e)[log.length]? = some e := by
  simp [appendEntry]

theorem logs_match_preserved_on_append (log1 log2 : List LogEntry) (e : LogEntry)
    (h_len1 : log1.length = log2.length)
    (h_match : LogsMatchUpTo log1 log2 log1.length) :
    LogsMatchUpTo (appendEntry log1 e) (appendEntry log2 e) (log1.length + 1) := by
  intro i hi
  have h_cases : i < log1.length ∨ i = log1.length := by omega
  rcases h_cases with h_old | rfl
  · rw [get_append_old log1 e i h_old,
      get_append_old log2 e i (by omega)]
    exact h_match i h_old
  · rw [get_append_last, h_len1, get_append_last]

/-- All pairs of present entries respect the order of their list positions. -/
def MonotonicLogTerms (log : List LogEntry) : Prop :=
  ∀ (i j : ℕ) e_i e_j, i ≤ j → log[i]? = some e_i → log[j]? = some e_j →
    e_i.term ≤ e_j.term

theorem append_preserves_monotonicity (log : List LogEntry) (e : LogEntry)
    (h_mono : MonotonicLogTerms log)
    (h_last_ge : ∀ (i : ℕ) e_i, log[i]? = some e_i → e_i.term ≤ e.term) :
    MonotonicLogTerms (appendEntry log e) := by
  intro i j e_i e_j hij hi hj
  have hi_lt := (List.getElem?_eq_some_iff.mp hi).choose
  have hj_lt := (List.getElem?_eq_some_iff.mp hj).choose
  rw [append_length] at hi_lt hj_lt
  have hi_cases : i < log.length ∨ i = log.length := by omega
  have hj_cases : j < log.length ∨ j = log.length := by omega
  rcases hi_cases with hi_old | rfl
  · rcases hj_cases with hj_old | rfl
    · rw [get_append_old log e i hi_old] at hi
      rw [get_append_old log e j hj_old] at hj
      exact h_mono i j e_i e_j hij hi hj
    · rw [get_append_old log e i hi_old] at hi
      rw [get_append_last] at hj
      cases hj
      exact h_last_ge i e_i hi
  · rcases hj_cases with hj_old | rfl
    · omega
    · rw [get_append_last] at hi hj
      cases hi
      cases hj
      exact le_refl _

/-- Under monotonicity it suffices to compare with the last existing term.
For the empty list the last-entry condition is vacuous. -/
theorem append_preserves_monotonicity_of_last (log : List LogEntry) (e : LogEntry)
    (h_mono : MonotonicLogTerms log)
    (h_last : ∀ last, log[log.length - 1]? = some last → last.term ≤ e.term) :
    MonotonicLogTerms (appendEntry log e) := by
  apply append_preserves_monotonicity log e h_mono
  intro i e_i hi
  have hi_lt := (List.getElem?_eq_some_iff.mp hi).choose
  have h_idx : log.length - 1 < log.length := by omega
  have h_get : log[log.length - 1]? = some log[log.length - 1] :=
    List.getElem?_eq_getElem h_idx
  exact le_trans (h_mono i (log.length - 1) e_i _ (by omega) hi h_get)
    (h_last _ h_get)

structure DistributedRaftLogAppendFormalSuite : Prop where
  h_length : ∀ (log : List LogEntry) (e : LogEntry),
    (appendEntry log e).length = log.length + 1
  h_get_old : ∀ (log : List LogEntry) (e : LogEntry) (i : ℕ),
    i < log.length → (appendEntry log e)[i]? = log[i]?
  h_get_last : ∀ (log : List LogEntry) (e : LogEntry),
    (appendEntry log e)[log.length]? = some e
  h_match_step : ∀ (log1 log2 : List LogEntry) (e : LogEntry),
    log1.length = log2.length → LogsMatchUpTo log1 log2 log1.length →
    LogsMatchUpTo (appendEntry log1 e) (appendEntry log2 e) (log1.length + 1)
  h_mono_append : ∀ (log : List LogEntry) (e : LogEntry),
    MonotonicLogTerms log →
    (∀ (i : ℕ) e_i, log[i]? = some e_i → e_i.term ≤ e.term) →
    MonotonicLogTerms (appendEntry log e)
  h_mono_last : ∀ (log : List LogEntry) (e : LogEntry),
    MonotonicLogTerms log →
    (∀ last, log[log.length - 1]? = some last → last.term ≤ e.term) →
    MonotonicLogTerms (appendEntry log e)

/-- Selected guarantees of local appending, with all hypotheses retained. -/
theorem distributed_raft_log_append_master_verification_suite :
    DistributedRaftLogAppendFormalSuite := {
  h_length := append_length
  h_get_old := get_append_old
  h_get_last := get_append_last
  h_match_step := logs_match_preserved_on_append
  h_mono_append := append_preserves_monotonicity
  h_mono_last := append_preserves_monotonicity_of_last
}

#print axioms distributed_raft_log_append_master_verification_suite

end DistributedRaftLogAppend
