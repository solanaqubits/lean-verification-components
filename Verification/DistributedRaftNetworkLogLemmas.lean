/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftStateMachine

/-!
# List lemmas for asynchronous Raft Log Matching

These lemmas derive the input compatibility of a partial AppendEntries merge
from Log Matching and the checked predecessor. They make no reachability claim
by themselves and introduce no additional guard on the operational transitions.
-/

namespace DistributedRaftNetworkLogLemmas

open DistributedRaftLeaderCompleteness (LogEntry)
open DistributedRaftStateMachine

theorem matching_refl (a : List LogEntry) : LogMatching a a := by
  intro _ _ _ _ _ _
  rfl

theorem matching_symm {a b : List LogEntry} (h : LogMatching a b) : LogMatching b a := by
  intro i x y hx hy ht
  exact (h i y x hy hx ht.symm).symm

theorem matching_take_right {a b : List LogEntry} (h : LogMatching a b) (n : ℕ) :
    LogMatching a (b.take n) :=
  matching_symm ((matching_symm h).take_left n)

theorem matching_take_both {a b : List LogEntry} (h : LogMatching a b) (m n : ℕ) :
    LogMatching (a.take m) (b.take n) :=
  matching_take_right (h.take_left m) n

theorem matching_prefix_left {a b a' : List LogEntry} (h : LogMatching a b)
    (hp : a'.IsPrefix a) : LogMatching a' b := by
  have he := List.prefix_iff_eq_take.mp hp
  simpa only [← he] using h.take_left a'.length

theorem matching_prefix_right {a b b' : List LogEntry} (h : LogMatching a b)
    (hp : b'.IsPrefix b) : LogMatching a b' :=
  matching_symm (matching_prefix_left (matching_symm h) hp)

theorem matching_prefix_both {a b a' b' : List LogEntry} (h : LogMatching a b)
    (ha : a'.IsPrefix a) (hb : b'.IsPrefix b) : LogMatching a' b' :=
  matching_prefix_right (matching_prefix_left h ha) hb

/-- Equal terms at a shared position determine the entire entry, including command. -/
theorem matching_entry_eq {a b : List LogEntry} (h : LogMatching a b)
    {i : ℕ} {x y : LogEntry} (hx : a[i]? = some x) (hy : b[i]? = some y)
    (ht : x.term = y.term) : x = y := by
  have he := congrArg (fun l : List LogEntry => l[i]?) (h i x y hx hy ht)
  simpa only [List.getElem?_take_of_succ, hx, hy, Option.some.injEq] using he

theorem compatible_of_aligned (a b : List LogEntry)
    (h : ∀ (i : ℕ) (x y : LogEntry),
      a[i]? = some x → b[i]? = some y → x.term = y.term → x = y) :
    CompatibleEntries a b := by
  induction a generalizing b with
  | nil => cases b <;> trivial
  | cons x a ih =>
    cases b with
    | nil => trivial
    | cons y b =>
      constructor
      · exact h 0 x y rfl rfl
      · apply ih
        intro i u v hu hv ht
        exact h (i + 1) u v (by simpa using hu) (by simpa using hv) ht

theorem matching_compatible {a b : List LogEntry} (h : LogMatching a b) :
    CompatibleEntries a b :=
  compatible_of_aligned a b (fun _ _ _ hx hy ht => matching_entry_eq h hx hy ht)

/-- Compatibility is inherited by the aligned suffix and the finite incoming batch. -/
theorem matching_compatible_slice {old source : List LogEntry}
    (h : LogMatching old source) (prev count : ℕ) :
    CompatibleEntries (old.drop prev) ((source.drop prev).take count) := by
  apply compatible_of_aligned
  intro i x y hx hy ht
  have hi : i < count := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hy
    simp only [List.length_take, List.length_drop] at hi
    omega
  rw [List.getElem?_drop] at hx
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop] at hy
  exact matching_entry_eq h hx hy ht

/-- Taking an earlier snapshot as a prefix preserves every defined predecessor term. -/
theorem termAt_prefix {a b : List LogEntry} (hp : a.IsPrefix b)
    (i : ℕ) (hi : i ≤ a.length) : termAt a i = termAt b i := by
  by_cases hz : i = 0
  · simp [termAt, hz]
  obtain ⟨suffix, rfl⟩ := hp
  simp only [termAt]
  rw [List.getElem?_append_left (by omega : i - 1 < a.length)]

/-- The predecessor test yields equality of complete prefixes, including at index zero. -/
theorem matching_predecessor_prefix {old source : List LogEntry}
    (h : LogMatching old source) (prev : ℕ) (hs : prev ≤ source.length)
    (hp : prevMatches old prev (termAt source prev)) :
    old.take prev = source.take prev := by
  by_cases hz : prev = 0
  · simp [hz]
  have ho : prev - 1 < old.length := by have := hp.1; omega
  have hi : prev - 1 < source.length := by omega
  have hgeto : old[prev - 1]? = some old[prev - 1] := List.getElem?_eq_getElem ho
  have hgets : source[prev - 1]? = some source[prev - 1] := List.getElem?_eq_getElem hi
  have ht : old[prev - 1].term = source[prev - 1].term := by
    simpa only [termAt, hz, ↓reduceIte, hgeto, hgets, Option.getD_some] using hp.2
  have hm := h (prev - 1) _ _ hgeto hgets ht
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ prev)] using hm

/-- A successful RPC leaves the old log or installs a prefix of its historical source. -/
theorem matching_append_entries_choice {old source : List LogEntry}
    (h : LogMatching old source) (prev count : ℕ) (hs : prev ≤ source.length)
    (hp : prevMatches old prev (termAt source prev)) :
    appendEntriesLog old prev ((source.drop prev).take count) = old ∨
    appendEntriesLog old prev ((source.drop prev).take count) =
      source.take (prev + count) :=
  append_entries_log_choice old source prev count
    (matching_predecessor_prefix h prev hs hp) (matching_compatible_slice h prev count)

end DistributedRaftNetworkLogLemmas
