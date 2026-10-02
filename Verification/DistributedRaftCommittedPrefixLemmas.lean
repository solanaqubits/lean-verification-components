/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftNetworkInduction

/-! Common-prefix retention for the actual conflict-sensitive partial-batch merge. -/
namespace DistributedRaftCommittedPrefixLemmas

open DistributedRaftLeaderCompleteness (LogEntry)
open DistributedRaftStateMachine
open DistributedRaftNetworkLogLemmas

/-- Even a batch ending inside the common prefix preserves the remaining old suffix. -/
theorem merge_common_prefix (p a b : List LogEntry) (count : ℕ) :
    p.IsPrefix (mergeSuffix (p ++ a) ((p ++ b).take count)) := by
  induction p generalizing count with
  | nil => simp
  | cons e p ih =>
    cases count with
    | zero => simp [List.prefix_append]
    | succ count =>
      simpa [mergeSuffix, List.cons_prefix_cons] using ih count

/-- A shared prefix survives any partial transmission from the source log. -/
theorem common_prefix_retained {p old source : List LogEntry}
    (ho : p.IsPrefix old) (hs : p.IsPrefix source) (prev count : ℕ) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) := by
  obtain ⟨a, rfl⟩ := ho
  obtain ⟨b, rfl⟩ := hs
  induction p generalizing prev with
  | nil => simp
  | cons e p ih =>
    cases prev with
    | zero =>
      simpa [appendEntriesLog] using merge_common_prefix (e :: p) a b count
    | succ prev =>
      simpa [appendEntriesLog, List.cons_prefix_cons] using ih prev

/-- Every incoming entry is retained by a compatible merge, including existing matches. -/
theorem incoming_prefix_merge {old incoming : List LogEntry}
    (hc : CompatibleEntries old incoming) : incoming.IsPrefix (mergeSuffix old incoming) := by
  induction old generalizing incoming with
  | nil => cases incoming <;> simp [mergeSuffix]
  | cons a old ih =>
    cases incoming with
    | nil => simp
    | cons b incoming =>
      dsimp [CompatibleEntries] at hc
      by_cases ht : a.term = b.term
      · have he := hc.1 ht
        subst b
        simpa [mergeSuffix, List.cons_prefix_cons] using ih hc.2
      · simp [mergeSuffix, ht]

/-- Successful matching delivery retains the entire transmitted source prefix. -/
theorem transmitted_prefix_retained {old source : List LogEntry}
    (hm : LogMatching old source) (prev count : ℕ) (hp : prev ≤ source.length)
    (hc : prevMatches old prev (termAt source prev)) :
    (source.take (prev + count)).IsPrefix
      (appendEntriesLog old prev ((source.drop prev).take count)) := by
  have heq := matching_predecessor_prefix hm prev hp hc
  have hmerge := incoming_prefix_merge (matching_compatible_slice hm prev count)
  obtain ⟨suffix, hs⟩ := hmerge
  refine ⟨suffix, ?_⟩
  rw [List.take_add]
  simp only [appendEntriesLog, heq, List.append_assoc, hs]

/-- A source prefix covered by the batch endpoint is installed even if absent locally. -/
theorem covered_prefix_installed {p old source : List LogEntry}
    (hs : p.IsPrefix source) (hm : LogMatching old source) (prev count : ℕ)
    (hp : prev ≤ source.length) (hc : prevMatches old prev (termAt source prev))
    (hlen : p.length ≤ prev + count) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) :=
  (List.prefix_take_iff.mpr ⟨hs, hlen⟩).trans
    (transmitted_prefix_retained hm prev count hp hc)


/-- Replaying an existing prefix leaves the entire local log unchanged. -/
theorem merge_prefix_identity {old incoming : List LogEntry} (h : incoming.IsPrefix old) :
    mergeSuffix old incoming = old := by
  obtain ⟨suffix, rfl⟩ := h
  induction incoming with
  | nil => simp
  | cons e incoming ih => simpa [mergeSuffix] using congrArg (List.cons e) ih

/-- A stale source snapshot that is already a local prefix cannot truncate the log. -/
theorem source_prefix_unchanged {old source : List LogEntry}
    (h : source.IsPrefix old) (prev count : ℕ) :
    appendEntriesLog old prev ((source.drop prev).take count) = old := by
  have hi := (List.take_prefix count (source.drop prev)).trans (h.drop prev)
  simp only [appendEntriesLog, merge_prefix_identity hi, List.take_append_drop]

/-- A common or older source preserves the selected local prefix. -/
theorem comparable_prefix_retained {p old source : List LogEntry}
    (ho : p.IsPrefix old) (hs : source.IsPrefix p ∨ p.IsPrefix source) (prev count : ℕ) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) := by
  rcases hs with hs | hs
  · rw [source_prefix_unchanged (hs.trans ho)]
    exact ho
  · exact common_prefix_retained ho hs prev count

end DistributedRaftCommittedPrefixLemmas
