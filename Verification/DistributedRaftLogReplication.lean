/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# DistributedRaftLogReplication

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

namespace DistributedRaftLogReplication

/-! Conditional list identities, not an inductive proof of the Raft network protocol. -/
structure LogEntry where
  index : ℕ
  term : ℕ
  cmd : ℕ
  deriving DecidableEq, Repr

abbrev RaftLog := List LogEntry

def entryMatches (e1 e2 : LogEntry) : Prop :=
  e1.index = e2.index ∧ e1.term = e2.term → e1.cmd = e2.cmd

theorem entry_eq_of_matching (e1 e2 : LogEntry)
    (h_idx : e1.index = e2.index) (h_term : e1.term = e2.term)
    (h_leader : e1.index = e2.index ∧ e1.term = e2.term → e1.cmd = e2.cmd) :
    e1 = e2 := by
  have hc := h_leader ⟨h_idx, h_term⟩
  cases e1
  cases e2
  simp_all

/-- Equality on the shared positions up to k; does not assert either log is long enough. -/
def logsMatchUpTo (l1 l2 : RaftLog) (k : ℕ) : Prop :=
  ∀ (i : ℕ), i ≤ k → (h1 : i < l1.length) → (h2 : i < l2.length) →
    l1.get ⟨i, h1⟩ = l2.get ⟨i, h2⟩

theorem logs_match_refl (l : RaftLog) (k : ℕ) : logsMatchUpTo l l k := by
  intro i _ _ _
  rfl

def isPrefix {α : Type} (p l : List α) : Prop := ∃ tail, l = p ++ tail

theorem append_is_prefix (l : RaftLog) (e : LogEntry) : isPrefix l (l ++ [e]) :=
  ⟨[e], rfl⟩

theorem prefix_preserves_entries (p l : RaftLog) (hp : isPrefix p l) :
    ∀ (i : ℕ) (h_p : i < p.length),
      ∃ (h_l : i < l.length), l.get ⟨i, h_l⟩ = p.get ⟨i, h_p⟩ := by
  rcases hp with ⟨tail, rfl⟩
  intro i h_p
  have hl : i < (p ++ tail).length := by simp only [List.length_append]; omega
  refine ⟨hl, ?_⟩
  simp [List.get_eq_getElem, List.getElem_append_left h_p]

/-- commitIndex is a prefix length (exclusive bound), not an inclusive entry index. -/
def applyEntries (l : RaftLog) (commitIndex : ℕ) : List ℕ :=
  (l.take commitIndex).map LogEntry.cmd

theorem state_machine_safety_deterministic (l1 l2 : RaftLog) (commitIndex : ℕ)
    (h_len1 : commitIndex ≤ l1.length) (h_len2 : commitIndex ≤ l2.length)
    (h_match : ∀ (i : ℕ) (hi : i < commitIndex),
      l1.get ⟨i, by omega⟩ = l2.get ⟨i, by omega⟩) :
    applyEntries l1 commitIndex = applyEntries l2 commitIndex := by
  unfold applyEntries
  congr 1
  apply List.ext_get
  · simp only [List.length_take]; omega
  · intro n h1 h2
    simp only [List.get_eq_getElem, List.getElem_take]
    have hn : n < commitIndex := by simp only [List.length_take] at h1; omega
    exact h_match n hn

structure DistributedRaftFormalSuite : Prop where
  h_entry_eq : ∀ (e1 e2 : LogEntry), e1.index = e2.index → e1.term = e2.term →
    (e1.index = e2.index ∧ e1.term = e2.term → e1.cmd = e2.cmd) → e1 = e2
  h_match_refl : ∀ (l : RaftLog) (k : ℕ), logsMatchUpTo l l k
  h_append_prefix : ∀ (l : RaftLog) (e : LogEntry), isPrefix l (l ++ [e])
  h_prefix_get : ∀ (p l : RaftLog), isPrefix p l →
    ∀ (i : ℕ) (hp : i < p.length), ∃ (hl : i < l.length), l.get ⟨i, hl⟩ = p.get ⟨i, hp⟩
  h_sm_safety : ∀ (l1 l2 : RaftLog) (commitIndex : ℕ)
    (h1 : commitIndex ≤ l1.length) (h2 : commitIndex ≤ l2.length),
    (∀ (i : ℕ) (hi : i < commitIndex),
      l1.get ⟨i, by omega⟩ = l2.get ⟨i, by omega⟩) →
    applyEntries l1 commitIndex = applyEntries l2 commitIndex

theorem distributed_raft_master_verification_suite : DistributedRaftFormalSuite := {
  h_entry_eq := entry_eq_of_matching
  h_match_refl := logs_match_refl
  h_append_prefix := append_is_prefix
  h_prefix_get := prefix_preserves_entries
  h_sm_safety := state_machine_safety_deterministic
}

end DistributedRaftLogReplication
