/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega

/-!
# Conditional Raft Leader Completeness

Strong induction on election terms over an abstract archive of log snapshots.
Log Matching, entry provenance, election restrictions and the admissibility of
voter histories are explicit premises. They are not proved invariants of network
RPC transitions. Local histories allow append and whole-log synchronization from
an earlier leader; this is an abstraction, not an implementation of AppendEntries.
-/

namespace DistributedRaftLeaderCompleteness

structure Cluster where
  size : ℕ
  positive : 0 < size

abbrev NodeId (cluster : Cluster) := Fin cluster.size

structure LogEntry where
  index : ℕ
  term : ℕ
  cmd : ℕ
  deriving DecidableEq, Repr

inductive Role where
  | follower | candidate | leader
  deriving DecidableEq, Repr

structure NodeState where
  currentTerm : ℕ
  role : Role
  log : List LogEntry
  deriving DecidableEq, Repr

def majority (cluster : Cluster) (Q : Finset (NodeId cluster)) : Prop :=
  cluster.size < 2 * Q.card

theorem quorum_intersection (cluster : Cluster) (Q₁ Q₂ : Finset (NodeId cluster))
    (h₁ : majority cluster Q₁) (h₂ : majority cluster Q₂) :
    (Q₁ ∩ Q₂).Nonempty := by
  apply Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ Q₁) (Finset.subset_univ Q₂)
  simp only [Finset.card_univ, Fintype.card_fin]
  dsimp [majority] at h₁ h₂
  omega

/-- The all-zero entry is a sentinel for an empty log, not a stored entry. -/
def lastEntry (log : List LogEntry) : LogEntry :=
  log.getLast?.getD ⟨0, 0, 0⟩

def lastTerm (log : List LogEntry) : ℕ := (lastEntry log).term
def lastIndex (log : List LogEntry) : ℕ := (lastEntry log).index

def logUpToDate (logC logV : List LogEntry) : Prop :=
  lastTerm logV < lastTerm logC ∨
    (lastTerm logC = lastTerm logV ∧ lastIndex logV ≤ lastIndex logC)

theorem lastEntry_mem {log : List LogEntry} (h : log ≠ []) : lastEntry log ∈ log := by
  simp only [lastEntry, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

/-- One-based consecutive indices, positive terms, and monotone terms along indices.
The endpoint bounds are recorded explicitly for convenient use in the safety proof. -/
structure WellFormed (log : List LogEntry) : Prop where
  indexed : ∀ (i : ℕ) (hi : i < log.length), (log[i]).index = i + 1
  positive_terms : ∀ e ∈ log, 0 < e.term
  unique_index : ∀ a ∈ log, ∀ b ∈ log, a.index = b.index → a = b
  last_bounds : ∀ e ∈ log, e.index ≤ lastIndex log ∧ e.term ≤ lastTerm log
  term_order : ∀ a ∈ log, ∀ b ∈ log, a.term < b.term → a.index < b.index

/-- One canonical leader per successful term; failed terms have `none`.
Snapshots are supplied data, not an asynchronous execution reconstructed here. -/
structure History (cluster : Cluster) where
  elected : ℕ → Option (NodeId cluster)
  candidate : ℕ → NodeState
  leader : ℕ → NodeState
  voter : ℕ → NodeId cluster → NodeState
  replica : ℕ → NodeId cluster → NodeState
  electionQuorum : ℕ → Finset (NodeId cluster)
  applied : NodeId cluster → LogEntry → Prop

def IsLeader {cluster : Cluster} (H : History cluster) (c : NodeId cluster) (t : ℕ) : Prop :=
  H.elected t = some c

/-- Votes recorded for the winning candidate, not a model of all RequestVote traffic. -/
def votedForCandidate {cluster : Cluster} (H : History cluster)
    (v c : NodeId cluster) (t : ℕ) : Prop :=
  IsLeader H c t ∧ v ∈ H.electionQuorum t

inductive RecordedLog {cluster : Cluster} (H : History cluster) : List LogEntry → Prop where
  | candidate (t) : RecordedLog H (H.candidate t).log
  | leader (t) : RecordedLog H (H.leader t).log
  | voter (t v) : RecordedLog H (H.voter t v).log
  | replica (t v) : RecordedLog H (H.replica t v).log

/-- Abstract local reachability between a replication snapshot and a later vote.
Only leaders in [lower, upper) can supply replacement logs. The term restriction
is a history premise; it is not derived here from message timestamps or currentTerm. -/
inductive VoterEvolution {cluster : Cluster} (H : History cluster) (lower upper : ℕ) :
    List LogEntry → List LogEntry → Prop where
  | refl (log) : VoterEvolution H lower upper log log
  | append (log suffix) : VoterEvolution H lower upper log (log ++ suffix)
  | synchronize (log k c) : lower ≤ k → k < upper → IsLeader H c k →
      VoterEvolution H lower upper log (H.leader k).log
  | trans {a b c} : VoterEvolution H lower upper a b →
      VoterEvolution H lower upper b c → VoterEvolution H lower upper a c

/-- Structural obligations on the archive. None of these fields states Leader
Completeness, preservation of a committed entry, or State Machine Safety. -/
structure HistoryValid {cluster : Cluster} (H : History cluster) : Prop where
  wellFormed : ∀ log, RecordedLog H log → WellFormed log
  origin : ∀ log, RecordedLog H log → ∀ e ∈ log,
    (∃ c, IsLeader H c e.term) ∧ e ∈ (H.leader e.term).log
  matching : ∀ a b, RecordedLog H a → RecordedLog H b →
    ∀ x ∈ a, ∀ y ∈ b, x.index = y.index → x.term = y.term →
    ∀ e ∈ a, e.index ≤ x.index → e ∈ b
  appendOnly : ∀ t, ∃ suffix, (H.leader t).log = (H.candidate t).log ++ suffix
  election_majority : ∀ c t, IsLeader H c t → majority cluster (H.electionQuorum t)
  vote_rule : ∀ v c t, votedForCandidate H v c t →
    logUpToDate (H.candidate t).log (H.voter t v).log
  candidate_old : ∀ c t, IsLeader H c t → lastTerm (H.candidate t).log < t
  roles : ∀ c t, IsLeader H c t →
    (H.candidate t).currentTerm = t ∧ (H.candidate t).role = .candidate ∧
    (H.leader t).currentTerm = t ∧ (H.leader t).role = .leader
  voter_history : ∀ t u, 0 < t → t < u → ∀ v,
    VoterEvolution H t u (H.replica t v).log (H.voter u v).log

/-- Direct commitment counts replicas of an entry from the leader's current term.
Older entries may be committed indirectly by a current-term anchor (see below). -/
def committedInTerm {cluster : Cluster} (H : History cluster) (e : LogEntry)
    (t : ℕ) (quorum : Finset (NodeId cluster)) : Prop :=
  e.term = t ∧ 0 < t ∧ majority cluster quorum ∧
  (∃ c, IsLeader H c t) ∧ e ∈ (H.leader t).log ∧
  ∀ v ∈ quorum, e ∈ (H.replica t v).log

/-- This retention lemma is proved by induction on local histories; earlier-leader
retention will itself be supplied by the strong induction on terms. -/
theorem voter_preserves_committed_entry {cluster : Cluster} {H : History cluster}
    {t u : ℕ} {a b : List LogEntry} (history : VoterEvolution H t u a b)
    (e : LogEntry) (h_old : e ∈ a)
    (h_leaders : ∀ k, t ≤ k → k < u → ∀ c, IsLeader H c k → e ∈ (H.leader k).log) :
    e ∈ b := by
  induction history with
  | refl => exact h_old
  | append log suffix => exact List.mem_append_left suffix h_old
  | synchronize log k c hlow hu he => exact h_leaders k hlow hu c he
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h_old)

/-- Equal last terms and sufficient length transfer entries via their common
origin leader and Log Matching. Up-to-Date alone would not justify this step. -/
theorem same_last_term_contains {cluster : Cluster} {H : History cluster}
    (valid : HistoryValid H) (a b : List LogEntry)
    (ha : RecordedLog H a) (hb : RecordedLog H b)
    (hterm : lastTerm a = lastTerm b) (hindex : lastIndex a ≤ lastIndex b)
    (e : LogEntry) (he : e ∈ a) : e ∈ b := by
  have hane : a ≠ [] := by intro h; simp [h] at he
  have hapos := (valid.wellFormed a ha).positive_terms e he
  have habound := (valid.wellFormed a ha).last_bounds e he
  have hbne : b ≠ [] := by
    intro h
    have hz : lastTerm b = 0 := by simp [h, lastTerm, lastEntry]
    rw [hz] at hterm
    omega
  have hamem := lastEntry_mem hane
  have hbmem := lastEntry_mem hbne
  have hoa := (valid.origin a ha (lastEntry a) hamem).2
  have hob := (valid.origin b hb (lastEntry b) hbmem).2
  have hprefix : e ∈ (H.leader (lastTerm a)).log :=
    valid.matching a _ ha (.leader _) _ hamem _ hoa rfl rfl e he habound.1
  have hob' : lastEntry b ∈ (H.leader (lastTerm a)).log := by
    change lastEntry b ∈ (H.leader (lastTerm b)).log at hob
    rw [← hterm] at hob
    exact hob
  exact valid.matching _ b (.leader _) hb _ hob' _ hbmem rfl rfl e hprefix
    (le_trans habound.1 hindex)

/-- Strong induction on terms. Both the equal-last-term branch and the strictly
newer-last-term branch use provenance and Log Matching; no preservation premise
for the target committed entry is assumed. -/
theorem leader_completeness {cluster : Cluster} {H : History cluster}
    (valid : HistoryValid H) (e : LogEntry) (t₁ : ℕ) (Q : Finset (NodeId cluster))
    (hc : committedInTerm H e t₁ Q) (t₂ : ℕ) (c : NodeId cluster)
    (hlt : t₁ < t₂) (hleader : IsLeader H c t₂) : e ∈ (H.leader t₂).log := by
  have main : ∀ u, t₁ < u → ∀ d, IsLeader H d u → e ∈ (H.leader u).log := by
    intro u
    induction u using Nat.strong_induction_on with
    | h u ih =>
      intro htu d hd
      have earlier : ∀ k, t₁ ≤ k → k < u → ∀ c', IsLeader H c' k →
          e ∈ (H.leader k).log := by
        intro k hlow hku c' hk
        by_cases heq : k = t₁
        · simpa [heq] using hc.2.2.2.2.1
        · exact ih k hku (by omega) c' hk
      obtain ⟨v, hv⟩ := quorum_intersection cluster Q (H.electionQuorum u)
        hc.2.2.1 (valid.election_majority d u hd)
      obtain ⟨hvQ, hvVote⟩ := Finset.mem_inter.mp hv
      have hev : e ∈ (H.voter u v).log :=
        voter_preserves_committed_entry (valid.voter_history t₁ u hc.2.1 htu v)
          e (hc.2.2.2.2.2 v hvQ) earlier
      have hUp := valid.vote_rule v d u ⟨hd, hvVote⟩
      have inCandidate : e ∈ (H.candidate u).log := by
        rcases hUp with hnew | ⟨hsame, hlen⟩
        · have hbound := (valid.wellFormed _ (.voter u v)).last_bounds e hev
          have hcne : (H.candidate u).log ≠ [] := by
            intro hnil
            simp [hnil, lastTerm, lastEntry] at hnew
          have hlast := lastEntry_mem hcne
          have horigin := valid.origin _ (.candidate u) _ hlast
          obtain ⟨oldLeader, holdLeader⟩ := horigin.1
          have hklo : t₁ < lastTerm (H.candidate u).log := by rw [← hc.1]; omega
          have hkhi := valid.candidate_old d u hd
          have heOrigin := ih _ hkhi hklo oldLeader holdLeader
          have hidx : e.index ≤ (lastEntry (H.candidate u).log).index := by
            have := (valid.wellFormed _ (.leader _)).term_order
              e heOrigin _ horigin.2 (by
                change e.term < lastTerm (H.candidate u).log
                rw [hc.1]
                exact hklo)
            omega
          exact valid.matching _ _ (.leader _) (.candidate u)
            _ horigin.2 _ hlast rfl rfl e heOrigin hidx
        · exact same_last_term_contains valid _ _ (.voter u v) (.candidate u)
            hsame.symm hlen e hev
      obtain ⟨suffix, hsuffix⟩ := valid.appendOnly u
      rw [hsuffix]
      exact List.mem_append_left suffix inCandidate
  exact main t₂ hlt c hleader

/-- A committed prefix entry has a directly committed current-term anchor. -/
def Committed {cluster : Cluster} (H : History cluster) (e : LogEntry) (t : ℕ) : Prop :=
  ∃ anchor Q, committedInTerm H anchor t Q ∧
    e ∈ (H.leader t).log ∧ e.index ≤ anchor.index

theorem committed_prefix_leader_completeness {cluster : Cluster} {H : History cluster}
    (valid : HistoryValid H) (e : LogEntry) (t u : ℕ)
    (hc : Committed H e t) (c : NodeId cluster) (htu : t < u)
    (hl : IsLeader H c u) : e ∈ (H.leader u).log := by
  obtain ⟨anchor, Q, hanchor, he, hindex⟩ := hc
  have hfuture := leader_completeness valid anchor t Q hanchor u c htu hl
  exact valid.matching _ _ (.leader t) (.leader u) _ hanchor.2.2.2.2.1
    _ hfuture rfl rfl e he hindex

/-- Entry-level safety for committed prefixes, before any application semantics. -/
theorem committed_entries_agree {cluster : Cluster} {H : History cluster}
    (valid : HistoryValid H) (e₁ e₂ : LogEntry) (t₁ t₂ : ℕ)
    (h₁ : Committed H e₁ t₁) (h₂ : Committed H e₂ t₂)
    (hindex : e₁.index = e₂.index) : e₁ = e₂ := by
  have in₁ : e₁ ∈ (H.leader t₁).log := h₁.choose_spec.choose_spec.2.1
  have in₂ : e₂ ∈ (H.leader t₂).log := h₂.choose_spec.choose_spec.2.1
  rcases lt_trichotomy t₁ t₂ with hlt | heq | hgt
  · obtain ⟨c, hc⟩ := h₂.choose_spec.choose_spec.1.2.2.2.1
    exact (valid.wellFormed _ (.leader t₂)).unique_index e₁
      (committed_prefix_leader_completeness valid e₁ t₁ t₂ h₁ c hlt hc) e₂ in₂ hindex
  · subst t₂
    exact (valid.wellFormed _ (.leader t₁)).unique_index e₁ in₁ e₂ in₂ hindex
  · obtain ⟨c, hc⟩ := h₁.choose_spec.choose_spec.1.2.2.2.1
    exact (valid.wellFormed _ (.leader t₁)).unique_index e₁ in₁ e₂
      (committed_prefix_leader_completeness valid e₂ t₂ t₁ h₂ c hgt hc) hindex

/-- Supplied application events; their connection to commitment is a separate
premise of State Machine Safety, not built into the event predicate. -/
def Applied {cluster : Cluster} (H : History cluster) (node : NodeId cluster)
    (e : LogEntry) : Prop := H.applied node e

theorem state_machine_safety {cluster : Cluster} {H : History cluster}
    (valid : HistoryValid H)
    (h_apply : ∀ n e, Applied H n e → ∃ t, Committed H e t)
    (n₁ n₂ : NodeId cluster) (e₁ e₂ : LogEntry)
    (h₁ : Applied H n₁ e₁) (h₂ : Applied H n₂ e₂)
    (hindex : e₁.index = e₂.index) : e₁.cmd = e₂.cmd := by
  obtain ⟨t₁, ht₁⟩ := h_apply n₁ e₁ h₁
  obtain ⟨t₂, ht₂⟩ := h_apply n₂ e₂ h₂
  exact congrArg LogEntry.cmd (committed_entries_agree valid e₁ e₂ t₁ t₂ ht₁ ht₂ hindex)

/-- A newer term can hide a different command at the same index in arbitrary lists.
This rules out deriving prefix inclusion from Up-to-Date alone. -/
theorem up_to_date_alone_insufficient :
    logUpToDate [⟨1, 2, 99⟩] [⟨1, 1, 7⟩] ∧
    (⟨1, 1, 7⟩ : LogEntry) ∉ [⟨1, 2, 99⟩] := by
  unfold logUpToDate lastTerm lastIndex lastEntry
  decide

/-! A nonempty model: one server commits command 7 in term 1 and is reelected
in every later term. This witnesses consistency of the history obligations. -/
namespace ExampleHistory

def cluster : Cluster := ⟨1, by decide⟩
def node : NodeId cluster := ⟨0, by decide⟩
def entry : LogEntry := ⟨1, 1, 7⟩
def stored (t : ℕ) : List LogEntry := if t = 0 then [] else [entry]
def beforeElection (t : ℕ) : List LogEntry := if t ≤ 1 then [] else [entry]

def history : History cluster where
  elected t := if t = 0 then none else some node
  candidate t := ⟨t, .candidate, beforeElection t⟩
  leader t := ⟨t, .leader, stored t⟩
  voter t _ := ⟨t, .follower, beforeElection t⟩
  replica t _ := ⟨t, .follower, stored t⟩
  electionQuorum _ := Finset.univ
  applied _ e := e = entry

theorem recorded_shape {log : List LogEntry} (h : RecordedLog history log) :
    log = [] ∨ log = [entry] := by
  cases h <;> simp only [history] <;>
    dsimp [stored, beforeElection] <;> split <;> simp

theorem wellFormed_empty : WellFormed [] := by
  constructor <;> simp

theorem wellFormed_singleton : WellFormed [entry] := by
  constructor
  · intro i hi
    have : i = 0 := by simpa using hi
    subst i
    rfl
  · simp [entry]
  · simp
  · simp [lastIndex, lastTerm, lastEntry, entry]
  · simp

theorem valid : HistoryValid history := by
  constructor
  · intro log hlog
    rcases recorded_shape hlog with rfl | rfl
    · exact wellFormed_empty
    · exact wellFormed_singleton
  · intro log hlog e he
    rcases recorded_shape hlog with rfl | rfl
    · simp at he
    · have : e = entry := by simpa using he
      subst e
      exact ⟨⟨node, rfl⟩, by simp [history, stored, entry]⟩
  · intro a b ha hb x hx y hy _ _ e he _
    rcases recorded_shape ha with rfl | rfl
    · simp at hx
    · rcases recorded_shape hb with rfl | rfl
      · simp at hy
      · exact he
  · intro t
    by_cases h0 : t = 0
    · subst t; exact ⟨[], rfl⟩
    · by_cases h1 : t ≤ 1
      · exact ⟨[entry], by simp [history, stored, beforeElection, h0, h1]⟩
      · exact ⟨[], by simp [history, stored, beforeElection, h0, h1]⟩
  · intro c t _
    change 1 < 2 * (Finset.univ : Finset (Fin 1)).card
    decide
  · intro v c t _
    right
    exact ⟨rfl, le_refl _⟩
  · intro c t ht
    have h0 : t ≠ 0 := by
      intro hz
      simp [IsLeader, history, hz] at ht
    change lastTerm (beforeElection t) < t
    by_cases h1 : t ≤ 1
    · simp [beforeElection, h1, lastTerm, lastEntry]
      omega
    · simp [beforeElection, h1, lastTerm, lastEntry, entry]
      omega
  · intro c t _
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro t u ht htu v
    have h0 : t ≠ 0 := by omega
    have hu : ¬ u ≤ 1 := by omega
    simpa [history, stored, beforeElection, h0, hu] using
      (VoterEvolution.refl (H := history) (lower := t) (upper := u) [entry])

theorem committed : committedInTerm history entry 1 Finset.univ := by
  refine ⟨rfl, by decide, by
    change 1 < 2 * (Finset.univ : Finset (Fin 1)).card
    decide, ⟨node, rfl⟩, ?_, ?_⟩
  · simp [history, stored]
  · intro v _; simp [history, stored]

theorem nontrivial_leader_completeness : entry ∈ (history.leader 2).log :=
  leader_completeness valid entry 1 Finset.univ committed 2 node (by decide) rfl

theorem application_is_committed : ∀ n e, Applied history n e → ∃ t, Committed history e t := by
  intro n e he
  change e = entry at he
  subst e
  exact ⟨1, entry, Finset.univ, committed, by simp [history, stored], le_refl _⟩

end ExampleHistory

structure RaftLeaderCompletenessSuite : Prop where
  h_intersection : ∀ cluster Q₁ Q₂, majority cluster Q₁ → majority cluster Q₂ →
    (Q₁ ∩ Q₂).Nonempty
  h_leader : ∀ {cluster} {H : History cluster}, HistoryValid H →
    ∀ e t Q, committedInTerm H e t Q → ∀ u c, t < u → IsLeader H c u →
      e ∈ (H.leader u).log
  h_prefix : ∀ {cluster} {H : History cluster}, HistoryValid H →
    ∀ e t u, Committed H e t → ∀ c, t < u → IsLeader H c u → e ∈ (H.leader u).log
  h_state_machine : ∀ {cluster} {H : History cluster}, HistoryValid H →
    (∀ n e, Applied H n e → ∃ t, Committed H e t) →
    ∀ n₁ n₂ e₁ e₂, Applied H n₁ e₁ → Applied H n₂ e₂ →
      e₁.index = e₂.index → e₁.cmd = e₂.cmd

theorem raft_leader_completeness_master_suite : RaftLeaderCompletenessSuite := {
  h_intersection := quorum_intersection
  h_leader := leader_completeness
  h_prefix := committed_prefix_leader_completeness
  h_state_machine := state_machine_safety
}

end DistributedRaftLeaderCompleteness
