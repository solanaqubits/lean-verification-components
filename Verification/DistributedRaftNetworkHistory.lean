/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftStateMachine

/-! Historical election tenure and authenticated AppendEntries for the unchanged automaton. -/
namespace DistributedRaftNetworkHistory
open DistributedRaftStateMachine
open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry)
variable {C : Cluster}

def MessageAuth (elected : Finset (ℕ × NodeId C)) (m : Envelope C) : Prop :=
  match m.body with
  | .appendEntries t leader _ _ _ _ => (t, leader) ∈ elected ∧ m.destination ≠ leader
  | _ => True

def NetworkAuth (s : GlobalState C) : Prop := ∀ m ∈ s.network, MessageAuth s.elected m

theorem elected_step_monotone {s s' : GlobalState C} (step : Step s s') :
    s.elected ⊆ s'.elected := by
  cases step <;> simp [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
    leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer]

theorem messageAuth_mono {a b : Finset (ℕ × NodeId C)} (h : a ⊆ b)
    {m : Envelope C} (hm : MessageAuth a m) : MessageAuth b m := by
  cases m with
  | mk dst body =>
    cases body <;> (dsimp [MessageAuth] at hm ⊢; try trivial)
    exact ⟨h hm.1, hm.2⟩

theorem broadcast_member_ne {sender : NodeId C} {body : NetworkMessage C}
    {m : Envelope C} (hm : m ∈ broadcast sender body) :
    m.body = body ∧ m.destination ≠ sender := by
  simp only [broadcast, List.mem_map, List.mem_filter] at hm
  obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hm
  exact ⟨rfl, of_decide_eq_true hn⟩

theorem network_auth_step {s s' : GlobalState C} (hr : Reachable s)
    (h : NetworkAuth s) (step : Step s s') : NetworkAuth s' := by
  have grow := elected_step_monotone step
  have old : ∀ m ∈ s.network, MessageAuth s'.elected m :=
    fun m hm => messageAuth_mono grow (h m hm)
  have rem : ∀ before after removed, s.network = before ++ removed :: after →
      ∀ m ∈ before ++ after, MessageAuth s'.elected m := by
    intro before after removed he m hm
    apply old m
    rw [he]
    simp only [List.mem_append, List.mem_cons] at hm ⊢
    tauto
  cases step with
  | observe => exact old
  | timeout n _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · obtain ⟨hb, _⟩ := broadcast_member_ne hm
      simp [MessageAuth, hb]
  | @vote v c t li lt before after he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | voteReply he _ _ => exact rem _ _ _ he
  | elect => exact old
  | append cmd hl =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · obtain ⟨hb, hd⟩ := broadcast_member_ne hm
      simp only [MessageAuth, hb]
      exact ⟨grow ((elections_reachable hr).2 _ hl), hd⟩
  | commit => exact old
  | @replicate n v prev count hl hne _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · simp only [List.mem_singleton] at hm
      subst m
      exact ⟨grow ((elections_reachable hr).2 _ hl), Ne.symm hne⟩
  | appendEntries he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | appendReply he _ _ => exact rem _ _ _ he
  | rejectVote he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | rejectAppend he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | drop he => exact rem _ _ _ he
  | @duplicate m hm =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact old _ hm
    · exact old a ha

structure HistoryFacts (s : GlobalState C) : Prop where
  electedBound : ∀ t n, (t, n) ∈ s.elected → t ≤ (s.servers n).currentTerm
  tenure : ∀ t n, (t, n) ∈ s.elected → (s.servers n).currentTerm = t →
    (s.servers n).role = .leader
  appendAuth : ∀ dst t leader prev pt entries lc,
    (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network →
    (t,leader) ∈ s.elected ∧ dst ≠ leader

theorem elected_bound_step {s s' : GlobalState C}
    (bound : ∀ t n, (t, n) ∈ s.elected → t ≤ (s.servers n).currentTerm)
    (step : Step s s') : ∀ t n, (t, n) ∈ s'.elected → t ≤ (s'.servers n).currentTerm := by
  have old : ∀ t n, (t, n) ∈ s.elected → t ≤ (s'.servers n).currentTerm :=
    fun t n hn => (bound t n hn).trans (term_step_monotone step n)
  cases step <;> try exact old
  case elect n hl hm =>
    intro t v hv
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hv
    rcases hv with ⟨rfl, rfl⟩ | hv
    · simp [becomeLeader, setServer]
    · exact old _ _ hv

theorem history_step {s s' : GlobalState C} (hr : Reachable s)
    (h : HistoryFacts s) (step : Step s s') : HistoryFacts s' := by
  have bound := elected_bound_step h.electedBound step
  have old : ∀ t n, (t, n) ∈ s.elected → (s'.servers n).currentTerm = t →
      (s'.servers n).role = .leader := by
    intro t n hn he
    have hb := h.electedBound t n hn
    have ht : (s.servers n).currentTerm = t := by
      have hm := term_step_monotone step n
      omega
    have hl := h.tenure t n hn ht
    have noRpc : ∀ leader prev pt entries lc,
        (⟨n, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∉ s.network := by
      intro leader prev pt entries lc hm
      obtain ⟨hel, hne⟩ := h.appendAuth n t leader prev pt entries lc hm
      exact hne (election_history_safety hr t n leader hn hel)
    cases step with
    | @appendEntries v leader tr prev pt lc entries before after hs htr _ =>
      by_cases hv : n = v
      · subst v
        have hrt : tr = t := htr.trans ht
        subst tr
        exact False.elim (noRpc leader prev pt entries lc (by simp [hs, ht]))
      · simpa [handleAppend, setServer, Function.update_of_ne hv] using hl
    | @rejectAppend v leader tr prev pt lc entries before after hs _ _ =>
      by_cases hv : n = v
      · subst v
        have hrt : tr ≠ (s.servers n).currentTerm := by
          intro hrt
          have heq : tr = t := hrt.trans ht
          subst tr
          exact noRpc leader prev pt entries lc (by simp [hs, ht])
        simpa [denyAppend, setServer, hrt] using hl
      · simpa [denyAppend, setServer, Function.update_of_ne hv] using hl
    | _ =>
      simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
        leaderAppend, receiveAppendReply, consume, commitLeader, setServer,
        Function.update_apply] at he ⊢
      (try split_ifs at he ⊢) <;> simp_all
  refine ⟨bound, ?_, ?_⟩
  · cases step <;> try exact old
    case elect n hl hm =>
      intro t v hv he
      simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hv
      rcases hv with ⟨rfl, rfl⟩ | hv
      · simp [becomeLeader, setServer]
      · exact old _ _ hv he
  · have auth : NetworkAuth s := by
      intro m hm
      cases m with
      | mk dst body =>
        cases body <;> (dsimp [MessageAuth]; try trivial)
        exact h.appendAuth _ _ _ _ _ _ _ hm
    have newauth := network_auth_step hr auth step
    intro dst t leader prev pt entries lc hm
    exact newauth _ hm

theorem reachable_history {s : GlobalState C} (hr : Reachable s) : HistoryFacts s := by
  induction hr with
  | init => constructor <;> simp [initState]
  | step hr step ih => exact history_step hr ih step

theorem active_elected_log_length_step {s s' : GlobalState C} (hr : Reachable s)
    (step : Step s s') (t : ℕ) (n : NodeId C) (hn : (t, n) ∈ s.elected)
    (he : t = (s'.servers n).currentTerm) :
    (s.servers n).log.length ≤ (s'.servers n).log.length := by
  have h := reachable_history hr
  have hb := h.electedBound t n hn
  have hm := term_step_monotone step n
  have ht : (s.servers n).currentTerm = t := by omega
  have hold := h.tenure t n hn ht
  have hnew := (reachable_history (hr.step step)).tenure t n
    (elected_step_monotone step hn) he.symm
  exact List.IsPrefix.length_le (leader_append_only_step step n hold hnew (ht.trans he))

end DistributedRaftNetworkHistory
