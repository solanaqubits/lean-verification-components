/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftNetworkInduction

/-!
# Operational commitment and the Raft completeness bridge

Historical statements concern actual executions of the existing operational
machine. In particular, a commit event is a `Step.commit`, not an assumption
that future leaders preserve a selected value.
-/
namespace DistributedRaftTraceMatching

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry majority)
open DistributedRaftStateMachine
open DistributedRaftNetworkHistory
open DistributedRaftNetworkInduction

variable {C : Cluster}

theorem reachable_after_path {s s' : GlobalState C} (hr : Reachable s)
    (path : Relation.ReflTransGen Step s s') : Reachable s' := by
  induction path with
  | refl => exact hr
  | tail _ st ih => exact ih.step st

theorem term_path_monotone {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') (n : NodeId C) :
    (s.servers n).currentTerm ≤ (s'.servers n).currentTerm := by
  induction path with
  | refl => exact le_rfl
  | tail _ st ih => exact ih.trans (term_step_monotone st n)

theorem elected_path_monotone {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') : s.elected ⊆ s'.elected := by
  induction path with
  | refl => exact fun _ h => h
  | tail _ st ih => exact fun _ h => elected_step_monotone st (ih h)

/-- A historically elected server remains append-only throughout its term.
The assertion is derived from actual steps, including delayed RPC deliveries. -/
theorem elected_same_term_log_prefix {s s' : GlobalState C} (hr : Reachable s)
    (path : Relation.ReflTransGen Step s s') (t : ℕ) (n : NodeId C)
    (helected : (t, n) ∈ s.elected)
    (hterm : (s'.servers n).currentTerm = t) :
    (s.servers n).log.IsPrefix (s'.servers n).log := by
  revert hterm
  induction path with
  | refl => intro _; exact List.prefix_refl _
  | @tail mid last path step ih =>
    intro hterm
    have hmid := reachable_after_path hr path
    have elected := elected_path_monotone path helected
    have bound := (reachable_history hmid).electedBound t n elected
    have mono := term_step_monotone step n
    have hmidterm : (mid.servers n).currentTerm = t := by omega
    have before := (reachable_history hmid).tenure t n elected hmidterm
    have after := (reachable_history (hmid.step step)).tenure t n
      (elected_step_monotone step elected) hterm
    exact (ih hmidterm).trans
      (leader_append_only_step step n before after (hmidterm.trans hterm.symm))

theorem archive_step_mono {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B ∧ ∀ l, A l → B l := by
  cases st with
  | append cmd leader => exact ⟨_, archive_step_append hr h _ cmd leader, fun _ hl => Or.inl hl⟩
  | appendEntries he ht hp => exact ⟨_, archive_step_handle_append hr h he ht hp, fun _ hl => hl⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr h (.observe hm ht) ?_, fun _ hl => hl⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn =>
    refine ⟨A, archive_frame hr h (.timeout _ n hn) ?_, fun _ hl => hl⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr h (.vote he ht hv) ?_, fun _ hl => hl⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc =>
    exact ⟨A, archive_frame hr h (.voteReply he ht hc) (by intros; rfl), fun _ hl => hl⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr h (.elect hc hq) ?_, fun _ hl => hl⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr h (.commit i hl hi ht hq) ?_, fun _ h => h⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr h (.replicate prev count hl hn hp) (by intros; rfl), fun _ hl => hl⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr h (.appendReply he ht hl) ?_, fun _ h => h⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv =>
    exact ⟨A, archive_frame hr h (.rejectVote he ht hv) (by intros; rfl), fun _ hl => hl⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr h (.rejectAppend he ht hp) ?_, fun _ h => h⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr h (.drop he) (by intros; rfl), fun _ hl => hl⟩
  | duplicate hm => exact ⟨A, archive_frame hr h (.duplicate hm) (by intros; rfl), fun _ hl => hl⟩


/-- Historical snapshots are retained by the proof archive along an execution. -/
theorem archive_path_mono {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (ha : ArchiveInvariant s A)
    (path : Relation.ReflTransGen Step s s') :
    ∃ B, ArchiveInvariant s' B ∧ ∀ l, A l → B l := by
  induction path with
  | refl => exact ⟨A, ha, fun _ h => h⟩
  | tail path st ih =>
    obtain ⟨B, hb, hab⟩ := ih
    obtain ⟨D, hd, hbd⟩ := archive_step_mono (reachable_after_path hr path) hb st
    exact ⟨D, hd, fun l h => hbd l (hab l h)⟩

/-- Log Matching applies to snapshots at different times in the same execution. -/
theorem historical_log_matching {s s' : GlobalState C} (hr : Reachable s)
    (path : Relation.ReflTransGen Step s s') (i j : NodeId C) :
    LogMatching (s.servers i).log (s'.servers j).log := by
  obtain ⟨A, ha⟩ := reachable_archive hr
  obtain ⟨B, hb, hab⟩ := archive_path_mono hr ha path
  exact hb.matching _ _ (hab _ (ha.servers i)) (hb.servers j)

end DistributedRaftTraceMatching
