/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftTraceMatching
import Verification.DistributedRaftEventHistory

/-! A candidate retains its campaign log until election or a change of term. -/
namespace DistributedRaftCandidateHistory
open DistributedRaftLeaderCompleteness (Cluster NodeId Role lastTerm lastIndex)
open DistributedRaftStateMachine
open DistributedRaftTraceMatching
open DistributedRaftEventHistory

variable {C : Cluster}

/-- A step ending as candidate in the same term preserves both candidacy and log. -/
theorem candidate_step_backwards {s s' : GlobalState C} (step : Step s s')
    (n : NodeId C) (hc : (s'.servers n).role = .candidate)
    (ht : (s.servers n).currentTerm = (s'.servers n).currentTerm) :
    (s.servers n).role = .candidate ∧ (s.servers n).log = (s'.servers n).log := by
  cases step <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader, leaderAppend,
      handleAppend, denyAppend, receiveAppendReply, consume, commitLeader, setServer,
      Function.update_apply] at hc ht ⊢ <;>
    (try split_ifs at hc ht ⊢) <;> simp_all

theorem candidate_path_log_eq {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') (n : NodeId C)
    (hc : (s'.servers n).role = .candidate)
    (ht : (s.servers n).currentTerm = (s'.servers n).currentTerm) :
    (s.servers n).role = .candidate ∧ (s.servers n).log = (s'.servers n).log := by
  induction path with
  | refl => exact ⟨hc, rfl⟩
  | @tail mid last path st ih =>
    have h1 := term_path_monotone path n
    have h2 := term_step_monotone st n
    have hs : (mid.servers n).currentTerm = (last.servers n).currentTerm := by omega
    obtain ⟨hmid, hlog⟩ := candidate_step_backwards st n hc hs
    obtain ⟨hold, hprefix⟩ := ih hmid (by omega)
    exact ⟨hold, hprefix.trans hlog⟩

/-- A queued RequestVote still describes the candidate's exact campaign log. -/
theorem request_candidate_snapshot (run : Execution C) (k t : ℕ) (hk : k ≤ run.length)
    (c : NodeId C) (li lt : ℕ) (hw : RequestWitness run k t c li lt)
    (hc : ((run.state k).servers c).role = .candidate)
    (ht : ((run.state k).servers c).currentTerm = t) :
    li = lastIndex ((run.state k).servers c).log ∧
    lt = lastTerm ((run.state k).servers c).log := by
  obtain ⟨i, hi, _, hterm, hli, hlt, hevent⟩ := hw
  have hs : ((run.state (i + 1)).servers c).currentTerm = t := by
    rw [hevent]
    simpa [startElection, setServer] using hterm.symm
  have hlog := (candidate_path_log_eq (run.path (i + 1) k (by omega) hk) c hc
    (hs.trans ht.symm)).2
  rw [hevent] at hlog
  have hlogs : ((run.state i).servers c).log = ((run.state k).servers c).log := by
    simpa [startElection, setServer] using hlog
  exact ⟨hli.trans (congrArg lastIndex hlogs), hlt.trans (congrArg lastTerm hlogs)⟩

end DistributedRaftCandidateHistory
