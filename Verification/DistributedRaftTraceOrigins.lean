/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftEventHistory
import Verification.DistributedRaftLogOrder

/-!
# Entry creation on the same Raft execution

A stored entry has an actual leader-append event on the finite execution being
examined. Delayed partial batches are traced back through their source snapshots;
there is no replacement by an unrelated existentially reachable execution.
-/
namespace DistributedRaftTraceOrigins

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry)
open DistributedRaftStateMachine
open DistributedRaftEventHistory
open DistributedRaftLogOrder

variable {C : Cluster}

/-- The entry was created by one of this execution's actual client append steps. -/
def TraceGenerated (run : Execution C) (k : ℕ) (e : LogEntry) : Prop :=
  ∃ j, j < k ∧ ∃ owner cmd,
    ((run.state j).servers owner).role = .leader ∧
    e = ⟨((run.state j).servers owner).log.length + 1,
      ((run.state j).servers owner).currentTerm, cmd⟩ ∧
    run.state (j + 1) = leaderAppend (run.state j) owner cmd

theorem TraceGenerated.mono {run : Execution C} {k k' : ℕ} {e : LogEntry}
    (h : TraceGenerated run k e) (hk : k ≤ k') : TraceGenerated run k' e := by
  obtain ⟨j, hj, rest⟩ := h
  exact ⟨j, by omega, rest⟩

/-- Every stored entry has an earlier creation event on this very trace. -/
theorem trace_generated (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (n : NodeId C) (e : LogEntry) (he : e ∈ ((run.state k).servers n).log) :
    TraceGenerated run k e := by
  induction k using Nat.strong_induction_on generalizing n e with
  | h k ih =>
    cases k with
    | zero => rw [run.initial] at he; simp [initState] at he
    | succ k =>
      have old : ∀ node, e ∈ ((run.state k).servers node).log → TraceGenerated run (k+1) e := by
        intro node hmem
        exact (ih k (by omega) (by omega) node e hmem).mono (by omega)
      have st := run.transition k (by omega)
      generalize hnext : run.state (k+1) = next at st he
      cases st with
      | @append owner cmd hl =>
        by_cases hn : n = owner
        · subst n
          simp only [leaderAppend, setServer, Function.update_self, List.mem_append,
            List.mem_singleton] at he
          rcases he with he | he
          · exact old owner he
          · exact ⟨k, by omega, owner, cmd, hl, he, hnext⟩
        · apply old n
          simpa [leaderAppend, setServer, Function.update_of_ne hn] using he
      | @appendEntries v leader t prev pt lc entries before after hnet ht hp =>
        by_cases hn : n = v
        · subst n
          have hm : e ∈ appendEntriesLog ((run.state k).servers v).log prev entries := by
            simpa [handleAppend, setServer] using he
          rcases appendEntriesLog_mem hm with hlocal | hincoming
          · exact old v hlocal
          · have hpacket : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈
                (run.state k).network := by rw [hnet]; simp
            have hw : AppendWitness run k t leader prev pt entries :=
              network_witness run k (by omega) _ hpacket
            obtain ⟨j, count, hj, _hrole, _hterm, _hprev, _hpt, hentries⟩ := hw
            rw [hentries] at hincoming
            have hsource := List.mem_of_mem_drop (List.mem_of_mem_take hincoming)
            exact (ih j (by omega) (by omega) leader e hsource).mono (by omega)
        · apply old n
          simpa [handleAppend, setServer, Function.update_of_ne hn] using he
      | _ =>
        apply old n
        simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
          receiveAppendReply, commitLeader, denyAppend, consume, setServer,
          Function.update_apply] at he
        (try split_ifs at he) <;> simp_all

/-- A same-trace leader snapshot of the entry's own term contains that entry. -/
theorem trace_record_origin (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (n : NodeId C) (e : LogEntry) (he : e ∈ ((run.state k).servers n).log) :
    ∃ j, j ≤ k ∧ ∃ owner,
      ((run.state j).servers owner).role = .leader ∧
      ((run.state j).servers owner).currentTerm = e.term ∧
      e ∈ ((run.state j).servers owner).log := by
  obtain ⟨j, hj, owner, cmd, hr, heq, hnext⟩ := trace_generated run k hk n e he
  refine ⟨j+1, by omega, owner, ?_, ?_, ?_⟩
  all_goals rw [hnext]; simp [leaderAppend, setServer, hr, heq]

end DistributedRaftTraceOrigins
