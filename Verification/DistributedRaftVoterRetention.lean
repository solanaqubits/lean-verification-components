/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftEventHistory
import Verification.DistributedRaftCandidateHistory
import Verification.DistributedRaftCommittedPrefixLemmas

/-! Local retention along a real execution, with explicit source comparability.
The complete bridge derives this auxiliary premise by induction on election terms. -/
namespace DistributedRaftVoterRetention

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry logUpToDate)
open DistributedRaftStateMachine
open DistributedRaftEventHistory
open DistributedRaftCandidateHistory
open DistributedRaftCommittedPrefixLemmas

variable {C : Cluster}

/-- Historical source snapshots of currently acceptable deliveries are comparable
with the protected prefix. This is an auxiliary proof premise, never a Step guard. -/
def ComparableSourcesAt (run : Execution C) (i : ℕ) (v : NodeId C)
    (p : List LogEntry) : Prop :=
  ∀ t leader prev pt entries lc,
    (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ (run.state i).network →
    t = ((run.state i).servers v).currentTerm →
    ∃ j count, j ≤ i ∧ ((run.state j).servers leader).role = .leader ∧
      ((run.state j).servers leader).currentTerm = t ∧
      prev ≤ ((run.state j).servers leader).log.length ∧
      pt = termAt ((run.state j).servers leader).log prev ∧
      entries = (((run.state j).servers leader).log.drop prev).take count ∧
      (((run.state j).servers leader).log.IsPrefix p ∨
        p.IsPrefix ((run.state j).servers leader).log)

theorem voter_prefix_step (run : Execution C) (i : ℕ) (v : NodeId C) (p : List LogEntry)
    (hp : p.IsPrefix ((run.state i).servers v).log)
    (sources : ComparableSourcesAt run i v p)
    (st : Step (run.state i) (run.state (i + 1))) :
    p.IsPrefix ((run.state (i + 1)).servers v).log := by
  generalize he : run.state (i + 1) = next at st ⊢
  cases st with
  | @append n cmd hn =>
    by_cases hv : v = n
    · subst v
      simpa only [leaderAppend, setServer, Function.update_self] using
        hp.trans (List.prefix_append _ _)
    · simpa only [leaderAppend, setServer, Function.update_of_ne hv] using hp
  | @appendEntries dst leader t prev pt lc entries before after hnet ht hm =>
    by_cases hv : v = dst
    · subst v
      have packet : (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈
          (run.state i).network := by rw [hnet]; simp
      obtain ⟨j, count, _, _, _, _, _, entriesEq, comparable⟩ :=
        sources t leader prev pt entries lc packet ht
      simp only [handleAppend, setServer, Function.update_self]
      rw [entriesEq]
      exact comparable_prefix_retained hp comparable prev count
    · simpa only [handleAppend, setServer, Function.update_of_ne hv] using hp
  | _ =>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      receiveAppendReply, denyAppend, consume, commitLeader, setServer,
      Function.update_apply]
    (try split_ifs) <;> simp_all

/-- Prefix retention across every partial batch in the specified interval. -/
theorem voter_prefix_retained (run : Execution C) (a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ run.length) (v : NodeId C) (p : List LogEntry)
    (initial : p.IsPrefix ((run.state a).servers v).log)
    (sources : ∀ i, a ≤ i → i < b → ComparableSourcesAt run i v p) :
    p.IsPrefix ((run.state b).servers v).log := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact initial
  | succ b ih =>
    by_cases he : a = b + 1
    · subst a; exact initial
    · have previous := ih (by omega) (by omega) (fun i hai hib => sources i hai (by omega))
      exact voter_prefix_step run b v p previous (sources b (by omega) (by omega))
        (run.transition b (by omega))

/-- A counted ballot supplies a same-execution voter snapshot satisfying the
actual comparison rule against the candidate's unchanged campaign log. -/
theorem winning_voter_snapshot (run : Execution C) (election : ℕ)
    (helection : election ≤ run.length) (c : NodeId C)
    (hc : ((run.state election).servers c).role = .candidate) (v : NodeId C)
    (hv : v ∈ votesFor (run.state election).received
      ((run.state election).servers c).currentTerm c) :
    ∃ b, b ≤ election ∧
      ((run.state b).servers v).currentTerm = ((run.state election).servers c).currentTerm ∧
      logUpToDate ((run.state election).servers c).log ((run.state b).servers v).log := by
  have witness := received_witness run election helection _ v c (by simpa using hv)
  cases witness with
  | selfVote i hi hvc _ ht hs =>
    subst v
    have term : ((run.state (i + 1)).servers c).currentTerm =
        ((run.state election).servers c).currentTerm := by
      rw [hs]
      simpa only [startElection, setServer, Function.update_self] using ht.symm
    have logs := (candidate_path_log_eq
      (run.path (i + 1) election (by omega) helection) c hc term).2
    refine ⟨i + 1, by omega, term, ?_⟩
    rw [logs]
    exact Or.inr ⟨rfl, le_rfl⟩
  | granted i li lt before after hi _ ht guard req _ =>
    obtain ⟨hli, hlt⟩ := request_candidate_snapshot run election _ helection c li lt
      (req.mono (by omega)) hc rfl
    refine ⟨i, by omega, ht.symm, ?_⟩
    have rule := guard.2
    change _ < lt ∨ (_ = lt ∧ _ ≤ li) at rule
    rw [hli, hlt] at rule
    rcases rule with hnew | ⟨heq, hlen⟩
    · exact Or.inl hnew
    · exact Or.inr ⟨heq.symm, hlen⟩

end DistributedRaftVoterRetention
