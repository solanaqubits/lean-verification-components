/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftNetworkInduction

/-! Chronological RPC evidence on one finite operational execution. -/
namespace DistributedRaftEventHistory

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry lastIndex lastTerm)
open DistributedRaftStateMachine
open DistributedRaftNetworkInduction

structure Execution (C : Cluster) where
  length : ℕ
  state : ℕ → GlobalState C
  initial : state 0 = initState C
  transition : ∀ i, i < length → Step (state i) (state (i + 1))

variable {C : Cluster}

theorem Execution.reachable (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    Reachable (run.state k) := by
  induction k with
  | zero => rw [run.initial]; exact .init
  | succ k ih => exact (ih (by omega)).step (run.transition k (by omega))

theorem Execution.path (run : Execution C) (a b : ℕ) (hab : a ≤ b)
    (hb : b ≤ run.length) : Relation.ReflTransGen Step (run.state a) (run.state b) := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact .refl
  | succ b ih =>
    by_cases he : a = b + 1
    · subst a; exact .refl
    · exact (ih (by omega) (by omega)).tail (run.transition b (by omega))

/-- A request retains the exact candidate snapshot of its timeout event. -/
def RequestWitness (run : Execution C) (k t : ℕ) (c : NodeId C) (li lt : ℕ) : Prop :=
  ∃ i, i < k ∧ ((run.state i).servers c).role ≠ .leader ∧
    t = ((run.state i).servers c).currentTerm + 1 ∧
    li = lastIndex ((run.state i).servers c).log ∧
    lt = lastTerm ((run.state i).servers c).log ∧
    run.state (i + 1) = startElection (run.state i) c

/-- Positive acknowledgments are generated only by actual successful deliveries. -/
def AckWitness (run : Execution C) (k t : ℕ) (leader v : NodeId C) (matched : ℕ) : Prop :=
  ∃ i prev pt entries lc before after, i < k ∧
    (run.state i).network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after ∧
    t = ((run.state i).servers v).currentTerm ∧
    prevMatches ((run.state i).servers v).log prev pt ∧
    matched = prev + entries.length ∧
    run.state (i + 1) = handleAppend (run.state i) v leader prev entries lc before after

theorem RequestWitness.mono {run : Execution C} {k k' t : ℕ} {c : NodeId C} {li lt : ℕ}
    (h : RequestWitness run k t c li lt) (hk : k ≤ k') : RequestWitness run k' t c li lt := by
  obtain ⟨i, hi, rest⟩ := h
  exact ⟨i, by omega, rest⟩

theorem AckWitness.mono {run : Execution C} {k k' t : ℕ} {c v : NodeId C} {matched : ℕ}
    (h : AckWitness run k t c v matched) (hk : k ≤ k') : AckWitness run k' t c v matched := by
  obtain ⟨i, prev, pt, entries, lc, before, after, hi, rest⟩ := h
  exact ⟨i, prev, pt, entries, lc, before, after, by omega, rest⟩

/-- The contiguous batch was sent from a leader snapshot in this same execution. -/
def AppendWitness (run : Execution C) (k t : ℕ) (leader : NodeId C)
    (prev pt : ℕ) (entries : List LogEntry) : Prop :=
  ∃ j count, j ≤ k ∧ ((run.state j).servers leader).role = .leader ∧
    ((run.state j).servers leader).currentTerm = t ∧
    prev ≤ ((run.state j).servers leader).log.length ∧
    pt = termAt ((run.state j).servers leader).log prev ∧
    entries = (((run.state j).servers leader).log.drop prev).take count

theorem AppendWitness.mono {run : Execution C} {k k' t : ℕ} {leader : NodeId C}
    {prev pt : ℕ} {entries : List LogEntry}
    (h : AppendWitness run k t leader prev pt entries) (hk : k ≤ k') :
    AppendWitness run k' t leader prev pt entries := by
  obtain ⟨j, count, hj, rest⟩ := h
  exact ⟨j, count, by omega, rest⟩

def PacketWitness (run : Execution C) (k : ℕ) (m : Envelope C) : Prop :=
  match m.body with
  | .requestVote t c li lt => RequestWitness run k t c li lt
  | .appendEntries t leader prev pt entries _ => AppendWitness run k t leader prev pt entries
  | .appendEntriesReply t true matched v => AckWitness run k t m.destination v matched
  | _ => True

def NetworkWitness (run : Execution C) (k : ℕ) : Prop :=
  ∀ m ∈ (run.state k).network, PacketWitness run k m

theorem PacketWitness.mono {run : Execution C} {k k' : ℕ} {m : Envelope C}
    (h : PacketWitness run k m) (hk : k ≤ k') : PacketWitness run k' m := by
  rcases m with ⟨dst, body⟩
  cases body with
  | requestVote => exact RequestWitness.mono h hk
  | appendEntriesReply t success matched v =>
    cases success
    · trivial
    · exact AckWitness.mono h hk
  | requestVoteReply => trivial
  | appendEntries => exact AppendWitness.mono h hk

theorem network_witness_step (run : Execution C) (k : ℕ)
    (h : NetworkWitness run k) (st : Step (run.state k) (run.state (k + 1))) :
    NetworkWitness run (k + 1) := by
  have old : ∀ m ∈ (run.state k).network, PacketWitness run (k + 1) m :=
    fun m hm => (h m hm).mono (by omega)
  intro m hm
  generalize he : run.state (k + 1) = next at st hm
  cases st with
  | observe => exact old m hm
  | elect => exact old m hm
  | commit => exact old m hm
  | timeout n hn =>
    simp only [startElection, List.mem_append] at hm
    rcases hm with hm | hm
    · exact old m hm
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨k, by omega, hn, rfl, rfl, rfl, he⟩
  | @append leader cmd hn =>
    simp only [leaderAppend, List.mem_append] at hm
    rcases hm with hm | hm
    · exact old m hm
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
      refine ⟨k + 1, 1, le_rfl, ?_, ?_, ?_, ?_, ?_⟩
      · rw [he]; simp [leaderAppend, setServer, hn]
      · rw [he]; simp [leaderAppend, setServer]
      · rw [he]; simp [leaderAppend, setServer]
      · rw [he]
        simpa only [leaderAppend, setServer, Function.update_self] using
          DistributedRaftNetworkLogLemmas.termAt_prefix
            (List.prefix_append ((run.state k).servers leader).log
              [⟨((run.state k).servers leader).log.length + 1,
                ((run.state k).servers leader).currentTerm, cmd⟩]) _ le_rfl
      · rw [he]; simp [leaderAppend, setServer]
  | @replicate leader v prev count hn hne hp =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact old m hm
    · exact ⟨k, count, by omega, hn, rfl, hp, rfl, rfl⟩
  | vote hnet ht hv =>
    simp only [grantVote, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · trivial
  | voteReply hnet ht hv => exact old m (packet_remainder hnet hm)
  | @appendEntries v leader t prev pt lc entries before after hnet ht hp =>
    simp only [handleAppend, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · change AckWitness run (k + 1) _ leader v (prev + entries.length)
      refine ⟨k, prev, pt, entries, lc, before, after, by omega, ?_, rfl, hp, rfl, he⟩
      simpa only [ht] using hnet
  | appendReply hnet ht hv => exact old m (packet_remainder hnet hm)
  | rejectVote hnet ht hv =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · trivial
  | rejectAppend hnet ht hv =>
    simp only [denyAppend, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · trivial
  | drop hnet => exact old m (packet_remainder hnet hm)
  | duplicate hm' =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact old _ hm'
    · exact old m hm

theorem network_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    NetworkWitness run k := by
  induction k with
  | zero => intro m hm; rw [run.initial] at hm; simp [initState] at hm
  | succ k ih => exact network_witness_step run k (ih (by omega)) (run.transition k (by omega))

/-- Every persistent ballot is tied to its actual local vote event. -/
inductive VoteWitness (run : Execution C) (k t : ℕ) (v c : NodeId C) : Prop where
  | selfVote (i : ℕ) : i < k → v = c →
      ((run.state i).servers c).role ≠ .leader →
      t = ((run.state i).servers c).currentTerm + 1 →
      run.state (i + 1) = startElection (run.state i) c → VoteWitness run k t v c
  | granted (i li lt : ℕ) (before after : List (Envelope C)) : i < k →
      (run.state i).network = before ++ ⟨v, .requestVote t c li lt⟩ :: after →
      t = ((run.state i).servers v).currentTerm →
      mayVote ((run.state i).servers v) c li lt →
      RequestWitness run i t c li lt →
      run.state (i + 1) = grantVote (run.state i) v c before after → VoteWitness run k t v c

theorem VoteWitness.mono {run : Execution C} {k k' t : ℕ} {v c : NodeId C}
    (h : VoteWitness run k t v c) (hk : k ≤ k') : VoteWitness run k' t v c := by
  cases h with
  | selfVote i hi he hr ht hs => exact .selfVote i (by omega) he hr ht hs
  | granted i li lt before after hi hn ht hv hw hs =>
    exact .granted i li lt before after (by omega) hn ht hv hw hs

def CastWitness (run : Execution C) (k : ℕ) : Prop :=
  ∀ t v c, (t, v, c) ∈ (run.state k).cast → VoteWitness run k t v c

theorem cast_witness_step (run : Execution C) (k : ℕ)
    (h : CastWitness run k) (net : NetworkWitness run k)
    (st : Step (run.state k) (run.state (k + 1))) : CastWitness run (k + 1) := by
  have old : ∀ t v c, (t, v, c) ∈ (run.state k).cast → VoteWitness run (k + 1) t v c :=
    fun t v c hm => (h t v c hm).mono (by omega)
  intro t v c hm
  generalize he : run.state (k + 1) = next at st hm
  cases st with
  | timeout n hn =>
    simp only [startElection, Finset.mem_insert, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · exact .selfVote k (by omega) rfl hn rfl he
    · exact old t v c hm
  | @vote voter candidate tr li lt before after hnet ht hv =>
    simp only [grantVote, Finset.mem_insert, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl⟩ | hm
    · have hp : (⟨v, .requestVote tr c li lt⟩ : Envelope C) ∈ (run.state k).network := by
        rw [hnet]; simp
      have hw : RequestWitness run k tr c li lt := net _ hp
      refine .granted k li lt before after (by omega) ?_ rfl hv ?_ he
      · simpa only [ht] using hnet
      · simpa only [ht] using hw
    · exact old t v c hm
  | _ => exact old t v c hm

theorem cast_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length) : CastWitness run k := by
  induction k with
  | zero => intro t v c hm; rw [run.initial] at hm; simp [initState] at hm
  | succ k ih =>
    exact cast_witness_step run k (ih (by omega))
      (network_witness run k (by omega)) (run.transition k (by omega))

theorem received_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (t : ℕ) (v c : NodeId C) (hm : (t, v, c) ∈ (run.state k).received) :
    VoteWitness run k t v c :=
  cast_witness run k hk t v c ((transport_reachable (run.reachable k hk)).received hm)

/-- A positive match counter has a historical successful-delivery acknowledgment
in the leader's current tenure. It need not describe the follower's current log. -/
def MatchWitness (run : Execution C) (k : ℕ) : Prop :=
  ∀ leader, ((run.state k).servers leader).role = .leader → ∀ v i, 0 < i →
    i ≤ ((run.state k).servers leader).matchIndex v →
    ∃ matched, i ≤ matched ∧
      AckWitness run k ((run.state k).servers leader).currentTerm leader v matched

theorem match_witness_step (run : Execution C) (k : ℕ)
    (h : MatchWitness run k) (net : NetworkWitness run k)
    (st : Step (run.state k) (run.state (k + 1))) : MatchWitness run (k + 1) := by
  have old : ∀ leader, ((run.state k).servers leader).role = .leader → ∀ v i, 0 < i →
      i ≤ ((run.state k).servers leader).matchIndex v →
      ∃ matched, i ≤ matched ∧
        AckWitness run (k + 1) ((run.state k).servers leader).currentTerm leader v matched := by
    intro leader hl v i hi hm
    obtain ⟨matched, hb, hw⟩ := h leader hl v i hi hm
    exact ⟨matched, hb, hw.mono (by omega)⟩
  intro leader hl v i hi hm
  generalize he : run.state (k + 1) = next at st hl hm ⊢
  cases st with
  | @appendReply n follower t matched before after hnet ht hn =>
    simp only [receiveAppendReply, setServer, Function.update_apply] at hl hm ⊢
    by_cases hln : leader = n
    · subst leader
      simp only [ite_true] at hl hm ⊢
      by_cases hv : v = follower
      · subst v
        simp only [Function.update_self] at hm
        rcases (le_max_iff.mp hm) with hold | hnew
        · exact old n hn follower i hi hold
        · have hp : (⟨n, .appendEntriesReply t true matched follower⟩ : Envelope C) ∈
              (run.state k).network := by rw [hnet]; simp
          have hw : AckWitness run k t n follower matched := net _ hp
          exact ⟨matched, hnew, ht ▸ hw.mono (by omega)⟩
      · simp only [Function.update_of_ne hv] at hm
        exact old n hn v i hi hm
    · simp only [hln, ite_false] at hl hm ⊢
      exact old leader hl v i hi hm
  | _ =>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, denyAppend, consume, commitLeader, setServer,
      Function.update_apply] at hl hm ⊢
    (try split_ifs at hl hm ⊢) <;> simp_all

theorem match_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length) : MatchWitness run k := by
  induction k with
  | zero => intro leader hl; rw [run.initial] at hl; simp [initState] at hl
  | succ k ih =>
    exact match_witness_step run k (ih (by omega)) (network_witness run k (by omega))
      (run.transition k (by omega))

/-- Election evidence identifies the exact earlier majority-counting step. -/
def ElectionWitness (run : Execution C) (k t : ℕ) (c : NodeId C) : Prop :=
  ∃ i, i < k ∧ ((run.state i).servers c).role = .candidate ∧
    t = ((run.state i).servers c).currentTerm ∧
    DistributedRaftLeaderCompleteness.majority C
      (votesFor (run.state i).received t c) ∧
    run.state (i + 1) = becomeLeader (run.state i) c

theorem ElectionWitness.mono {run : Execution C} {k k' t : ℕ} {c : NodeId C}
    (h : ElectionWitness run k t c) (hk : k ≤ k') : ElectionWitness run k' t c := by
  obtain ⟨i, hi, rest⟩ := h
  exact ⟨i, by omega, rest⟩

def ElectionsWitness (run : Execution C) (k : ℕ) : Prop :=
  ∀ t c, (t, c) ∈ (run.state k).elected → ElectionWitness run k t c

theorem elections_witness_step (run : Execution C) (k : ℕ)
    (h : ElectionsWitness run k) (st : Step (run.state k) (run.state (k + 1))) :
    ElectionsWitness run (k + 1) := by
  have old : ∀ t c, (t, c) ∈ (run.state k).elected → ElectionWitness run (k + 1) t c :=
    fun t c hm => (h t c hm).mono (by omega)
  intro t c hm
  generalize he : run.state (k + 1) = next at st hm
  cases st with
  | elect hc hq =>
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · exact ⟨k, by omega, hc, rfl, hq, he⟩
    · exact old t c hm
  | _ => exact old t c hm

theorem elections_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    ElectionsWitness run k := by
  induction k with
  | zero => intro t c hm; rw [run.initial] at hm; simp [initState] at hm
  | succ k ih => exact elections_witness_step run k (ih (by omega)) (run.transition k (by omega))

theorem leader_election_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (c : NodeId C) (hc : ((run.state k).servers c).role = .leader) :
    ElectionWitness run k ((run.state k).servers c).currentTerm c :=
  elections_witness run k hk _ c ((elections_reachable (run.reachable k hk)).2 c hc)

end DistributedRaftEventHistory
