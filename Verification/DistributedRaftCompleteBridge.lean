/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftTraceMatching
import Verification.DistributedRaftEventHistory
import Verification.DistributedRaftLogOrder
import Verification.DistributedRaftTraceOrigins
import Verification.DistributedRaftCommittedPrefixLemmas
import Verification.DistributedRaftVoterRetention

/-! # Operational commitment and the Raft completeness bridge -/
namespace DistributedRaftCompleteBridge

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry majority)
open DistributedRaftStateMachine
open DistributedRaftNetworkHistory
open DistributedRaftNetworkInduction
open DistributedRaftTraceMatching
open DistributedRaftEventHistory
open DistributedRaftLogOrder
open DistributedRaftCommittedPrefixLemmas
open DistributedRaftVoterRetention
open DistributedRaftTraceOrigins
open DistributedRaftLeaderCompleteness (lastEntry lastTerm lastIndex logUpToDate lastEntry_mem)

variable {C : Cluster}

/-- A real operational commit event, including its unmodified local guards. -/
structure CommitEvent (run : Execution C) (k : ℕ) (leader : NodeId C) (index : ℕ) : Prop where
  within : k < run.length
  leaderRole : ((run.state k).servers leader).role = .leader
  withinLog : index ≤ ((run.state k).servers leader).log.length
  currentTerm : termAt ((run.state k).servers leader).log index =
    ((run.state k).servers leader).currentTerm
  quorum : majority C (replicationQuorum (run.state k) leader index)
  next : run.state (k + 1) = commitLeader (run.state k) leader index

/-- The entry belongs to the prefix certified by a real commit step in the
same finite execution ending at `s`. Earlier-term prefix entries are included. -/
def committedInTerm (s : GlobalState C) (e : LogEntry) (t : ℕ) : Prop :=
  ∃ run : Execution C, ∃ k leader index,
    run.state run.length = s ∧ CommitEvent run k leader index ∧
    ((run.state k).servers leader).currentTerm = t ∧
    e ∈ (((run.state k).servers leader).log.take index)

theorem snapshot_matching (run : Execution C) (a b : ℕ)
    (ha : a ≤ run.length) (hb : b ≤ run.length) (i j : NodeId C) :
    LogMatching ((run.state a).servers i).log ((run.state b).servers j).log := by
  by_cases he : a = b
  · subst b
    exact reachable_global_log_matching _ (run.reachable a ha) i j
  rcases le_total a b with hab | hba
  · exact historical_log_matching (run.reachable a ha) (run.path a b hab hb) i j
  · exact DistributedRaftNetworkLogLemmas.matching_symm
      (historical_log_matching (run.reachable b hb) (run.path b a hba ha) j i)

/-- Every snapshot of the unique leader in one term is prefix-comparable. -/
theorem same_term_snapshots_comparable (run : Execution C) (a b : ℕ)
    (ha : a ≤ run.length) (hb : b ≤ run.length) (i j : NodeId C)
    (hi : ((run.state a).servers i).role = .leader)
    (hj : ((run.state b).servers j).role = .leader)
    (ht : ((run.state a).servers i).currentTerm =
      ((run.state b).servers j).currentTerm) :
    ((run.state a).servers i).log.IsPrefix ((run.state b).servers j).log ∨
    ((run.state b).servers j).log.IsPrefix ((run.state a).servers i).log := by
  have ei := (elections_reachable (run.reachable a ha)).2 i hi
  have ej := (elections_reachable (run.reachable b hb)).2 j hj
  have eil := elected_path_monotone (run.path a run.length ha le_rfl) ei
  have ejl := elected_path_monotone (run.path b run.length hb le_rfl) ej
  have hij : i = j := election_history_safety (run.reachable _ le_rfl) _ i j eil
    (ht ▸ ejl)
  subst j
  rcases le_total a b with hab | hba
  · exact Or.inl (elected_same_term_log_prefix (run.reachable a ha)
      (run.path a b hab hb) _ i ei ht.symm)
  · exact Or.inr (elected_same_term_log_prefix (run.reachable b hb)
      (run.path b a hba ha) _ i ej ht)

/-- A successful upcoming election excludes every earlier leader in its term. -/
theorem no_leader_before_election (run : Execution C) (election : ℕ)
    (helection : election < run.length) (candidate : NodeId C)
    (hcandidate : ((run.state election).servers candidate).role = .candidate)
    (hnext : run.state (election + 1) = becomeLeader (run.state election) candidate)
    (j : ℕ) (hj : j ≤ election) (n : NodeId C)
    (hrole : ((run.state j).servers n).role = .leader) :
    ((run.state j).servers n).currentTerm ≠
      ((run.state election).servers candidate).currentTerm := by
  intro ht
  have ej := (elections_reachable (run.reachable j (by omega))).2 n hrole
  have ee := elected_path_monotone (run.path j election hj (by omega)) ej
  have en := elected_path_monotone (run.path election (election + 1) (by omega)
    (by omega)) ee
  have ec : (((run.state election).servers candidate).currentTerm, candidate) ∈
      (run.state (election + 1)).elected := by rw [hnext]; simp [becomeLeader]
  have eqn : n = candidate := election_history_safety
    (run.reachable (election + 1) (by omega)) _ n candidate en (ht ▸ ec)
  subst n
  have hl := (reachable_history (run.reachable election (by omega))).tenure _ candidate
    ee ht.symm
  rw [hcandidate] at hl
  contradiction

/-- A commit index in a reachable execution is strictly positive. -/
theorem CommitEvent.positive {run : Execution C} {k : ℕ} {n : NodeId C} {i : ℕ}
    (hc : CommitEvent run k n i) : 0 < i := by
  have ht := reachable_active_positive (run.reachable k (by have := hc.within; omega)) n
    (by rw [hc.leaderRole]; decide)
  have he := hc.currentTerm
  by_contra hz
  have hi : i = 0 := by omega
  simp [hi, termAt] at he
  omega

/-- Every member counted by a real commit has a prior same-term replica
snapshot of the committed prefix. Delayed acknowledgments are kept historical. -/
theorem commit_quorum_replica {run : Execution C} {k : ℕ} {leader : NodeId C}
    {index : ℕ} (hc : CommitEvent run k leader index) (v : NodeId C)
    (hv : v ∈ replicationQuorum (run.state k) leader index) :
    ∃ a, a ≤ k ∧
      ((run.state a).servers v).currentTerm = ((run.state k).servers leader).currentTerm ∧
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state a).servers v).log := by
  have hk : k ≤ run.length := Nat.le_of_lt hc.within
  simp only [replicationQuorum, Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with rfl | hv
  · exact ⟨k, le_rfl, rfl, List.take_prefix _ _⟩
  obtain ⟨matched, hmatched, a, prev, pt, entries, lc, before, after,
    ha, hnet, ht, hprev, hlen, hnext⟩ :=
    match_witness run k hk leader hc.leaderRole v index hc.positive hv
  have hpacket : (⟨v, .appendEntries ((run.state k).servers leader).currentTerm
      leader prev pt entries lc⟩ : Envelope C) ∈ (run.state a).network := by
    rw [hnet]; simp
  have hw : AppendWitness run a ((run.state k).servers leader).currentTerm
      leader prev pt entries := network_witness run a (by omega) _ hpacket
  obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
    hsourcePrev, hsourcePt, hentries⟩ := hw
  let source := ((run.state sourceTime).servers leader).log
  have sourceLength : index ≤ source.length := by
    rw [hentries] at hlen
    simp only [List.length_take, List.length_drop] at hlen
    dsimp [source]
    omega
  have hcomparable := same_term_snapshots_comparable run sourceTime k (by omega) hk
    leader leader hsourceRole hc.leaderRole hsourceTerm
  have hprefix : (((run.state k).servers leader).log.take index).IsPrefix source := by
    rcases hcomparable with hs | hs
    · exact List.prefix_of_prefix_length_le (List.take_prefix _ _) hs
        (by simp only [List.length_take]; omega)
    · exact (List.take_prefix _ _).trans hs
  have hmatching := snapshot_matching run a sourceTime (by omega) (by omega) v leader
  have hpreserved := covered_prefix_installed hprefix hmatching prev count hsourcePrev
    (hsourcePt ▸ hprev) (by
      simp only [List.length_take]
      rw [hentries] at hlen
      simp only [List.length_take, List.length_drop] at hlen
      omega)
  refine ⟨a + 1, by omega, ?_, ?_⟩
  · rw [hnext]
    simpa [handleAppend, setServer] using ht.symm
  · rw [hnext]
    simpa only [handleAppend, setServer, Function.update_self, hentries] using hpreserved

theorem CommitEvent.anchor {run : Execution C} {k : ℕ} {n : NodeId C} {index : ℕ}
    (hc : CommitEvent run k n index) :
    ∃ e : LogEntry, e ∈ (((run.state k).servers n).log.take index) ∧
      e.index = index ∧ e.term = ((run.state k).servers n).currentTerm := by
  have hpos := hc.positive
  have hib := hc.withinLog
  have hi : index - 1 < ((run.state k).servers n).log.length := by omega
  let e := ((run.state k).servers n).log[index - 1]
  have he : ((run.state k).servers n).log[index - 1]? = some e :=
    List.getElem?_eq_getElem hi
  have hm : e ∈ (((run.state k).servers n).log.take index) := by
    apply List.mem_of_getElem? (i := index - 1)
    rw [List.getElem?_take_of_lt (by omega)]
    exact he
  have hind := reachable_entry_index (run.reachable k (Nat.le_of_lt hc.within)) n _ e he
  refine ⟨e, hm, by omega, ?_⟩
  have ht := hc.currentTerm
  simpa only [termAt, Nat.ne_of_gt hpos, ↓reduceIte, he, Option.getD_some] using ht

/-- Up-to-Date transfers the commit prefix using origin and historical matching.
Strictly newer last terms use the induction hypothesis for earlier leaders. -/
theorem candidate_prefix_of_upToDate (run : Execution C) (k : ℕ) (leader : NodeId C)
    (index : ℕ) (hc : CommitEvent run k leader index)
    (election : ℕ) (helection : election ≤ run.length) (candidate : NodeId C)
    (hcandidate : ((run.state election).servers candidate).role = .candidate)
    (b : ℕ) (hb : b ≤ run.length) (v : NodeId C)
    (hp : (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state b).servers v).log)
    (hup : logUpToDate ((run.state election).servers candidate).log
      ((run.state b).servers v).log)
    (earlier : ∀ j, j ≤ run.length → ∀ n,
      ((run.state j).servers n).role = .leader →
      ((run.state k).servers leader).currentTerm < ((run.state j).servers n).currentTerm →
      ((run.state j).servers n).currentTerm <
        ((run.state election).servers candidate).currentTerm →
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state j).servers n).log) :
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state election).servers candidate).log := by
  let cLog := ((run.state election).servers candidate).log
  let vLog := ((run.state b).servers v).log
  let p := ((run.state k).servers leader).log.take index
  obtain ⟨anchor, hanchor, haindex, haterm⟩ := hc.anchor
  have hvanchor : anchor ∈ vLog := hp.sublist.subset hanchor
  have wfv := reachable_wellFormed (run.reachable b hb) v
  have wfc := reachable_wellFormed (run.reachable election helection) candidate
  have hvbounds := wfv.last_bounds anchor hvanchor
  change anchor.index ≤ lastIndex vLog ∧ anchor.term ≤ lastTerm vLog at hvbounds
  have htpos := reachable_active_positive (run.reachable k (Nat.le_of_lt hc.within))
    leader (by rw [hc.leaderRole]; decide)
  have htc : ((run.state k).servers leader).currentTerm ≤ lastTerm cLog := by
    dsimp [logUpToDate] at hup
    change lastTerm vLog < lastTerm cLog ∨
      (lastTerm cLog = lastTerm vLog ∧ lastIndex vLog ≤ lastIndex cLog) at hup
    rw [haterm] at hvbounds
    rcases hup with h | ⟨h, _⟩ <;> omega
  have hcne : cLog ≠ [] := by
    intro he
    have hz : lastTerm cLog = 0 := by simp [he, lastTerm, lastEntry]
    omega
  have hlast : lastEntry cLog ∈ cLog := lastEntry_mem hcne
  obtain ⟨originTime, horiginTime, owner, hownerRole, hownerTerm, hownerEntry⟩ :=
    trace_record_origin run election helection candidate (lastEntry cLog) hlast
  have hoend : originTime ≤ run.length := by omega
  have wfo := reachable_wellFormed (run.reachable originTime hoend) owner
  have hupper : ((run.state originTime).servers owner).currentTerm <
      ((run.state election).servers candidate).currentTerm := by
    rw [hownerTerm]
    exact reachable_candidate_strict (run.reachable election helection) candidate
      hcandidate _ hlast
  have hplen : p.length = index := by
    simp only [p, List.length_take, Nat.min_eq_left hc.withinLog]
  have hpOrigin : p.IsPrefix ((run.state originTime).servers owner).log := by
    by_cases heq : ((run.state k).servers leader).currentTerm = lastTerm cLog
    · have candLength : index ≤ cLog.length := by
        have hclen := wellFormed_lastIndex_eq_length wfc
        have hvlen := wellFormed_lastIndex_eq_length wfv
        dsimp [logUpToDate] at hup
        change lastTerm vLog < lastTerm cLog ∨
          (lastTerm cLog = lastTerm vLog ∧ lastIndex vLog ≤ lastIndex cLog) at hup
        have hpl := hp.length_le
        change p.length ≤ vLog.length at hpl
        rw [haterm] at hvbounds
        change lastIndex cLog = cLog.length at hclen
        change lastIndex vLog = vLog.length at hvlen
        rw [hplen] at hpl
        rcases hup with h | ⟨_, hlen⟩ <;> omega
      have hlastIndex : (lastEntry cLog).index = cLog.length :=
        wellFormed_lastIndex_eq_length wfc
      have hindexBound := (wfo.last_bounds _ hownerEntry).1
      rw [wellFormed_lastIndex_eq_length wfo, hlastIndex] at hindexBound
      have compare := same_term_snapshots_comparable run originTime k hoend
        (Nat.le_of_lt hc.within) owner leader hownerRole hc.leaderRole
        (hownerTerm.trans heq.symm)
      rcases compare with h | h
      · exact List.prefix_of_prefix_length_le (List.take_prefix _ _) h (by omega)
      · exact (List.take_prefix _ _).trans h
    · apply earlier originTime hoend owner hownerRole _ hupper
      rw [hownerTerm]
      change ((run.state k).servers leader).currentTerm < lastTerm cLog
      omega
  have hposition : p.length ≤ (lastEntry cLog).index := by
    have hanchorOrigin := hpOrigin.sublist.subset hanchor
    by_cases heq : anchor.term = (lastEntry cLog).term
    · have hci := wellFormed_lastIndex_eq_length wfc
      have hvi := wellFormed_lastIndex_eq_length wfv
      dsimp [logUpToDate] at hup
      change lastTerm vLog < lastTerm cLog ∨
        (lastTerm cLog = lastTerm vLog ∧ lastIndex vLog ≤ lastIndex cLog) at hup
      have hbound := wfv.last_bounds anchor hvanchor
      change anchor.index ≤ lastIndex vLog ∧ anchor.term ≤ lastTerm vLog at hbound
      change anchor.term = lastTerm cLog at heq
      have hpl := hp.length_le
      change p.length ≤ vLog.length at hpl
      change lastIndex cLog = cLog.length at hci
      change lastIndex vLog = vLog.length at hvi
      change p.length ≤ lastIndex cLog
      rcases hup with h | ⟨_, hlen⟩ <;> omega
    · have htne : anchor.term ≠ lastTerm cLog := heq
      have hord := wfo.term_order anchor hanchorOrigin _ hownerEntry
        (by change anchor.term < lastTerm cLog; rw [haterm] at htne ⊢; omega)
      omega
  exact matching_transfers_prefix wfo wfc
    (snapshot_matching run originTime election hoend helection owner candidate)
    hpOrigin _ _ hownerEntry hlast rfl rfl hposition

/-- Strong induction on leader terms on one execution. The commit quorum and
winning vote quorum intersect in a real replica and a real later vote event. -/
theorem commit_prefix_in_later_leader (run : Execution C) (k : ℕ)
    (leader : NodeId C) (index : ℕ) (hc : CommitEvent run k leader index) :
    ∀ u, ((run.state k).servers leader).currentTerm < u →
      ∀ j, j ≤ run.length → ∀ n, ((run.state j).servers n).role = .leader →
      ((run.state j).servers n).currentTerm = u →
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state j).servers n).log := by
  intro u
  induction u using Nat.strong_induction_on with
  | h u ih =>
    intro htu j hj n hn hnt
    obtain ⟨election, helection, hcandidate, het, hmajority, hnext⟩ :=
      leader_election_witness run j hj n hn
    have electionEnd : election ≤ run.length := by omega
    have electionTerm : ((run.state election).servers n).currentTerm = u :=
      het.symm.trans hnt
    have majorityVote : majority C (votesFor (run.state election).received
        ((run.state election).servers n).currentTerm n) := by
      simpa only [het] using hmajority
    obtain ⟨v, hv⟩ := DistributedRaftLeaderCompleteness.quorum_intersection C
      (replicationQuorum (run.state k) leader index)
      (votesFor (run.state election).received ((run.state election).servers n).currentTerm n)
      hc.quorum majorityVote
    obtain ⟨hvCommit, hvVote⟩ := Finset.mem_inter.mp hv
    obtain ⟨a, ha, hat, hap⟩ := commit_quorum_replica hc v hvCommit
    obtain ⟨b, hb, hbt, hup⟩ :=
      winning_voter_snapshot run election electionEnd n hcandidate v hvVote
    have aEnd : a ≤ run.length := by have := hc.within; omega
    have bEnd : b ≤ run.length := by omega
    have hab : a ≤ b := by
      by_contra h
      have mono := term_path_monotone (run.path b a (by omega) aEnd) v
      rw [hat, hbt, electionTerm] at mono
      omega
    have earlier : ∀ z, z ≤ run.length → ∀ owner,
        ((run.state z).servers owner).role = .leader →
        ((run.state k).servers leader).currentTerm <
          ((run.state z).servers owner).currentTerm →
        ((run.state z).servers owner).currentTerm <
          ((run.state election).servers n).currentTerm →
        (((run.state k).servers leader).log.take index).IsPrefix
          ((run.state z).servers owner).log := by
      intro z hz owner hrole hlow hhigh
      exact ih _ (by rw [electionTerm] at hhigh; exact hhigh) hlow z hz owner hrole rfl
    have voterPrefix := voter_prefix_retained run a b hab bEnd v
      (((run.state k).servers leader).log.take index) hap (by
        intro i hai hib t sender prev pt entries lc packet ht
        have hiEnd : i ≤ run.length := by omega
        have hw : AppendWitness run i t sender prev pt entries :=
          network_witness run i hiEnd _ packet
        obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries⟩ := hw
        refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries, ?_⟩
        have sourceEnd : sourceTime ≤ run.length := by omega
        have low := term_path_monotone (run.path a i hai hiEnd) v
        have high := term_path_monotone (run.path i b (by omega) bEnd) v
        rw [hat, ← ht] at low
        rw [← ht, hbt] at high
        have hne := no_leader_before_election run election (by omega) n hcandidate
          hnext sourceTime (by omega) sender hsourceRole
        have strictHigh : ((run.state sourceTime).servers sender).currentTerm <
            ((run.state election).servers n).currentTerm := by
          rw [hsourceTerm] at hne ⊢
          omega
        by_cases heq : t = ((run.state k).servers leader).currentTerm
        · have comparable := same_term_snapshots_comparable run sourceTime k sourceEnd
            (Nat.le_of_lt hc.within) sender leader hsourceRole hc.leaderRole
            (hsourceTerm.trans heq)
          rcases comparable with h | h
          · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
          · exact Or.inr ((List.take_prefix _ _).trans h)
        · exact Or.inr (earlier sourceTime sourceEnd sender hsourceRole
            (by rw [hsourceTerm]; omega) strictHigh))
    have candidatePrefix := candidate_prefix_of_upToDate run k leader index hc
      election electionEnd n hcandidate b bEnd v voterPrefix hup earlier
    have postElection : ((run.state (election + 1)).servers n).role = .leader := by
      rw [hnext]; simp [becomeLeader, setServer]
    have postTerm : ((run.state (election + 1)).servers n).currentTerm = u := by
      rw [hnext]; simpa [becomeLeader, setServer] using electionTerm
    have hfinalPrefix := elected_same_term_log_prefix
      (run.reachable (election + 1) (by omega)) (run.path (election + 1) j (by omega) hj)
      u n (by
        have elected := (elections_reachable (run.reachable (election + 1) (by omega))).2
          n postElection
        simpa only [postTerm] using elected) hnt
    apply List.IsPrefix.trans _ hfinalPrefix
    simpa only [hnext, becomeLeader, setServer, Function.update_self] using candidatePrefix

/-- Leader Completeness for actual commit events in the operational automaton.
The trace witness includes reachability; the explicit reachability parameter
keeps the public theorem aligned with other operational invariant statements. -/
theorem reachable_leader_completeness (s : GlobalState C) (_h_reach : Reachable s) :
    ∀ (e : LogEntry) (t₁ t₂ : ℕ) (leader : NodeId C),
      t₁ < t₂ → committedInTerm s e t₁ →
      (s.servers leader).role = .leader →
      (s.servers leader).currentTerm = t₂ → e ∈ (s.servers leader).log := by
  intro e t₁ t₂ leader hlt committed hrole hterm
  obtain ⟨run, k, owner, index, hend, hc, ht, he⟩ := committed
  have hp := commit_prefix_in_later_leader run k owner index hc t₂
    (by rw [ht]; exact hlt) run.length le_rfl leader (hend ▸ hrole) (hend ▸ hterm)
  rw [hend] at hp
  exact hp.sublist.subset he

/-- A replica which contains the whole directly committed prefix retains it
through every later operational transition of the same execution. -/
theorem committed_prefix_preserved (run : Execution C) (k : ℕ)
    (leader : NodeId C) (index : ℕ) (hc : CommitEvent run k leader index)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ run.length) (v : NodeId C)
    (initial : (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state a).servers v).log) :
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state b).servers v).log := by
  obtain ⟨anchor, hanchor, _hindex, haterm⟩ := hc.anchor
  have anchorAtA := initial.sublist.subset hanchor
  have lower := reachable_log_bound (run.reachable a (by omega)) v anchor anchorAtA
  rw [haterm] at lower
  apply voter_prefix_retained run a b hab hb v _ initial
  intro i hai hib t sender prev pt entries lc packet ht
  have hiEnd : i ≤ run.length := by omega
  have hw : AppendWitness run i t sender prev pt entries :=
    network_witness run i hiEnd _ packet
  obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
    hsourcePrev, hsourcePt, hentries⟩ := hw
  refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
    hsourcePrev, hsourcePt, hentries, ?_⟩
  have sourceEnd : sourceTime ≤ run.length := by omega
  have mono := term_path_monotone (run.path a i hai hiEnd) v
  rw [← ht] at mono
  by_cases heq : t = ((run.state k).servers leader).currentTerm
  · have comparable := same_term_snapshots_comparable run sourceTime k sourceEnd
      (Nat.le_of_lt hc.within) sender leader hsourceRole hc.leaderRole
      (hsourceTerm.trans heq)
    rcases comparable with h | h
    · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
    · exact Or.inr ((List.take_prefix _ _).trans h)
  · exact Or.inr (commit_prefix_in_later_leader run k leader index hc t (by omega)
      sourceTime sourceEnd sender hsourceRole hsourceTerm)

/-- The exported suite includes reachable Log Matching, actual commit-quorum
replicas, operational Leader Completeness, and temporal retention of commit prefixes. -/
structure RaftCompleteBridgeSuite : Prop where
  h_matching : ∀ {C : Cluster} (s : GlobalState C), Reachable s → GlobalLogMatching s
  h_replica : ∀ {C : Cluster} {run : Execution C} {k : ℕ} {leader : NodeId C}
    {index : ℕ}, CommitEvent run k leader index → ∀ v,
    v ∈ replicationQuorum (run.state k) leader index →
    ∃ a, a ≤ k ∧
      ((run.state a).servers v).currentTerm = ((run.state k).servers leader).currentTerm ∧
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state a).servers v).log
  h_completeness : ∀ {C : Cluster} (s : GlobalState C), Reachable s →
    ∀ (e : LogEntry) (t₁ t₂ : ℕ) (leader : NodeId C),
      t₁ < t₂ → committedInTerm s e t₁ →
      (s.servers leader).role = .leader →
      (s.servers leader).currentTerm = t₂ → e ∈ (s.servers leader).log
  h_retention : ∀ {C : Cluster} (run : Execution C) (k : ℕ)
    (leader : NodeId C) (index : ℕ), CommitEvent run k leader index →
    ∀ a b, a ≤ b → b ≤ run.length → ∀ v,
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state a).servers v).log →
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state b).servers v).log

theorem raft_complete_bridge_master_suite : RaftCompleteBridgeSuite := {
  h_matching := reachable_global_log_matching
  h_replica := commit_quorum_replica
  h_completeness := reachable_leader_completeness
  h_retention := committed_prefix_preserved
}

end DistributedRaftCompleteBridge
