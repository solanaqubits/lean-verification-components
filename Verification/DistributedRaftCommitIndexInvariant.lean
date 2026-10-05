/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftCompleteBridge

/-! Chronological certificates for operational commit indices. -/
namespace DistributedRaftCommitIndexInvariant

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry)
open DistributedRaftStateMachine
open DistributedRaftEventHistory
open DistributedRaftCompleteBridge
open DistributedRaftNetworkInduction
open DistributedRaftTraceMatching
open DistributedRaftVoterRetention
open DistributedRaftCommittedPrefixLemmas

variable {C : Cluster}

theorem commitIndex_step_monotone {s s' : GlobalState C} (st : Step s s')
    (v : NodeId C) : (s.servers v).commitIndex ≤ (s'.servers v).commitIndex := by
  cases st <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader,
      setServer, Function.update_apply] <;>
    (try split_ifs) <;> simp_all

/-- A smaller prefix of an actual committed prefix is protected once the
recipient has reached the committing term. This covers partial RPC batches. -/
theorem committed_subprefix_preserved (run : Execution C) (k : ℕ)
    (leader : NodeId C) (index : ℕ) (hc : CommitEvent run k leader index)
    (p : List LogEntry)
    (hp : p.IsPrefix (((run.state k).servers leader).log.take index))
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ run.length) (v : NodeId C)
    (lower : ((run.state k).servers leader).currentTerm ≤ ((run.state a).servers v).currentTerm)
    (initial : p.IsPrefix ((run.state a).servers v).log) :
    p.IsPrefix ((run.state b).servers v).log := by
  apply voter_prefix_retained run a b hab hb v p initial
  intro i hai hib t sender prev pt entries lc packet ht
  have hiEnd : i ≤ run.length := by omega
  obtain ⟨j, count, hj, hrole, hterm, hprev, hpt, hent⟩ :
      AppendWitness run i t sender prev pt entries := network_witness run i hiEnd _ packet
  refine ⟨j, count, hj, hrole, hterm, hprev, hpt, hent, ?_⟩
  have mono := term_path_monotone (run.path a i hai hiEnd) v
  rw [← ht] at mono
  by_cases heq : t = ((run.state k).servers leader).currentTerm
  · have comparable := same_term_snapshots_comparable run j k (by omega)
      (Nat.le_of_lt hc.within) sender leader hrole hc.leaderRole (hterm.trans heq)
    rcases comparable with hs | hs
    · exact List.prefix_or_prefix_of_prefix hs (hp.trans (List.take_prefix _ _))
    · exact Or.inr (hp.trans ((List.take_prefix _ _).trans hs))
  · exact Or.inr (hp.trans (commit_prefix_in_later_leader run k leader index hc t
      (by omega) j (by omega) sender hrole hterm))

/-- The certificate records one actual earlier commit event of this execution,
not merely a majority-shaped configuration. Empty prefixes need no event. -/
def PrefixCertificate (run : Execution C) (time term : ℕ) (p : List LogEntry) : Prop :=
  p = [] ∨ ∃ k leader index, k < time ∧ CommitEvent run k leader index ∧
    ((run.state k).servers leader).currentTerm ≤ term ∧
    p.IsPrefix (((run.state k).servers leader).log.take index)

theorem PrefixCertificate.mono {run : Execution C} {a b t u : ℕ} {p : List LogEntry}
    (h : PrefixCertificate run a t p) (hab : a ≤ b) (htu : t ≤ u) :
    PrefixCertificate run b u p := by
  rcases h with h | ⟨k, l, i, hk, hc, ht, hp⟩
  · exact Or.inl h
  · exact Or.inr ⟨k, l, i, by omega, hc, by omega, hp⟩

theorem PrefixCertificate.prefix {run : Execution C} {a t : ℕ} {p q : List LogEntry}
    (h : PrefixCertificate run a t p) (hq : q.IsPrefix p) : PrefixCertificate run a t q := by
  rcases h with rfl | ⟨k, l, i, hk, hc, ht, hp⟩
  · exact Or.inl (List.prefix_nil.mp hq)
  · exact Or.inr ⟨k, l, i, hk, hc, ht, hq.trans hp⟩

theorem PrefixCertificate.retained {run : Execution C} {a b : ℕ} {v : NodeId C}
    {p : List LogEntry}
    (h : PrefixCertificate run a ((run.state a).servers v).currentTerm p)
    (hab : a ≤ b) (hb : b ≤ run.length)
    (initial : p.IsPrefix ((run.state a).servers v).log) :
    p.IsPrefix ((run.state b).servers v).log := by
  rcases h with rfl | ⟨k, l, i, _, hc, ht, hp⟩
  · simp
  · exact committed_subprefix_preserved run k l i hc p hp a b hab hb v ht initial

/-- Each server's committed prefix is bounded and certified by actual history. -/
def ServerCertified (run : Execution C) (k : ℕ) (v : NodeId C) : Prop :=
  ((run.state k).servers v).commitIndex ≤ ((run.state k).servers v).log.length ∧
  PrefixCertificate run k ((run.state k).servers v).currentTerm
    (((run.state k).servers v).log.take ((run.state k).servers v).commitIndex)

/-- Strengthens the historical AppendWitness with evidence for leaderCommit.
The source snapshot and transmitted prefix belong to this very execution. -/
def CommitPacket (run : Execution C) (k : ℕ) (m : Envelope C) : Prop :=
  match m.body with
  | .appendEntries t leader prev pt entries lc =>
    ∃ j count, j ≤ k ∧ ((run.state j).servers leader).role = .leader ∧
      ((run.state j).servers leader).currentTerm = t ∧
      prev ≤ ((run.state j).servers leader).log.length ∧
      pt = termAt ((run.state j).servers leader).log prev ∧
      entries = (((run.state j).servers leader).log.drop prev).take count ∧
      lc ≤ ((run.state j).servers leader).log.length ∧
      PrefixCertificate run k t (((run.state j).servers leader).log.take lc)
  | _ => True

def NetworkCertified (run : Execution C) (k : ℕ) : Prop :=
  ∀ m ∈ (run.state k).network, CommitPacket run k m

theorem CommitPacket.mono {run : Execution C} {a b : ℕ} {m : Envelope C}
    (h : CommitPacket run a m) (hab : a ≤ b) : CommitPacket run b m := by
  rcases m with ⟨dst, body⟩
  cases body <;> try trivial
  case appendEntries t l prev pt entries lc =>
    obtain ⟨j, count, hj, hr, ht, hp, hpt, he, hc, cert⟩ := h
    exact ⟨j, count, by omega, hr, ht, hp, hpt, he, hc, cert.mono hab le_rfl⟩

theorem take_of_prefix_length {α : Type*} {p l : List α} {c : ℕ}
    (hp : p.IsPrefix l) (hc : p.length = c) : l.take c = p := by
  obtain ⟨q, rfl⟩ := hp
  rw [← hc]
  simp

theorem certified_retained (run : Execution C) (k : ℕ) (hk : k < run.length)
    (h : ∀ v, ServerCertified run k v) (v : NodeId C) :
    let p := (run.state k).servers v
    p.commitIndex ≤ ((run.state (k + 1)).servers v).log.length ∧
    PrefixCertificate run (k + 1) ((run.state (k + 1)).servers v).currentTerm
      (((run.state (k + 1)).servers v).log.take p.commitIndex) := by
  dsimp
  have old := h v
  have hp := old.2.retained (by omega : k ≤ k + 1) (by omega) (List.take_prefix _ _)
  have len : (((run.state k).servers v).log.take
      ((run.state k).servers v).commitIndex).length = ((run.state k).servers v).commitIndex :=
    List.length_take_of_le old.1
  have eqtake := take_of_prefix_length hp len
  refine ⟨by have := hp.length_le; omega, ?_⟩
  rw [eqtake]
  exact old.2.mono (by omega) (term_step_monotone (run.transition k hk) v)

theorem servers_certified_step (run : Execution C) (k : ℕ) (hk : k < run.length)
    (h : ∀ v, ServerCertified run k v) (net : NetworkCertified run k) :
    ∀ v, ServerCertified run (k + 1) v := by
  intro v
  have retained := certified_retained run k hk h v
  have st := run.transition k hk
  generalize he : run.state (k + 1) = next at st retained ⊢
  unfold ServerCertified
  rw [he]
  cases st with
  | @commit n i hn hi ht hq =>
    by_cases hv : v = n
    · subst v
      have hc : CommitEvent run k n i := ⟨hk, hn, hi, ht, hq, he⟩
      simp only [commitLeader, setServer, Function.update_self] at retained ⊢
      by_cases hm : i ≤ ((run.state k).servers n).commitIndex
      · simpa only [Nat.max_eq_left hm] using retained
      · rw [Nat.max_eq_right (by omega)]
        exact ⟨hi, Or.inr ⟨k, n, i, by omega, hc, le_rfl, List.prefix_refl _⟩⟩
    · simpa only [commitLeader, setServer, Function.update_of_ne hv] using retained
  | @appendEntries dst leader t prev pt lc entries before after hnet ht hp =>
    by_cases hv : v = dst
    · subst v
      have packet : (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈
          (run.state k).network := by rw [hnet]; simp
      obtain ⟨j, count, hj, _hr, hterm, hprev, hpt, hent, hlc, cert⟩ := net _ packet
      have matching := snapshot_matching run k j (by omega) (by omega) dst leader
      let c := min lc (prev + entries.length)
      let p := ((run.state j).servers leader).log.take c
      have pc : p.IsPrefix (((run.state j).servers leader).log.take lc) :=
        List.take_prefix_take_left (Nat.min_le_left _ _)
      have plen : p.length = c := List.length_take_of_le (by dsimp [c]; omega)
      have installed : p.IsPrefix
          (appendEntriesLog ((run.state k).servers dst).log prev entries) := by
        rw [hent]
        apply covered_prefix_installed (List.take_prefix _ _) matching prev count hprev
        · simpa only [← hpt] using hp
        · dsimp [p, c]
          rw [hent]
          simp only [List.length_take, List.length_drop]
          omega
      have pnew : (appendEntriesLog ((run.state k).servers dst).log prev entries).take c = p :=
        take_of_prefix_length installed plen
      simp only [handleAppend, setServer, Function.update_self] at retained ⊢
      by_cases hm : c ≤ ((run.state k).servers dst).commitIndex
      · have hm' : min lc (prev + entries.length) ≤ ((run.state k).servers dst).commitIndex := hm
        rw [Nat.max_eq_left hm']
        exact retained
      · rw [Nat.max_eq_right (by dsimp [c] at hm ⊢; omega)]
        change c ≤ (appendEntriesLog ((run.state k).servers dst).log prev entries).length ∧
          PrefixCertificate run (k + 1) _
            ((appendEntriesLog ((run.state k).servers dst).log prev entries).take c)
        refine ⟨by have := installed.length_le; omega, ?_⟩
        rw [pnew]
        exact (cert.prefix pc).mono (by omega) (by omega)
    · simpa only [handleAppend, setServer, Function.update_of_ne hv] using retained
  | _ =>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, receiveAppendReply, denyAppend, consume, setServer,
      Function.update_apply] at retained ⊢
    (try split_ifs at retained ⊢) <;> simp_all

theorem network_certified_step (run : Execution C) (k : ℕ)
    (h : NetworkCertified run k)
    (servers : ∀ v, ServerCertified run k v)
    (serversNext : ∀ v, ServerCertified run (k + 1) v)
    (st : Step (run.state k) (run.state (k + 1))) : NetworkCertified run (k + 1) := by
  have old : ∀ m ∈ (run.state k).network, CommitPacket run (k + 1) m :=
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
      trivial
  | @append leader cmd hn =>
    simp only [leaderAppend, List.mem_append] at hm
    rcases hm with hm | hm
    · exact old m hm
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
      refine ⟨k + 1, 1, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      · have hh := (serversNext leader).1
        rw [he] at hh ⊢
        simpa only [leaderAppend, setServer, Function.update_self] using hh
      · have hh := (serversNext leader).2
        rw [he] at hh ⊢
        simpa only [leaderAppend, setServer, Function.update_self] using hh
  | @replicate leader v prev count hn hne hp =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact old m hm
    · exact ⟨k, count, by omega, hn, rfl, hp, rfl, rfl, (servers leader).1,
        (servers leader).2.mono (by omega) le_rfl⟩
  | vote hnet ht hv =>
    simp only [grantVote, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · trivial
  | voteReply hnet ht hv => exact old m (packet_remainder hnet hm)
  | appendEntries hnet ht hp =>
    simp only [handleAppend, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | rfl
    · apply old m; rw [hnet]; exact List.mem_append_left _ hm
    · apply old m; rw [hnet]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · trivial
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

/-- Induction simultaneously certifies operational servers and queued RPCs.
Neither certification predicate appears among operational transition guards. -/
theorem execution_certified (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    (∀ v, ServerCertified run k v) ∧ NetworkCertified run k := by
  induction k with
  | zero =>
    constructor
    · intro v
      simp only [ServerCertified, run.initial, initState]
      exact ⟨by simp, Or.inl rfl⟩
    · intro m hm
      rw [run.initial] at hm
      simp [initState] at hm
  | succ k ih =>
    have previous := ih (by omega)
    have sn := servers_certified_step run k (by omega) previous.1 previous.2
    exact ⟨sn, network_certified_step run k previous.2 previous.1 sn
      (run.transition k (by omega))⟩

theorem execution_commitIndex_bound (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (v : NodeId C) : ((run.state k).servers v).commitIndex ≤ ((run.state k).servers v).log.length :=
  ((execution_certified run k hk).1 v).1

/-- Every operational commit prefix remains a prefix at every later state. -/
theorem execution_commit_prefix_stable (run : Execution C) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ run.length) (v : NodeId C) :
    (((run.state a).servers v).log.take ((run.state a).servers v).commitIndex).IsPrefix
      ((run.state b).servers v).log :=
  ((execution_certified run a (by omega)).1 v).2.retained hab hb (List.take_prefix _ _)

/-- A positive operational commit index is justified by one earlier CommitEvent
in this same execution. In particular its entire local prefix is certified. -/
theorem execution_commit_provenance (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (v : NodeId C) (hc : 0 < ((run.state k).servers v).commitIndex) :
    ∃ a leader index, a < k ∧ CommitEvent run a leader index ∧
      (((run.state k).servers v).log.take ((run.state k).servers v).commitIndex).IsPrefix
        (((run.state a).servers leader).log.take index) := by
  have cert := (execution_certified run k hk).1 v
  have bounded := cert.1
  rcases cert.2 with hn | ⟨a, l, i, ha, event, _ht, hp⟩
  · have := congrArg List.length hn
    simp only [List.length_take, List.length_nil] at this
    omega
  · exact ⟨a, l, i, ha, event, hp⟩

theorem execution_commitIndex_monotone (run : Execution C) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ run.length) (v : NodeId C) :
    ((run.state a).servers v).commitIndex ≤ ((run.state b).servers v).commitIndex := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    by_cases he : a = b + 1
    · subst a; exact le_rfl
    · exact (ih (by omega) (by omega)).trans
        (commitIndex_step_monotone (run.transition b (by omega)) v)

/-- A concrete entry below commitIndex has a real, strictly earlier commitment
witness, including earlier-term entries covered by the current-term commit. -/
theorem execution_committed_entry (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (v : NodeId C) (i : ℕ) (hi : i < ((run.state k).servers v).commitIndex)
    (e : LogEntry) (he : ((run.state k).servers v).log[i]? = some e) :
    ∃ a leader index, a < k ∧ CommitEvent run a leader index ∧
      e ∈ (((run.state a).servers leader).log.take index) := by
  obtain ⟨a, leader, index, ha, hc, hp⟩ :=
    execution_commit_provenance run k hk v (by omega)
  refine ⟨a, leader, index, ha, hc, hp.sublist.subset ?_⟩
  apply List.mem_of_getElem? (i := i)
  rw [List.getElem?_take_of_lt hi]
  exact he

end DistributedRaftCommitIndexInvariant
