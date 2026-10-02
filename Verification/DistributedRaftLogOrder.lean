/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftNetworkInduction

/-!
# Ordered logs in the operational Raft machine

Entry terms are bounded by each server's current term; candidates have strictly
older entries. These facts and positive active terms are derived simultaneously
with packet bounds from the original small-step semantics. A strengthened ghost
archive then proves positive, nondecreasing log terms. Together with the existing
record-origin indexing theorem, this establishes the abstract `WellFormed`
contract for every reachable server log. No transition guard is strengthened.
-/

namespace DistributedRaftLogOrder

open DistributedRaftLeaderCompleteness
  (Cluster NodeId Role LogEntry WellFormed lastEntry lastIndex lastTerm)
open DistributedRaftStateMachine
open DistributedRaftNetworkInduction

variable {C : Cluster}

structure ServerBounds (p : ServerState C) : Prop where
  bound : ∀ e ∈ p.log, e.term ≤ p.currentTerm
  candidate : p.role = .candidate → ∀ e ∈ p.log, e.term < p.currentTerm
  active : p.role ≠ .follower → 0 < p.currentTerm

def PacketBounds (m : Envelope C) : Prop :=
  match m.body with
  | .appendEntries t _ _ _ entries _ => ∀ e ∈ entries, e.term ≤ t
  | _ => True

structure Bounds (s : GlobalState C) : Prop where
  servers : ∀ n, ServerBounds (s.servers n)
  network : ∀ m ∈ s.network, PacketBounds m

theorem mergeSuffix_mem {old incoming : List LogEntry} {e : LogEntry}
    (he : e ∈ mergeSuffix old incoming) : e ∈ old ∨ e ∈ incoming := by
  induction old generalizing incoming with
  | nil =>
    cases incoming with
    | nil => simp at he
    | cons b incoming => exact Or.inr he
  | cons a old ih =>
    cases incoming with
    | nil => simp_all
    | cons b incoming =>
      simp only [mergeSuffix] at he
      split_ifs at he with hab
      · rcases List.mem_cons.mp he with rfl | he
        · simp
        · rcases ih he with ho | hi
          · exact Or.inl (List.mem_cons_of_mem a ho)
          · exact Or.inr (List.mem_cons_of_mem b hi)
      · exact Or.inr he

theorem appendEntriesLog_mem {old incoming : List LogEntry} {prev : ℕ} {e : LogEntry}
    (he : e ∈ appendEntriesLog old prev incoming) : e ∈ old ∨ e ∈ incoming := by
  rcases List.mem_append.mp he with he | he
  · exact Or.inl (List.mem_of_mem_take he)
  · rcases mergeSuffix_mem he with he | he
    · exact Or.inl (List.mem_of_mem_drop he)
    · exact Or.inr he

theorem ServerBounds.observe {p : ServerState C} (h : ServerBounds p) {t : ℕ}
    (ht : p.currentTerm ≤ t) :
    ServerBounds { p with currentTerm := t, votedFor := none, role := .follower } := by
  constructor
  · intro e he; exact (h.bound e he).trans ht
  · simp
  · simp

theorem ServerBounds.timeout {p : ServerState C} (h : ServerBounds p) (n : NodeId C) :
    ServerBounds { p with
      currentTerm := p.currentTerm + 1
      votedFor := some n
      role := .candidate } := by
  constructor
  · intro e he; exact (h.bound e he).trans (Nat.le_succ _)
  · intro _ e he; exact Nat.lt_succ_of_le (h.bound e he)
  · simp

theorem ServerBounds.elect {p : ServerState C} (h : ServerBounds p)
    (hc : p.role = .candidate) :
    ServerBounds { p with role := .leader, matchIndex := fun _ => 0 } := by
  constructor
  · exact h.bound
  · simp
  · intro _; exact h.active (by simp [hc])

theorem ServerBounds.append {p : ServerState C} (h : ServerBounds p)
    (hl : p.role = .leader) (cmd : ℕ) :
    ServerBounds { p with log := p.log ++ [⟨p.log.length + 1, p.currentTerm, cmd⟩] } := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he | he
    · exact h.bound e he
    · simp only [List.mem_singleton] at he
      subst e; exact le_rfl
  · simp [hl]
  · exact h.active

theorem ServerBounds.handle {p : ServerState C} (h : ServerBounds p)
    (prev lc : ℕ) (entries : List LogEntry)
    (hb : ∀ e ∈ entries, e.term ≤ p.currentTerm) :
    ServerBounds { p with
      role := .follower
      log := appendEntriesLog p.log prev entries
      commitIndex := max p.commitIndex (min lc (prev + entries.length)) } := by
  constructor
  · intro e he
    rcases appendEntriesLog_mem he with he | he
    · exact h.bound e he
    · exact hb e he
  · simp
  · simp

theorem ServerBounds.same {p q : ServerState C} (h : ServerBounds p)
    (ht : q.currentTerm = p.currentTerm) (hl : q.log = p.log) (hr : q.role = p.role) :
    ServerBounds q := by
  constructor
  · simpa [ht, hl] using h.bound
  · simpa [ht, hl, hr] using h.candidate
  · simpa [ht, hr] using h.active

theorem servers_set {s : GlobalState C} (h : ∀ n, ServerBounds (s.servers n))
    (n : NodeId C) (p : ServerState C) (hp : ServerBounds p) :
    ∀ v, ServerBounds ((setServer s n p).servers v) := by
  intro v
  by_cases hv : v = n
  · subst v; simpa [setServer] using hp
  · simpa [setServer, Function.update_of_ne hv] using h v

theorem bounds_step {s s' : GlobalState C} (h : Bounds s) (st : Step s s') : Bounds s' := by
  constructor
  · cases st with
    | observe _ ht => exact servers_set h.servers _ _ ((h.servers _).observe ht.le)
    | timeout n _ => exact servers_set h.servers _ _ ((h.servers n).timeout n)
    | elect hc _ => exact servers_set h.servers _ _ ((h.servers _).elect hc)
    | append cmd hl => exact servers_set h.servers _ _ ((h.servers _).append hl cmd)
    | @appendEntries v leader t prev pt lc entries before after he ht _ =>
      apply servers_set h.servers v _ ((h.servers v).handle prev lc entries ?_)
      have hm : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network := by
        rw [he]; simp
      simpa [PacketBounds, ht] using h.network _ hm
    | @rejectAppend v leader t prev pt lc entries before after _ _ _ =>
      apply servers_set h.servers v
      constructor
      · exact (h.servers v).bound
      · dsimp; split_ifs <;> simp_all [ServerBounds.candidate (h.servers v)]
      · dsimp; split_ifs <;> simp_all [ServerBounds.active (h.servers v)]
    | _ =>
      intro n
      apply (h.servers n).same
      all_goals
        simp only [grantVote, receiveVote, receiveAppendReply, commitLeader, consume,
          setServer, Function.update_apply] <;>
          (try split_ifs) <;> simp_all
  · intro m hm
    cases st with
    | observe => exact h.network m hm
    | elect => exact h.network m hm
    | commit => exact h.network m hm
    | timeout =>
      simp only [startElection, List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.network m hm
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
        trivial
    | @append n cmd hl =>
      simp only [leaderAppend, List.mem_append] at hm
      rcases hm with hm | hm
      · exact h.network m hm
      · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hm
        simp [PacketBounds]
    | @replicate n v prev count hl hn hp =>
      simp only [List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | rfl
      · exact h.network m hm
      · intro e he
        exact (h.servers n).bound e (List.mem_of_mem_drop (List.mem_of_mem_take he))
    | vote he | appendEntries he | rejectVote he | rejectAppend he =>
      simp only [grantVote, handleAppend, denyAppend, List.mem_append, List.mem_singleton] at hm
      rcases hm with (hm | hm) | rfl
      · exact h.network m (packet_remainder he (List.mem_append_left _ hm))
      · exact h.network m (packet_remainder he (List.mem_append_right _ hm))
      · trivial
    | voteReply he | appendReply he | drop he =>
      exact h.network m (packet_remainder he hm)
    | duplicate hm' =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact h.network _ hm'
      · exact h.network m hm

theorem reachable_bounds {s : GlobalState C} (hr : Reachable s) : Bounds s := by
  induction hr with
  | init =>
    constructor
    · intro n; constructor <;> simp [initState]
    · simp [initState]
  | step _ st ih => exact bounds_step ih st

theorem reachable_log_bound {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (e : LogEntry) (he : e ∈ (s.servers n).log) :
    e.term ≤ (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.bound e he

theorem reachable_candidate_strict {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (hc : (s.servers n).role = .candidate)
    (e : LogEntry) (he : e ∈ (s.servers n).log) :
    e.term < (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.candidate hc e he

theorem reachable_active_positive {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (hc : (s.servers n).role ≠ .follower) :
    0 < (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.active hc

/-- Terms in a leader snapshot are positive and nondecreasing. -/
structure OrderedPositive (log : List LogEntry) : Prop where
  ordered : log.Pairwise (fun a b => a.term ≤ b.term)
  positive : ∀ e ∈ log, 0 < e.term

theorem OrderedPositive.prefix {a b : List LogEntry} (h : OrderedPositive b)
    (hp : a.IsPrefix b) : OrderedPositive a :=
  ⟨h.ordered.sublist hp.sublist, fun e he => h.positive e (hp.mem he)⟩

theorem OrderedPositive.append {log : List LogEntry} (h : OrderedPositive log)
    (e : LogEntry) (hb : ∀ a ∈ log, a.term ≤ e.term) (he : 0 < e.term) :
    OrderedPositive (log ++ [e]) := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨h.ordered, by simp, ?_⟩
    intro a ha b hb'
    simp only [List.mem_singleton] at hb'
    subst b
    exact hb a ha
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact h.positive a ha
    · simpa using (List.mem_singleton.mp ha) ▸ he

theorem ordered_archive_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A)
    (ho : ∀ l, A l → OrderedPositive l) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B ∧ ∀ l, B l → OrderedPositive l := by
  cases st with
  | @append n cmd leader =>
    refine ⟨_, archive_step_append hr h n cmd leader, ?_⟩
    intro l hl
    rcases hl with hl | hl
    · exact ho l hl
    · apply OrderedPositive.prefix _ hl
      apply (ho _ (h.servers n)).append
      · exact reachable_log_bound hr n
      · exact reachable_active_positive hr n (by simp [leader])
  | appendEntries he ht hp =>
    exact ⟨A, archive_step_handle_append hr h he ht hp, ho⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr h (.observe hm ht) ?_, ho⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn =>
    refine ⟨A, archive_frame hr h (.timeout _ n hn) ?_, ho⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr h (.vote he ht hv) ?_, ho⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc => exact ⟨A, archive_frame hr h (.voteReply he ht hc) (by intros; rfl), ho⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr h (.elect hc hq) ?_, ho⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr h (.commit i hl hi ht hq) ?_, ho⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr h (.replicate prev count hl hn hp) (by intros; rfl), ho⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr h (.appendReply he ht hl) ?_, ho⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv => exact ⟨A, archive_frame hr h (.rejectVote he ht hv) (by intros; rfl), ho⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr h (.rejectAppend he ht hp) ?_, ho⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr h (.drop he) (by intros; rfl), ho⟩
  | duplicate hm => exact ⟨A, archive_frame hr h (.duplicate hm) (by intros; rfl), ho⟩

theorem reachable_ordered_archive {s : GlobalState C} (hr : Reachable s) :
    ∃ A, ArchiveInvariant s A ∧ ∀ l, A l → OrderedPositive l := by
  induction hr with
  | init =>
    refine ⟨_, archive_init, ?_⟩
    intro l hl
    subst l
    constructor <;> simp
  | step hr st ih =>
    obtain ⟨A, hA, hO⟩ := ih
    exact ordered_archive_step hr hA hO st

theorem reachable_ordered_positive {s : GlobalState C} (hr : Reachable s) (n : NodeId C) :
    OrderedPositive (s.servers n).log := by
  obtain ⟨A, hA, hO⟩ := reachable_ordered_archive hr
  exact hO _ (hA.servers n)

/-- Consecutive indexing and monotone positive terms imply the abstract log contract. -/
theorem wellFormed_of_ordered_indexed {log : List LogEntry}
    (ho : OrderedPositive log)
    (hi : ∀ (i : ℕ) (h : i < log.length), log[i].index = i + 1) :
    WellFormed log := by
  constructor
  · exact hi
  · exact ho.positive
  · intro a ha b hb hab
    obtain ⟨i, hilen, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hjlen, rfl⟩ := List.mem_iff_getElem.mp hb
    have hii := hi i hilen
    have hjj := hi j hjlen
    have ij : i = j := by omega
    subst j
    rfl
  · intro e he
    obtain ⟨i, hilen, rfl⟩ := List.mem_iff_getElem.mp he
    have hlen : 0 < log.length := by omega
    have hlast : log.length - 1 < log.length := by omega
    have hlastEq : lastEntry log = log[log.length - 1] := by
      simp [lastEntry, List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlast]
    constructor
    · dsimp [lastIndex]
      rw [hlastEq, hi i hilen, hi (log.length - 1) hlast]
      omega
    · dsimp [lastTerm]
      rw [hlastEq]
      by_cases hij : i = log.length - 1
      · subst i; exact le_rfl
      · exact List.pairwise_iff_getElem.mp ho.ordered i (log.length - 1)
          hilen hlast (by omega)
  · intro a ha b hb ht
    obtain ⟨i, hilen, rfl⟩ := List.mem_iff_getElem.mp ha
    obtain ⟨j, hjlen, rfl⟩ := List.mem_iff_getElem.mp hb
    rw [hi i hilen, hi j hjlen]
    by_contra hnot
    have hji : j ≤ i := by omega
    rcases hji.eq_or_lt with hji | hji
    · subst j; omega
    · have := List.pairwise_iff_getElem.mp ho.ordered j i hjlen hilen hji
      omega

/-- Well-formed logs follow from execution, rather than being transition guards. -/
theorem reachable_wellFormed {s : GlobalState C} (hr : Reachable s) (n : NodeId C) :
    WellFormed (s.servers n).log := by
  apply wellFormed_of_ordered_indexed (reachable_ordered_positive hr n)
  intro i hi
  exact reachable_entry_index hr n i _ (List.getElem?_eq_getElem hi)

/-- One-based consecutive indices identify the last index with the list length. -/
theorem wellFormed_lastIndex_eq_length {log : List LogEntry} (hw : WellFormed log) :
    lastIndex log = log.length := by
  by_cases hn : log = []
  · subst log; rfl
  · have hp := List.length_pos_iff.mpr hn
    have hl : log.length - 1 < log.length := by omega
    change (lastEntry log).index = log.length
    simp only [lastEntry, List.getLast?_eq_getElem?, List.getElem?_eq_getElem hl,
      Option.getD_some, hw.indexed (log.length - 1) hl]
    omega

/-- A matching entry carries every shorter source prefix to the other log. -/
theorem matching_transfers_prefix {source candidate p : List LogEntry}
    (hs : WellFormed source) (hc : WellFormed candidate)
    (hm : LogMatching source candidate) (hp : p.IsPrefix source)
    (x y : LogEntry) (hx : x ∈ source) (hy : y ∈ candidate)
    (hi : x.index = y.index) (ht : x.term = y.term) (hlen : p.length ≤ x.index) :
    p.IsPrefix candidate := by
  obtain ⟨i, hil, hix⟩ := List.mem_iff_getElem.mp hx
  obtain ⟨j, hjl, hjy⟩ := List.mem_iff_getElem.mp hy
  have hxi : x.index = i + 1 := by rw [← hix]; exact hs.indexed i hil
  have hyj : y.index = j + 1 := by rw [← hjy]; exact hc.indexed j hjl
  have hij : i = j := by omega
  subst j
  have hsx : source[i]? = some x := List.getElem?_eq_some_iff.mpr ⟨hil, hix⟩
  have hcy : candidate[i]? = some y := List.getElem?_eq_some_iff.mpr ⟨hjl, hjy⟩
  have heq := hm i x y hsx hcy ht
  have hp' : p.IsPrefix (source.take (i+1)) := by
    have htake := hp.take (i+1)
    rw [(List.take_eq_self_iff p).mpr (by omega)] at htake
    exact htake
  rw [heq] at hp'
  exact hp'.trans (List.take_prefix _ _)

end DistributedRaftLogOrder
