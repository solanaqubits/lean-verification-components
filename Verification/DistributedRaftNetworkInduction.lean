/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftNetworkHistory
import Verification.DistributedRaftNetworkLogLemmas

/-!
# Global Log Matching for the asynchronous Raft machine

The proof carries a ghost archive of prefixes of logs actually produced by leader
append events. Network packets have historical sources: a delayed packet need not
agree with its sender's current log after that sender changes term.
The operational `Step` relation is unchanged.
-/
namespace DistributedRaftNetworkInduction

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry)
open DistributedRaftStateMachine
open DistributedRaftNetworkHistory
open DistributedRaftNetworkLogLemmas

variable {C : Cluster}

/-- The standard positional Log Matching condition, for every pair of servers. -/
def GlobalLogMatching (s : GlobalState C) : Prop :=
  ∀ i j, LogMatching (s.servers i).log (s.servers j).log

/-- An RPC's predecessor and contiguous batch come from one archived source log. -/
def Backed (s : GlobalState C) (A : List LogEntry → Prop)
    (t : ℕ) (leader : NodeId C) (prev pt : ℕ) (entries : List LogEntry) : Prop :=
  ∃ source count, A source ∧ prev ≤ source.length ∧ pt = termAt source prev ∧
    entries = (source.drop prev).take count ∧
    ∃ generated : GlobalState C, Reachable generated ∧
      Relation.ReflTransGen Step generated s ∧
      (generated.servers leader).role = .leader ∧
      (generated.servers leader).currentTerm = t ∧
      (generated.servers leader).log = source

/-- Every in-flight AppendEntries packet has a historical source snapshot. -/
def NetworkBacked (s : GlobalState C) (A : List LogEntry → Prop) : Prop :=
  ∀ dst t leader prev pt entries lc,
    (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network →
    Backed s A t leader prev pt entries

/-- A concrete entry was generated at this position by an actual leader append,
and that generated state precedes the state being certified. -/
def Generated (s : GlobalState C) (i : ℕ) (e : LogEntry) : Prop :=
  ∃ before : GlobalState C, ∃ n cmd, Reachable before ∧
    (before.servers n).role = .leader ∧ i = (before.servers n).log.length ∧
    e = ⟨(before.servers n).log.length + 1, (before.servers n).currentTerm, cmd⟩ ∧
    Relation.ReflTransGen Step (leaderAppend before n cmd) s

theorem Generated.advance {s s' : GlobalState C} {i : ℕ} {e : LogEntry}
    (h : Generated s i e) (st : Step s s') : Generated s' i e := by
  obtain ⟨before, n, cmd, hr, hl, hi, he, path⟩ := h
  exact ⟨before, n, cmd, hr, hl, hi, he, path.tail st⟩

/-- Entries originated at an elected leader, and a same-term originating leader
has already advanced strictly past every index it generated. -/
def Origin (s : GlobalState C) (A : List LogEntry → Prop) : Prop :=
  ∀ l, A l → ∀ i e, l[i]? = some e →
    ∃ n, (e.term, n) ∈ s.elected ∧
      (e.term = (s.servers n).currentTerm → i < (s.servers n).log.length) ∧ Generated s i e

/-- Strengthened induction invariant. The archive is proof-only state. -/
structure ArchiveInvariant (s : GlobalState C) (A : List LogEntry → Prop) : Prop where
  closed : ∀ a b, A b → a.IsPrefix b → A a
  matching : ∀ a b, A a → A b → LogMatching a b
  origin : Origin s A
  servers : ∀ n, A (s.servers n).log
  network : NetworkBacked s A

/-- There is no archive at initialization except the empty history. -/
theorem archive_init : ArchiveInvariant (initState C) (fun l => l = []) := by
  constructor
  · intro a b hb hp
    subst b
    simpa using hp
  · intro a b ha hb
    subst a; subst b
    intro i x y hx
    simp at hx
  · intro l hl i e he
    subst l
    simp at he
  · intro n; rfl
  · intro dst t leader prev pt entries lc hm
    simp [initState] at hm

theorem Backed.mono {s : GlobalState C} {A B : List LogEntry → Prop}
    (hab : ∀ l, A l → B l) {t prev pt : ℕ} {leader : NodeId C}
    {entries : List LogEntry} (h : Backed s A t leader prev pt entries) :
    Backed s B t leader prev pt entries := by
  obtain ⟨source, count, hs, hp, ht, he, history⟩ := h
  exact ⟨source, count, hab source hs, hp, ht, he, history⟩

theorem Backed.advance {s s' : GlobalState C} {A : List LogEntry → Prop}
    {t prev pt : ℕ} {leader : NodeId C} {entries : List LogEntry}
    (h : Backed s A t leader prev pt entries) (st : Step s s') :
    Backed s' A t leader prev pt entries := by
  obtain ⟨source, count, hs, hp, ht, he, generated, hr, path, role, term, log⟩ := h
  exact ⟨source, count, hs, hp, ht, he, generated, hr, path.tail st, role, term, log⟩

theorem NetworkBacked.mono {s : GlobalState C} {A B : List LogEntry → Prop}
    (h : NetworkBacked s A) (hab : ∀ l, A l → B l) : NetworkBacked s B := by
  intro dst t leader prev pt entries lc hm
  exact (h dst t leader prev pt entries lc hm).mono hab

/-- Queue consumption retains only packets already present. -/
theorem packet_remainder {s : GlobalState C} {before after : List (Envelope C)}
    {m x : Envelope C} (he : s.network = before ++ m :: after)
    (hx : x ∈ before ++ after) : x ∈ s.network := by
  rw [he]
  rcases List.mem_append.mp hx with hx | hx
  · exact List.mem_append_left _ hx
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ hx)

/-- An existing archived entry retains its origin after any operational step. -/
theorem origin_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (st : Step s s') (h : Origin s A) : Origin s' A := by
  intro l hl i e he
  obtain ⟨n, hn, hb, hg⟩ := h l hl i e he
  refine ⟨n, elected_step_monotone st hn, ?_, hg.advance st⟩
  intro ht
  have bound := (reachable_history hr).electedBound e.term n hn
  have mono := term_step_monotone st n
  have oldTerm : e.term = (s.servers n).currentTerm := by omega
  exact (hb oldTerm).trans_le (active_elected_log_length_step hr st e.term n hn ht)

/-- A same-term entry cannot occur at the fresh append index anywhere in the archive. -/
theorem archive_fresh {s : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A) {n : NodeId C}
    (leader : (s.servers n).role = .leader) {l : List LogEntry} (hl : A l)
    (e : LogEntry) (he : l[(s.servers n).log.length]? = some e) :
    (s.servers n).currentTerm ≠ e.term := by
  intro ht
  obtain ⟨owner, elected, bound, _generated⟩ := h.origin l hl _ e he
  have ours := (elections_reachable hr).2 n leader
  have same : owner = n := election_history_safety hr e.term owner n elected (ht ▸ ours)
  subst owner
  have := bound ht.symm
  omega

/-- Archive expansion on a genuine client append. -/
def extendArchive (A : List LogEntry → Prop) (fresh : List LogEntry) : List LogEntry → Prop :=
  fun l => A l ∨ l.IsPrefix fresh

/-- Transport preservation uses only genuine RPC construction and queue operations. -/
theorem network_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : NetworkBacked s A) (st : Step s s')
    (oldLogs : ∀ n, A (s.servers n).log) (newLogs : ∀ n, A (s'.servers n).log) :
    NetworkBacked s' A := by
  have oldPacket : ∀ dst t leader prev pt entries lc,
      (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network →
      Backed s' A t leader prev pt entries := by
    intro dst t leader prev pt entries lc hm
    exact (h dst t leader prev pt entries lc hm).advance st
  intro dst t leader prev pt entries lc hm
  cases st with
  | observe => exact oldPacket dst t leader prev pt entries lc hm
  | elect => exact oldPacket dst t leader prev pt entries lc hm
  | commit => exact oldPacket dst t leader prev pt entries lc hm
  | @timeout n _ =>
    simp only [startElection, List.mem_append] at hm
    rcases hm with hm | hm
    · exact oldPacket dst t leader prev pt entries lc hm
    · simp [broadcast] at hm
  | @append n cmd hn =>
    simp only [leaderAppend, List.mem_append] at hm
    rcases hm with hm | hm
    · exact oldPacket dst t leader prev pt entries lc hm
    · simp only [broadcast, List.mem_map] at hm
      obtain ⟨v, _, hv⟩ := hm
      cases hv
      refine ⟨(s.servers leader).log ++ [⟨(s.servers leader).log.length + 1,
        (s.servers leader).currentTerm, cmd⟩], 1, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [leaderAppend, setServer] using newLogs leader
      · simp
      · exact termAt_prefix (List.prefix_append _ _) _ (Nat.le_refl _)
      · simp
      · refine ⟨leaderAppend s leader cmd, hr.step (.append cmd hn), .refl, ?_, ?_, ?_⟩
        all_goals simp [leaderAppend, setServer, hn]
  | @replicate n v prev' count hn hne hprev =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | hm
    · exact oldPacket dst t leader prev pt entries lc hm
    · cases hm
      refine ⟨(s.servers leader).log, count, oldLogs leader, hprev, rfl, rfl, s, hr,
        Relation.ReflTransGen.single (.replicate prev count hn hne hprev), hn, rfl, rfl⟩
  | @duplicate m hm' =>
    rcases List.mem_cons.mp hm with he | hm
    · exact oldPacket dst t leader prev pt entries lc (he ▸ hm')
    · exact oldPacket dst t leader prev pt entries lc hm
  | vote he _ _ =>
    simp only [grantVote, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_left _ hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · cases hm
  | voteReply he _ _ =>
    exact oldPacket dst t leader prev pt entries lc (packet_remainder he hm)
  | appendEntries he _ _ =>
    simp only [handleAppend, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_left _ hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · cases hm
  | appendReply he _ _ =>
    exact oldPacket dst t leader prev pt entries lc (packet_remainder he hm)
  | rejectVote he _ _ =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_left _ hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · cases hm
  | rejectAppend he _ _ =>
    simp only [denyAppend, List.mem_append, List.mem_singleton] at hm
    rcases hm with (hm | hm) | hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_left _ hm
    · apply oldPacket dst t leader prev pt entries lc
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hm)
    · cases hm
  | drop he => exact oldPacket dst t leader prev pt entries lc (packet_remainder he hm)

/-- Changes to roles, votes, terms and commit metadata preserve archived server logs. -/
theorem archive_frame {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A) (st : Step s s')
    (logs : ∀ n, (s'.servers n).log = (s.servers n).log) : ArchiveInvariant s' A := by
  have hs : ∀ n, A (s'.servers n).log := by intro n; rw [logs]; exact h.servers n
  exact ⟨h.closed, h.matching, origin_step hr st h.origin, hs,
    network_step hr h.network st h.servers hs⟩

/-- A position in a prefix is the same position in its containing snapshot. -/
theorem prefix_get {a b : List LogEntry} (hp : a.IsPrefix b)
    {i : ℕ} {e : LogEntry} (he : a[i]? = some e) : b[i]? = some e := by
  obtain ⟨tail, rfl⟩ := hp
  have hi : i < a.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at he
    contradiction
  rw [List.getElem?_append_left hi]
  exact he

theorem archive_step_append {s : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A) (n : NodeId C) (cmd : ℕ)
    (leader : (s.servers n).role = .leader) :
    ArchiveInvariant (leaderAppend s n cmd)
      (extendArchive A ((s.servers n).log ++
        [⟨(s.servers n).log.length + 1, (s.servers n).currentTerm, cmd⟩])) := by
  let e : LogEntry := ⟨(s.servers n).log.length + 1, (s.servers n).currentTerm, cmd⟩
  let fresh := (s.servers n).log ++ [e]
  let B := extendArchive A fresh
  have st : Step s (leaderAppend s n cmd) := .append cmd leader
  have inclusion : ∀ l, A l → B l := fun _ hl => Or.inl hl
  have matchFresh : ∀ l, A l → LogMatching fresh l := by
    intro l hl
    apply log_matching_append (h.matching _ _ (h.servers n) hl) e
    intro y hy
    exact archive_fresh hr h leader hl y hy
  have origOld := origin_step hr st h.origin
  have origFresh : ∀ i x, fresh[i]? = some x →
      ∃ owner, (x.term, owner) ∈ (leaderAppend s n cmd).elected ∧
        (x.term = ((leaderAppend s n cmd).servers owner).currentTerm →
          i < ((leaderAppend s n cmd).servers owner).log.length) ∧
        Generated (leaderAppend s n cmd) i x := by
    intro i x hx
    by_cases hi : i < (s.servers n).log.length
    · rw [List.getElem?_append_left hi] at hx
      exact origOld _ (h.servers n) i x hx
    · have bound : i < fresh.length := by
        by_contra hn
        rw [List.getElem?_eq_none (by omega)] at hx
        contradiction
      have index : i = (s.servers n).log.length := by
        simp only [fresh, List.length_append, List.length_singleton] at bound
        omega
      subst i
      have he : e = x := by simpa [fresh] using hx
      subst x
      refine ⟨n, (elections_reachable hr).2 n leader, ?_, ?_⟩
      · intro _
        simp [leaderAppend, setServer]
      · exact ⟨s, n, cmd, hr, leader, rfl, rfl, .refl⟩
  have logs : ∀ node, B ((leaderAppend s n cmd).servers node).log := by
    intro node
    by_cases hn : node = n
    · subst node
      right
      simp [leaderAppend, setServer, fresh, e]
    · left
      simpa [leaderAppend, setServer, Function.update_of_ne hn] using h.servers node
  change ArchiveInvariant (leaderAppend s n cmd) B
  constructor
  · intro a b hb hp
    rcases hb with hb | hb
    · exact Or.inl (h.closed a b hb hp)
    · exact Or.inr (hp.trans hb)
  · intro a b ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact h.matching a b ha hb
    · exact matching_prefix_right (matching_symm (matchFresh a ha)) hb
    · exact matching_prefix_left (matchFresh b hb) ha
    · exact matching_prefix_both (matching_refl fresh) ha hb
  · intro l hl i x hx
    rcases hl with hl | hl
    · exact origOld l hl i x hx
    · exact origFresh i x (prefix_get hl hx)
  · exact logs
  · exact network_step hr (h.network.mono inclusion) st (fun n => inclusion _ (h.servers n)) logs

/-- A partial received batch produces either the old log or an archived prefix. -/
theorem archive_step_handle_append {s : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A)
    {v leader : NodeId C} {t prev pt lc : ℕ} {entries : List LogEntry}
    {before after : List (Envelope C)}
    (he : s.network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after)
    (ht : t = (s.servers v).currentTerm) (hp : prevMatches (s.servers v).log prev pt) :
    ArchiveInvariant (handleAppend s v leader prev entries lc before after) A := by
  have st : Step s (handleAppend s v leader prev entries lc before after) :=
    .appendEntries he ht hp
  have packet : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network := by
    rw [he]; simp
  obtain ⟨source, count, hs, hprev, hpt, hentries, _history⟩ :=
    h.network v t leader prev pt entries lc packet
  have matching := h.matching _ _ (h.servers v) hs
  have sourcePrev : prevMatches (s.servers v).log prev (termAt source prev) := hpt ▸ hp
  have choice := matching_append_entries_choice matching prev count hprev sourcePrev
  have updated : A (appendEntriesLog (s.servers v).log prev entries) := by
    rw [hentries]
    rcases choice with old | new
    · rw [old]; exact h.servers v
    · rw [new]; exact h.closed _ _ hs (List.take_prefix _ _)
  have logs : ∀ n, A ((handleAppend s v leader prev entries lc before after).servers n).log := by
    intro n
    by_cases hn : n = v
    · subst n; simpa [handleAppend, setServer] using updated
    · simpa [handleAppend, setServer, Function.update_of_ne hn] using h.servers n
  exact ⟨h.closed, h.matching, origin_step hr st h.origin, logs,
    network_step hr h.network st h.servers logs⟩

/-- Every operational step admits a suitable updated ghost archive. -/
theorem archive_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (h : ArchiveInvariant s A) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B := by
  cases st with
  | append cmd leader => exact ⟨_, archive_step_append hr h _ cmd leader⟩
  | appendEntries he ht hp => exact ⟨_, archive_step_handle_append hr h he ht hp⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr h (.observe hm ht) ?_⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn =>
    refine ⟨A, archive_frame hr h (.timeout _ n hn) ?_⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr h (.vote he ht hv) ?_⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc => exact ⟨A, archive_frame hr h (.voteReply he ht hc) (by intros; rfl)⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr h (.elect hc hq) ?_⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr h (.commit i hl hi ht hq) ?_⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr h (.replicate prev count hl hn hp) (by intros; rfl)⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr h (.appendReply he ht hl) ?_⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv => exact ⟨A, archive_frame hr h (.rejectVote he ht hv) (by intros; rfl)⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr h (.rejectAppend he ht hp) ?_⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr h (.drop he) (by intros; rfl)⟩
  | duplicate hm => exact ⟨A, archive_frame hr h (.duplicate hm) (by intros; rfl)⟩

/-- Strengthened induction from empty logs, including authenticated packets in flight. -/
theorem reachable_archive {s : GlobalState C} (hr : Reachable s) :
    ∃ A, ArchiveInvariant s A := by
  induction hr with
  | init => exact ⟨_, archive_init⟩
  | step hr st ih =>
    obtain ⟨A, hA⟩ := ih
    exact archive_step hr hA st

/-- Global Log Matching follows unconditionally for every reachable state. -/
theorem reachable_global_log_matching (s : GlobalState C) (h_reach : Reachable s) :
    GlobalLogMatching s := by
  obtain ⟨A, hA⟩ := reachable_archive h_reach
  exact fun i j => hA.matching _ _ (hA.servers i) (hA.servers j)

/-- Every current log entry has a genuine earlier leader-append event. -/
theorem reachable_record_origin {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (i : ℕ) (e : LogEntry) (he : (s.servers n).log[i]? = some e) :
    Generated s i e := by
  obtain ⟨A, hA⟩ := reachable_archive hr
  obtain ⟨_, _, _, generated⟩ := hA.origin _ (hA.servers n) i e he
  exact generated

/-- Entries inside delayed or duplicated partial packets retain their original
leader-append event at the absolute position `prev + offset`. -/
theorem reachable_network_entry_origin {s : GlobalState C} (hr : Reachable s)
    {dst leader : NodeId C} {t prev pt lc offset : ℕ} {entries : List LogEntry}
    (hm : (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network)
    (e : LogEntry) (he : entries[offset]? = some e) : Generated s (prev + offset) e := by
  obtain ⟨A, hA⟩ := reachable_archive hr
  obtain ⟨source, count, hs, _, _, entriesEq, _⟩ :=
    hA.network dst t leader prev pt entries lc hm
  rw [entriesEq] at he
  have bound : offset < count := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp he
    simp only [List.length_take, List.length_drop] at hi
    omega
  rw [List.getElem?_take_of_lt bound, List.getElem?_drop] at he
  obtain ⟨_, _, _, generated⟩ := hA.origin source hs (prev + offset) e he
  exact generated

/-- The explicit entry index agrees with its one-based list position. -/
theorem reachable_entry_index {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (i : ℕ) (e : LogEntry) (he : (s.servers n).log[i]? = some e) :
    e.index = i + 1 := by
  obtain ⟨before, owner, cmd, _, _, hi, entry, _⟩ := reachable_record_origin hr n i e he
  rw [entry, hi]

/-- A packet is sourced from the authenticated archive, which is internally
prefix-consistent and also consistent with every current server log. -/
def NetworkLogConsistency (s : GlobalState C) : Prop :=
  ∃ A, ArchiveInvariant s A

theorem reachable_network_log_consistency {s : GlobalState C} (hr : Reachable s) :
    NetworkLogConsistency s := reachable_archive hr

theorem log_matching_init : GlobalLogMatching (initState C) :=
  reachable_global_log_matching _ .init

theorem log_matching_step_leader_append {s : GlobalState C} (hr : Reachable s)
    (n : NodeId C) (cmd : ℕ) (hl : (s.servers n).role = .leader) :
    GlobalLogMatching (leaderAppend s n cmd) :=
  reachable_global_log_matching _ (hr.step (.append cmd hl))

theorem log_matching_step_handle_append_entries {s : GlobalState C} (hr : Reachable s)
    {v leader : NodeId C} {t prev pt lc : ℕ} {entries : List LogEntry}
    {before after : List (Envelope C)}
    (he : s.network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after)
    (ht : t = (s.servers v).currentTerm) (hp : prevMatches (s.servers v).log prev pt) :
    GlobalLogMatching (handleAppend s v leader prev entries lc before after) :=
  reachable_global_log_matching _ (hr.step (.appendEntries he ht hp))

theorem log_matching_step_other {s s' : GlobalState C} (h : GlobalLogMatching s)
    (logs : ∀ n, (s'.servers n).log = (s.servers n).log) : GlobalLogMatching s' := by
  intro i j
  rw [logs, logs]
  exact h i j

/-- Main manifest states precisely the reachable-state conclusion. -/
structure RaftNetworkInductionSuite : Prop where
  h_matching : ∀ {C : Cluster} (s : GlobalState C), Reachable s → GlobalLogMatching s
  h_network : ∀ {C : Cluster} {s : GlobalState C}, Reachable s → NetworkLogConsistency s
  h_origin : ∀ {C : Cluster} {s : GlobalState C}, Reachable s →
    ∀ n i e, (s.servers n).log[i]? = some e → Generated s i e
  h_packet_origin : ∀ {C : Cluster} {s : GlobalState C}, Reachable s →
    ∀ dst leader t prev pt lc entries offset e,
      (⟨dst, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network →
      entries[offset]? = some e → Generated s (prev + offset) e
  h_index : ∀ {C : Cluster} {s : GlobalState C}, Reachable s →
    ∀ n i e, (s.servers n).log[i]? = some e → e.index = i + 1
  h_init : ∀ C, GlobalLogMatching (initState C)

theorem raft_network_induction_master_suite : RaftNetworkInductionSuite := {
  h_matching := reachable_global_log_matching
  h_network := reachable_network_log_consistency
  h_origin := reachable_record_origin
  h_packet_origin := fun hr _ _ _ _ _ _ _ _ e hm he =>
    reachable_network_entry_origin hr hm e he
  h_index := reachable_entry_index
  h_init := fun _ => log_matching_init
}

end DistributedRaftNetworkInduction
