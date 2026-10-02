/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftLeaderCompleteness
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FinCases

/-!
# Small-step Raft: elections and log operations

A fixed cluster, addressed asynchronous RPCs, persistent vote evidence, and
conflict-sensitive AppendEntries. Cast-vote and election records are ghost state,
updated by actual events.
The received-vote set is operational state used for majority counting.
Higher-term observation and election promotion are separate small steps.
The connection to `HistoryValid` and `VoterEvolution` is a separate obligation.
-/

namespace DistributedRaftStateMachine

open DistributedRaftLeaderCompleteness (Cluster NodeId Role LogEntry majority
  quorum_intersection lastTerm lastIndex logUpToDate)

variable {C : Cluster}

structure ServerState (C : Cluster) where
  currentTerm : ℕ := 0
  votedFor : Option (NodeId C) := none
  role : Role := .follower
  log : List LogEntry := []
  commitIndex : ℕ := 0
  matchIndex : NodeId C → ℕ := fun _ => 0

inductive NetworkMessage (C : Cluster) where
  | requestVote (term : ℕ) (candidate : NodeId C) (lastIndex lastTerm : ℕ)
  | requestVoteReply (term : ℕ) (granted : Bool) (voter : NodeId C)
  | appendEntries (term : ℕ) (leader : NodeId C) (prevIndex prevTerm : ℕ)
      (entries : List LogEntry) (leaderCommit : ℕ)
  | appendEntriesReply (term : ℕ) (success : Bool) (matchIndex : ℕ) (follower : NodeId C)
  deriving DecidableEq

structure Envelope (C : Cluster) where
  destination : NodeId C
  body : NetworkMessage C
  deriving DecidableEq

/-- A historical vote: term, voter, candidate. -/
abbrev BallotRecord (C : Cluster) := ℕ × NodeId C × NodeId C

structure GlobalState (C : Cluster) where
  servers : NodeId C → ServerState C
  network : List (Envelope C)
  cast : Finset (BallotRecord C)
  received : Finset (BallotRecord C)
  elected : Finset (ℕ × NodeId C)

def initState (C : Cluster) : GlobalState C :=
  ⟨fun _ => {}, [], ∅, ∅, ∅⟩

def setServer (s : GlobalState C) (n : NodeId C) (p : ServerState C) : GlobalState C :=
  { s with servers := Function.update s.servers n p }

/-- Distinct authenticated deliveries are counted once; duplicates cannot add votes. -/
def votesFor (records : Finset (BallotRecord C)) (t : ℕ) (c : NodeId C) :
    Finset (NodeId C) := Finset.univ.filter (fun v => (t, v, c) ∈ records)

@[simp] theorem mem_votesFor (r : Finset (BallotRecord C)) (t : ℕ) (c v : NodeId C) :
    v ∈ votesFor r t c ↔ (t, v, c) ∈ r := by simp [votesFor]

def broadcast (sender : NodeId C) (body : NetworkMessage C) : List (Envelope C) :=
  ((List.finRange C.size).filter (fun n => n ≠ sender)).map (fun n => ⟨n, body⟩)

def rpcTerm (m : NetworkMessage C) : ℕ :=
  match m with
  | .requestVote t _ _ _ | .requestVoteReply t _ _ => t
  | .appendEntries t _ _ _ _ _ | .appendEntriesReply t _ _ _ => t

/-- A delivery removes one occurrence at any position; scheduling is asynchronous. -/
def consume (s : GlobalState C) (before after : List (Envelope C)) : GlobalState C :=
  { s with network := before ++ after }

def termAt (log : List LogEntry) (i : ℕ) : ℕ :=
  if i = 0 then 0 else ((log[i - 1]?).getD ⟨0, 0, 0⟩).term

def prevMatches (log : List LogEntry) (i t : ℕ) : Prop :=
  i ≤ log.length ∧ termAt log i = t

instance (log : List LogEntry) (i t : ℕ) : Decidable (prevMatches log i t) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Keep matching local entries, including a suffix beyond an exhausted RPC batch.
Only the first conflicting entry triggers deletion of the remaining local suffix. -/
def mergeSuffix : List LogEntry → List LogEntry → List LogEntry
  | old, [] => old
  | [], incoming => incoming
  | a :: old, b :: incoming =>
      if a.term = b.term then a :: mergeSuffix old incoming else b :: incoming

def appendEntriesLog (old : List LogEntry) (prev : ℕ) (entries : List LogEntry) :=
  old.take prev ++ mergeSuffix (old.drop prev) entries

@[simp] theorem mergeSuffix_nil (old : List LogEntry) : mergeSuffix old [] = old := by
  cases old <;> rfl

@[simp] theorem heartbeat_preserves_log (old : List LogEntry) (prev : ℕ) :
    appendEntriesLog old prev [] = old := by
  simp [appendEntriesLog]

def upToDateFields (p : ServerState C) (li lt : ℕ) : Prop :=
  lastTerm p.log < lt ∨ (lastTerm p.log = lt ∧ lastIndex p.log ≤ li)

/-- Normal Raft current-term vote guard. The historical evidence is not consulted. -/
def mayVote (p : ServerState C) (candidate : NodeId C) (li lt : ℕ) : Prop :=
  (p.votedFor = none ∨ p.votedFor = some candidate) ∧ upToDateFields p li lt

/-- Observe a strictly newer RPC term without consuming that RPC. -/
def observeTerm (s : GlobalState C) (n : NodeId C) (t : ℕ) : GlobalState C :=
  setServer s n { s.servers n with currentTerm := t, votedFor := none, role := .follower }

def startElection (s : GlobalState C) (n : NodeId C) : GlobalState C :=
  let p := s.servers n
  let t := p.currentTerm + 1
  let s' := setServer s n { p with currentTerm := t, votedFor := some n, role := .candidate }
  { s' with
    cast := insert (t, n, n) s.cast
    received := insert (t, n, n) s.received
    network := s.network ++ broadcast n (.requestVote t n (lastIndex p.log) (lastTerm p.log)) }

def grantVote (s : GlobalState C) (v c : NodeId C)
    (before after : List (Envelope C)) : GlobalState C :=
  let t := (s.servers v).currentTerm
  let s' := setServer s v { s.servers v with votedFor := some c }
  { s' with cast := insert (t, v, c) s.cast
            network := before ++ after ++ [⟨c, .requestVoteReply t true v⟩] }

def receiveVote (s : GlobalState C) (v c : NodeId C) (t : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  { s with received := insert (t, v, c) s.received, network := before ++ after }

def becomeLeader (s : GlobalState C) (n : NodeId C) : GlobalState C :=
  let p := s.servers n
  let s' := setServer s n { p with role := .leader, matchIndex := fun _ => 0 }
  { s' with elected := insert (p.currentTerm, n) s.elected }

def leaderAppend (s : GlobalState C) (n : NodeId C) (cmd : ℕ) : GlobalState C :=
  let p := s.servers n
  let e : LogEntry := ⟨p.log.length + 1, p.currentTerm, cmd⟩
  let s' := setServer s n { p with log := p.log ++ [e] }
  let messages := broadcast n (.appendEntries p.currentTerm n p.log.length
    (termAt p.log p.log.length) [e] p.commitIndex)
  { s' with network := s.network ++ messages }

def handleAppend (s : GlobalState C) (v leader : NodeId C)
    (prev : ℕ) (entries : List LogEntry) (leaderCommit : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  let p := s.servers v
  let log := appendEntriesLog p.log prev entries
  let updated := { p with
    role := .follower
    log := log
    commitIndex := max p.commitIndex (min leaderCommit (prev + entries.length)) }
  let s' := setServer s v updated
  { s' with network := before ++ after ++
      [⟨leader, .appendEntriesReply p.currentTerm true (prev + entries.length) v⟩] }

def denyAppend (s : GlobalState C) (v leader : NodeId C) (t : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  let p := s.servers v
  let s' := setServer s v
    { p with role := if t = p.currentTerm then .follower else p.role }
  { s' with network := before ++ after ++
      [⟨leader, .appendEntriesReply p.currentTerm false 0 v⟩] }

def receiveAppendReply (s : GlobalState C) (leader v : NodeId C) (matched : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  let p := s.servers leader
  let s' := setServer s leader
    { p with matchIndex := Function.update p.matchIndex v (max (p.matchIndex v) matched) }
  { s' with network := before ++ after }

def commitLeader (s : GlobalState C) (n : NodeId C) (i : ℕ) : GlobalState C :=
  setServer s n { s.servers n with commitIndex := max (s.servers n).commitIndex i }

def replicationQuorum (s : GlobalState C) (leader : NodeId C) (i : ℕ) : Finset (NodeId C) :=
  Finset.univ.filter (fun v => v = leader ∨ i ≤ (s.servers leader).matchIndex v)

/-- Operational rules. Guards are local Raft tests, never desired global invariants. -/
inductive Step : GlobalState C → GlobalState C → Prop where
  | observe {s : GlobalState C} {m : Envelope C} : m ∈ s.network →
      (s.servers m.destination).currentTerm < rpcTerm m.body →
      Step s (observeTerm s m.destination (rpcTerm m.body))
  | timeout (s : GlobalState C) (n : NodeId C) :
      (s.servers n).role ≠ .leader → Step s (startElection s n)
  | vote {s : GlobalState C} {v c : NodeId C} {t li lt : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .requestVote t c li lt⟩ :: after →
      t = (s.servers v).currentTerm → mayVote (s.servers v) c li lt →
      Step s (grantVote s v c before after)
  | voteReply {s : GlobalState C} {v c : NodeId C} {t : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨c, .requestVoteReply t true v⟩ :: after →
      t = (s.servers c).currentTerm → (s.servers c).role = .candidate →
      Step s (receiveVote s v c t before after)
  | elect {s : GlobalState C} {n : NodeId C} :
      (s.servers n).role = .candidate →
      majority C (votesFor s.received (s.servers n).currentTerm n) →
      Step s (becomeLeader s n)
  | append {s : GlobalState C} {n : NodeId C} (cmd : ℕ) :
      (s.servers n).role = .leader → Step s (leaderAppend s n cmd)
  | commit {s : GlobalState C} {n : NodeId C} (i : ℕ) :
      (s.servers n).role = .leader → i ≤ (s.servers n).log.length →
      termAt (s.servers n).log i = (s.servers n).currentTerm →
      majority C (replicationQuorum s n i) → Step s (commitLeader s n i)
  | replicate {s : GlobalState C} {n v : NodeId C} (prev count : ℕ) :
      (s.servers n).role = .leader → n ≠ v → prev ≤ (s.servers n).log.length →
      Step s { s with network := s.network ++ [⟨v,
        .appendEntries (s.servers n).currentTerm n prev (termAt (s.servers n).log prev)
          (((s.servers n).log.drop prev).take count) (s.servers n).commitIndex⟩] }
  | appendEntries {s : GlobalState C} {v leader : NodeId C} {t prev pt lc : ℕ}
      {entries : List LogEntry} {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after →
      t = (s.servers v).currentTerm → prevMatches (s.servers v).log prev pt →
      Step s (handleAppend s v leader prev entries lc before after)
  | appendReply {s : GlobalState C} {leader v : NodeId C} {t matched : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨leader, .appendEntriesReply t true matched v⟩ :: after →
      t = (s.servers leader).currentTerm → (s.servers leader).role = .leader →
      Step s (receiveAppendReply s leader v matched before after)
  | rejectVote {s : GlobalState C} {v c : NodeId C} {t li lt : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .requestVote t c li lt⟩ :: after →
      t ≤ (s.servers v).currentTerm →
      (t < (s.servers v).currentTerm ∨ ¬ mayVote (s.servers v) c li lt) →
      Step s { s with network := before ++ after ++
        [⟨c, .requestVoteReply (s.servers v).currentTerm false v⟩] }
  | rejectAppend {s : GlobalState C} {v leader : NodeId C} {t prev pt lc : ℕ}
      {entries : List LogEntry} {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after →
      t ≤ (s.servers v).currentTerm →
      (t < (s.servers v).currentTerm ∨ ¬ prevMatches (s.servers v).log prev pt) →
      Step s (denyAppend s v leader t before after)
  | drop {s : GlobalState C} {m : Envelope C} {before after : List (Envelope C)} :
      s.network = before ++ m :: after → Step s (consume s before after)
  | duplicate {s : GlobalState C} {m : Envelope C} : m ∈ s.network →
      Step s { s with network := m :: s.network }

inductive Reachable : GlobalState C → Prop where
  | init : Reachable (initState C)
  | step {s s' : GlobalState C} : Reachable s → Step s s' → Reachable s'


/-- Actual vote events are unique per voter and term, including past terms. -/
structure VoteHistoryValid (s : GlobalState C) : Prop where
  unique : ∀ t v a b, (t, v, a) ∈ s.cast → (t, v, b) ∈ s.cast → a = b
  bound : ∀ t v c, (t, v, c) ∈ s.cast → t ≤ (s.servers v).currentTerm
  binding : ∀ t v c, (t, v, c) ∈ s.cast → t = (s.servers v).currentTerm →
    (s.servers v).votedFor = some c

theorem VoteHistoryValid.local_update {s : GlobalState C} (h : VoteHistoryValid s)
    (n : NodeId C) (p : ServerState C)
    (ht : (s.servers n).currentTerm ≤ p.currentTerm)
    (hv : p.currentTerm = (s.servers n).currentTerm →
      ∀ c, (s.servers n).votedFor = some c → p.votedFor = some c) :
    VoteHistoryValid (setServer s n p) := by
  constructor
  · exact h.unique
  · intro t v c hc
    by_cases hn : v = n
    · subst v
      simpa [setServer] using (h.bound t n c hc).trans ht
    · simpa [setServer, Function.update_of_ne hn] using h.bound t v c hc
  · intro t v c hc he
    by_cases hn : v = n
    · subst v
      simp only [setServer, Function.update_self] at he ⊢
      have hb := h.bound t n c hc
      have eqt : p.currentTerm = (s.servers n).currentTerm := by omega
      exact hv eqt c (h.binding t n c hc (by omega))
    · simp only [setServer, Function.update_of_ne hn] at he ⊢
      exact h.binding t v c hc he

theorem VoteHistoryValid.insert_vote {s : GlobalState C} (h : VoteHistoryValid s)
    (v c : NodeId C) (hv : (s.servers v).votedFor = some c) :
    VoteHistoryValid { s with cast := insert ((s.servers v).currentTerm, v, c) s.cast } := by
  constructor
  · intro t w a b ha hb
    simp only [Finset.mem_insert, Prod.mk.injEq] at ha hb
    rcases ha with ⟨ht, hw, ha⟩ | ha <;> rcases hb with ⟨ht', hw', hb⟩ | hb
    · exact ha.trans hb.symm
    · subst t; subst w; subst a
      exact Option.some.inj (hv.symm.trans (h.binding _ _ _ hb rfl))
    · subst t; subst w; subst b
      exact Option.some.inj ((h.binding _ _ _ ha rfl).symm.trans hv)
    · exact h.unique t w a b ha hb
  · intro t w a ha
    simp only [Finset.mem_insert, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl, rfl⟩ | ha
    · exact le_rfl
    · exact h.bound t w a ha
  · intro t w a ha he
    simp only [Finset.mem_insert, Prod.mk.injEq] at ha
    rcases ha with ⟨rfl, rfl, rfl⟩ | ha
    · exact hv
    · exact h.binding t w a ha he

/-- Changes to networking and other ghost records do not change vote history validity. -/
theorem VoteHistoryValid.frame {s s' : GlobalState C} (h : VoteHistoryValid s)
    (hs : s'.servers = s.servers) (hc : s'.cast = s.cast) : VoteHistoryValid s' := by
  constructor
  · simpa only [hc] using h.unique
  · simpa only [hc, hs] using h.bound
  · simpa only [hc, hs] using h.binding

theorem VoteHistoryValid.frame_votes {s s' : GlobalState C} (h : VoteHistoryValid s)
    (hc : s'.cast = s.cast)
    (ht : ∀ n, (s'.servers n).currentTerm = (s.servers n).currentTerm)
    (hv : ∀ n, (s'.servers n).votedFor = (s.servers n).votedFor) : VoteHistoryValid s' := by
  constructor
  · simpa only [hc] using h.unique
  · simpa only [hc, ht] using h.bound
  · simpa only [hc, ht, hv] using h.binding

theorem vote_history_step {s s' : GlobalState C} (h : VoteHistoryValid s)
    (step : Step s s') : VoteHistoryValid s' := by
  cases step with
  | observe _ ht =>
    apply h.local_update _ _ (Nat.le_of_lt ht)
    intro he
    dsimp at he
    omega
  | timeout n _ =>
    have hu := h.local_update n
      { s.servers n with
        currentTerm := (s.servers n).currentTerm + 1
        votedFor := some n
        role := .candidate }
      (by simp) (by intro he; dsimp at he; omega)
    exact (hu.insert_vote n n (by simp [setServer])).frame rfl (by simp [startElection, setServer])
  | @vote v c t li lt before after _ _ guard =>
    have hu := h.local_update v { s.servers v with votedFor := some c } le_rfl (by
      intro _ a ha
      rcases guard.1 with hn | hn
      · simp [hn] at ha
      · simpa [hn] using ha)
    exact (hu.insert_vote v c (by simp [setServer])).frame rfl
      (by simp [grantVote, setServer])
  | voteReply => exact h.frame rfl rfl
  | elect =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [becomeLeader, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | append =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [leaderAppend, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | commit =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [commitLeader, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | replicate => exact h.frame rfl rfl
  | appendEntries =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [handleAppend, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | appendReply =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [receiveAppendReply, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | rejectVote => exact h.frame rfl rfl
  | rejectAppend =>
    apply h.frame_votes
    · rfl
    all_goals
      intro n
      simp only [denyAppend, setServer, Function.update_apply]
      split_ifs <;> simp_all
  | drop => exact h.frame rfl rfl
  | duplicate => exact h.frame rfl rfl

theorem vote_history_reachable {s : GlobalState C} (h : Reachable s) :
    VoteHistoryValid s := by
  induction h with
  | init => constructor <;> simp [initState]
  | step _ step ih => exact vote_history_step ih step

theorem single_vote_preserved {s : GlobalState C} (h : Reachable s)
    (t : ℕ) (v a b : NodeId C) (ha : (t, v, a) ∈ s.cast) (hb : (t, v, b) ∈ s.cast) :
    a = b := (vote_history_reachable h).unique t v a b ha hb

theorem term_step_monotone {s s' : GlobalState C} (h : Step s s') (n : NodeId C) :
    (s.servers n).currentTerm ≤ (s'.servers n).currentTerm := by
  cases h <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer,
      Function.update_apply] <;>
    (try split_ifs) <;> simp_all
  omega


theorem cast_step_monotone {s s' : GlobalState C} (h : Step s s') : s.cast ⊆ s'.cast := by
  cases h <;> simp [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
    leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer]

/-- Extract only positive vote replies from an addressed queue. -/
def replyVotes : List (Envelope C) → Finset (BallotRecord C)
  | [] => ∅
  | m :: ms => match m.body with
    | .requestVoteReply t true v => insert (t, v, m.destination) (replyVotes ms)
    | _ => replyVotes ms

@[simp] theorem replyVotes_append (a b : List (Envelope C)) :
    replyVotes (a ++ b) = replyVotes a ∪ replyVotes b := by
  induction a with
  | nil => simp [replyVotes]
  | cons m ms ih =>
    cases m with
    | mk dst body =>
      cases body with
      | requestVoteReply t granted v => cases granted <;> simp [replyVotes, ih]
      | requestVote => simp [replyVotes, ih]
      | appendEntries => simp [replyVotes, ih]
      | appendEntriesReply => simp [replyVotes, ih]

theorem replyVotes_map (nodes : List (NodeId C)) (body : NetworkMessage C)
    (h : ∀ t v, body ≠ .requestVoteReply t true v) :
    replyVotes (nodes.map (fun n => ⟨n, body⟩)) = ∅ := by
  induction nodes with
  | nil => rfl
  | cons n ns ih =>
    cases body <;> simp [replyVotes, ih]

theorem replyVotes_broadcast (n : NodeId C) (body : NetworkMessage C)
    (h : ∀ t v, body ≠ .requestVoteReply t true v) :
    replyVotes (broadcast n body) = ∅ := replyVotes_map _ body h

@[simp] theorem replyVotes_requestBroadcast (n c : NodeId C) (t li lt : ℕ) :
    replyVotes (broadcast n (.requestVote t c li lt)) = ∅ :=
  replyVotes_broadcast n _ (by intros; intro he; cases he)

@[simp] theorem replyVotes_appendBroadcast (n leader : NodeId C) (t pi pt lc : ℕ)
    (entries : List LogEntry) :
    replyVotes (broadcast n (.appendEntries t leader pi pt entries lc)) = ∅ :=
  replyVotes_broadcast n _ (by intros; intro he; cases he)

structure TransportSound (s : GlobalState C) : Prop where
  network : replyVotes s.network ⊆ s.cast
  received : s.received ⊆ s.cast

theorem TransportSound.remainder {s : GlobalState C} (h : TransportSound s)
    {before after : List (Envelope C)} {m : Envelope C}
    (he : s.network = before ++ m :: after) :
    replyVotes (before ++ after) ⊆ s.cast := by
  have hn := h.network
  rw [he, replyVotes_append] at hn
  rw [replyVotes_append]
  apply Finset.union_subset
  · exact fun _ hm => hn (Finset.mem_union_left _ hm)
  · intro x hx
    apply hn
    apply Finset.mem_union_right
    cases m with
    | mk dst body =>
      cases body with
      | requestVoteReply t granted v => cases granted <;> simp [replyVotes, hx]
      | requestVote => exact hx
      | appendEntries => exact hx
      | appendEntriesReply => exact hx

theorem transport_step {s s' : GlobalState C} (h : TransportSound s)
    (step : Step s s') : TransportSound s' := by
  have grow := cast_step_monotone step
  have oldNetwork := h.network.trans grow
  have oldReceived := h.received.trans grow
  constructor
  · cases step with
    | observe => exact oldNetwork
    | timeout n _ =>
      simpa [startElection] using oldNetwork
    | @vote v c t li lt before after he _ _ =>
      have rem := (h.remainder he).trans grow
      simpa [grantVote, replyVotes] using
        (Finset.insert_subset (Finset.mem_insert_self ((s.servers v).currentTerm, v, c) s.cast) rem)
    | voteReply he _ _ => exact (h.remainder he).trans grow
    | elect => exact oldNetwork
    | append cmd _ =>
      simpa [leaderAppend] using oldNetwork
    | commit => exact oldNetwork
    | replicate => simpa [replyVotes] using oldNetwork
    | appendEntries he _ _ => simpa [handleAppend, replyVotes] using (h.remainder he).trans grow
    | appendReply he _ _ => exact (h.remainder he).trans grow
    | rejectVote he _ _ => simpa [replyVotes] using (h.remainder he).trans grow
    | rejectAppend he _ _ => simpa [denyAppend, replyVotes] using (h.remainder he).trans grow
    | drop he => exact (h.remainder he).trans grow
    | @duplicate m hm =>
      have part : replyVotes [m] ⊆ s.cast := by
        intro x hx
        have hn := h.network
        have mem : ∀ (a : Envelope C) (xs : List (Envelope C)), a ∈ xs →
            replyVotes [a] ⊆ replyVotes xs := by
          intro a xs ha
          induction xs with
          | nil => simp at ha
          | cons b bs ih =>
            rcases List.mem_cons.mp ha with rfl | hb
            · cases a with
              | mk dst body =>
                cases body with
                | requestVoteReply t granted v => cases granted <;> simp [replyVotes]
                | requestVote => simp [replyVotes]
                | appendEntries => simp [replyVotes]
                | appendEntriesReply => simp [replyVotes]
            · have hi := ih hb
              cases b with
              | mk dst body =>
                cases body with
                | requestVoteReply t granted v =>
                  cases granted
                  · exact hi
                  · exact hi.trans (Finset.subset_insert _ _)
                | requestVote => exact hi
                | appendEntries => exact hi
                | appendEntriesReply => exact hi
        exact hn (mem m s.network hm hx)
      change replyVotes ([m] ++ s.network) ⊆ _
      rw [replyVotes_append]
      exact Finset.union_subset (part.trans grow) oldNetwork
  · cases step with
    | timeout n _ =>
      exact Finset.insert_subset (Finset.mem_insert_self ..) oldReceived
    | @voteReply v c t before after he _ _ =>
      have present : (t, v, c) ∈ s.cast := by
        apply h.network
        rw [he, replyVotes_append]
        apply Finset.mem_union_right
        exact Finset.mem_insert_self ..
      exact Finset.insert_subset (grow present) oldReceived
    | observe => exact oldReceived
    | vote => exact oldReceived
    | elect => exact oldReceived
    | append => exact oldReceived
    | commit => exact oldReceived
    | replicate => exact oldReceived
    | appendEntries => exact oldReceived
    | appendReply => exact oldReceived
    | rejectVote => exact oldReceived
    | rejectAppend => exact oldReceived
    | drop => exact oldReceived
    | duplicate => exact oldReceived

theorem transport_reachable {s : GlobalState C} (h : Reachable s) : TransportSound s := by
  induction h with
  | init => constructor <;> simp [initState, replyVotes]
  | step _ step ih => exact transport_step ih step

theorem majority_votes_mono {a b : Finset (BallotRecord C)} (h : a ⊆ b)
    (t : ℕ) (c : NodeId C) (hm : majority C (votesFor a t c)) :
    majority C (votesFor b t c) := by
  have hs : votesFor a t c ⊆ votesFor b t c := by
    intro v hv
    exact (mem_votesFor b t c v).mpr (h ((mem_votesFor a t c v).mp hv))
  have hc := Finset.card_le_card hs
  dsimp [majority] at *
  omega

def ElectionsSound (s : GlobalState C) : Prop :=
  ∀ t c, (t, c) ∈ s.elected → majority C (votesFor s.cast t c)

def LeadersCovered (s : GlobalState C) : Prop :=
  ∀ n, (s.servers n).role = .leader → ((s.servers n).currentTerm, n) ∈ s.elected

theorem elections_step {s s' : GlobalState C} (h : ElectionsSound s)
    (ht : TransportSound s) (step : Step s s') : ElectionsSound s' := by
  have grow := cast_step_monotone step
  have old : ∀ t c, (t, c) ∈ s.elected → majority C (votesFor s'.cast t c) :=
    fun t c hc => majority_votes_mono grow t c (h t c hc)
  cases step with
  | @elect n _ majority =>
    intro t c hc
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl⟩ | hc
    · exact majority_votes_mono ht.received _ _ majority
    · exact old _ _ hc
  | observe => exact old
  | timeout => exact old
  | vote => exact old
  | voteReply => exact old
  | append => exact old
  | commit => exact old
  | replicate => exact old
  | appendEntries => exact old
  | appendReply => exact old
  | rejectVote => exact old
  | rejectAppend => exact old
  | drop => exact old
  | duplicate => exact old

theorem leaders_step {s s' : GlobalState C} (h : LeadersCovered s)
    (step : Step s s') : LeadersCovered s' := by
  intro n hn
  cases step <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer,
      Function.update_apply] at hn ⊢ <;>
    (try split_ifs at hn ⊢) <;> simp_all [LeadersCovered]

theorem elections_reachable {s : GlobalState C} (h : Reachable s) :
    ElectionsSound s ∧ LeadersCovered s := by
  induction h with
  | init => constructor <;> simp [ElectionsSound, LeadersCovered, initState]
  | step reach step ih =>
    exact ⟨elections_step ih.1 (transport_reachable reach) step, leaders_step ih.2 step⟩

/-- Historical election uniqueness, stronger than simultaneous leader uniqueness. -/
theorem election_history_safety {s : GlobalState C} (h : Reachable s)
    (t : ℕ) (a b : NodeId C) (ha : (t, a) ∈ s.elected) (hb : (t, b) ∈ s.elected) :
    a = b := by
  have eh := (elections_reachable h).1
  obtain ⟨v, hv⟩ := quorum_intersection C _ _ (eh t a ha) (eh t b hb)
  obtain ⟨va, vb⟩ := Finset.mem_inter.mp hv
  exact single_vote_preserved h t v a b (by simpa using va) (by simpa using vb)

theorem election_safety {s : GlobalState C} (h : Reachable s) (a b : NodeId C)
    (ha : (s.servers a).role = .leader) (hb : (s.servers b).role = .leader)
    (ht : (s.servers a).currentTerm = (s.servers b).currentTerm) : a = b := by
  have covered := (elections_reachable h).2
  apply election_history_safety h (s.servers a).currentTerm a b (covered a ha)
  rw [ht]
  exact covered b hb

theorem election_safety_step {s s' : GlobalState C} (h : Reachable s) (step : Step s s')
    (a b : NodeId C) (ha : (s'.servers a).role = .leader)
    (hb : (s'.servers b).role = .leader)
    (ht : (s'.servers a).currentTerm = (s'.servers b).currentTerm) : a = b :=
  election_safety (h.step step) a b ha hb ht


/-- Append-only is a tenure property: the node remains leader of the same term. -/
theorem leader_append_only_step {s s' : GlobalState C} (step : Step s s')
    (n : NodeId C) (before : (s.servers n).role = .leader)
    (after : (s'.servers n).role = .leader)
    (sameTerm : (s.servers n).currentTerm = (s'.servers n).currentTerm) :
    (s.servers n).log.IsPrefix (s'.servers n).log := by
  cases step <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer,
      Function.update_apply] at before after sameTerm ⊢ <;>
    (try split_ifs at after sameTerm ⊢) <;> simp_all

/-- Command agreement wherever aligned entries have the same term. This is an
explicit compatibility premise for the local log-operation lemmas below. -/
def CompatibleEntries : List LogEntry → List LogEntry → Prop
  | [], _ | _, [] => True
  | a :: old, b :: incoming => (a.term = b.term → a = b) ∧ CompatibleEntries old incoming

theorem mergeSuffix_choice (old incoming : List LogEntry)
    (h : CompatibleEntries old incoming) :
    mergeSuffix old incoming = old ∨ mergeSuffix old incoming = incoming := by
  induction old generalizing incoming with
  | nil => cases incoming <;> simp [mergeSuffix]
  | cons a old ih =>
    cases incoming with
    | nil => simp
    | cons b incoming =>
      change (a.term = b.term → a = b) ∧ CompatibleEntries old incoming at h
      by_cases ht : a.term = b.term
      · have hab := h.1 ht
        subst b
        rcases ih incoming h.2 with ho | hi
        · left; simp [mergeSuffix, ho]
        · right; simp [mergeSuffix, hi]
      · right; simp [mergeSuffix, ht]

/-- A successful merge is either unchanged local history or the received source
prefix. Both premises concern the inputs; neither assumes a safe output. -/
theorem append_entries_log_choice (old source : List LogEntry) (prev count : ℕ)
    (hp : old.take prev = source.take prev)
    (hc : CompatibleEntries (old.drop prev) ((source.drop prev).take count)) :
    appendEntriesLog old prev ((source.drop prev).take count) = old ∨
    appendEntriesLog old prev ((source.drop prev).take count) = source.take (prev + count) := by
  rcases mergeSuffix_choice _ _ hc with ho | hi
  · left; simp [appendEntriesLog, ho]
  · right; rw [appendEntriesLog, hi, hp, List.take_add]

/-- Positional Log Matching: equal terms at a shared index imply equal prefixes.
For logs indexed consecutively from one, this is the usual (index, term) condition. -/
def LogMatching (a b : List LogEntry) : Prop :=
  ∀ i x y, a[i]? = some x → b[i]? = some y → x.term = y.term →
    a.take (i + 1) = b.take (i + 1)

theorem LogMatching.take_left {a b : List LogEntry} (h : LogMatching a b) (n : ℕ) :
    LogMatching (a.take n) b := by
  intro i x y hx hy ht
  have hi : i < n := by
    by_contra hn
    have hz := List.getElem?_take_eq_none (l := a) (by omega : n ≤ i)
    rw [hz] at hx
    contradiction
  rw [List.getElem?_take_of_lt hi] at hx
  simpa [List.take_take, Nat.min_eq_left (by omega : i + 1 ≤ n)] using h i x y hx hy ht

/-- Local preservation of Log Matching against an arbitrary third log. The
compatibility of the RPC source must still be derived from reachable histories
before this can be used as a global reachable-state Log Matching theorem. -/
theorem log_matching_step (old source other : List LogEntry) (prev count : ℕ)
    (hp : old.take prev = source.take prev)
    (hc : CompatibleEntries (old.drop prev) ((source.drop prev).take count))
    (ho : LogMatching old other) (hs : LogMatching source other) :
    LogMatching (appendEntriesLog old prev ((source.drop prev).take count)) other := by
  rcases append_entries_log_choice old source prev count hp hc with he | he
  · rw [he]; exact ho
  · rw [he]; exact hs.take_left _

/-- All entries before the checked predecessor survive a successful AppendEntries. -/
theorem append_entries_preserves_predecessor (old : List LogEntry) (prev : ℕ)
    (entries : List LogEntry) :
    (old.take prev).IsPrefix (appendEntriesLog old prev entries) :=
  ⟨mergeSuffix (old.drop prev) entries, rfl⟩


/-- Appending a fresh term at the new index preserves matching with another log.
Freshness is an input obligation, not yet a theorem about all reachable RPC histories. -/
theorem log_matching_append {old other : List LogEntry} (h : LogMatching old other)
    (e : LogEntry)
    (fresh : ∀ y, other[old.length]? = some y → e.term ≠ y.term) :
    LogMatching (old ++ [e]) other := by
  intro i x y hx hy ht
  by_cases hi : i < old.length
  · rw [List.getElem?_append_left hi] at hx
    rw [List.take_append_of_le_length (by omega : i + 1 ≤ old.length)]
    exact h i x y hx hy ht
  · have bound : i < (old ++ [e]).length := by
      by_contra hn
      rw [List.getElem?_eq_none (by omega)] at hx
      contradiction
    have he : i = old.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst i
    simp only [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.some.injEq] at hx
    subst x
    exact False.elim (fresh y hy ht)

/-! Small executable witnesses exercise the protocol, not just the arithmetic lemmas. -/
namespace Examples

def cluster : Cluster := ⟨3, by decide⟩
def n0 : NodeId cluster := ⟨0, by decide⟩
def n1 : NodeId cluster := ⟨1, by decide⟩
def n2 : NodeId cluster := ⟨2, by decide⟩
def initial : GlobalState cluster := initState cluster
def campaigning : GlobalState cluster := startElection initial n0

def voteRequest (v : NodeId cluster) : Envelope cluster :=
  ⟨v, .requestVote 1 n0 0 0⟩

def prepared : GlobalState cluster := observeTerm campaigning n1 1

def granted : GlobalState cluster := grantVote prepared n1 n0 [] [voteRequest n2]
def received : GlobalState cluster := receiveVote granted n1 n0 1 [voteRequest n2] []
def elected : GlobalState cluster := becomeLeader received n0
def appended : GlobalState cluster := leaderAppend elected n0 7

theorem campaigning_reachable : Reachable campaigning :=
  .step .init (Step.timeout initial n0 (by decide))

theorem prepared_reachable : Reachable prepared := by
  apply campaigning_reachable.step
  apply Step.observe (m := voteRequest n1)
  · decide
  · decide

theorem granted_reachable : Reachable granted := by
  apply prepared_reachable.step
  apply Step.vote (t := 1) (li := 0) (lt := 0)
  · decide
  · decide
  · constructor
    · left; decide
    · right; constructor <;> decide

theorem received_reachable : Reachable received := by
  apply granted_reachable.step
  apply Step.voteReply
  · decide
  · decide
  · decide

theorem elected_reachable : Reachable elected := by
  apply received_reachable.step
  apply Step.elect
  · decide
  · change 3 < 2 * (votesFor received.received (received.servers n0).currentTerm n0).card
    decide

theorem appended_reachable : Reachable appended :=
  elected_reachable.step (Step.append 7 (by decide))

theorem nonempty_leader_log :
    (appended.servers n0).role = .leader ∧
    (appended.servers n0).log = [⟨1, 1, 7⟩] := by decide

def appendRequest (v : NodeId cluster) : Envelope cluster :=
  ⟨v, .appendEntries 1 n0 0 0 [⟨1, 1, 7⟩] 0⟩

def replicated : GlobalState cluster :=
  handleAppend appended n1 n0 0 [⟨1, 1, 7⟩] 0 [voteRequest n2] [appendRequest n2]

def acknowledged : GlobalState cluster :=
  receiveAppendReply replicated n0 n1 1 [voteRequest n2, appendRequest n2] []

def committed : GlobalState cluster := commitLeader acknowledged n0 1

theorem replicated_reachable : Reachable replicated := by
  apply appended_reachable.step
  apply Step.appendEntries (t := 1) (pt := 0)
  · decide
  · decide
  · constructor <;> decide

theorem acknowledged_reachable : Reachable acknowledged := by
  apply replicated_reachable.step
  apply Step.appendReply (t := 1)
  · decide
  · decide
  · decide

theorem committed_reachable : Reachable committed := by
  apply acknowledged_reachable.step
  apply Step.commit
  · decide
  · decide
  · decide
  · change 3 < 2 * (replicationQuorum acknowledged n0 1).card
    decide

theorem replicated_and_committed :
    (committed.servers n0).commitIndex = 1 ∧
    (committed.servers n1).log = [⟨1, 1, 7⟩] := by decide

/-- A duplicated reply has no effect on the cardinality of collected votes. -/
theorem duplicate_reply_not_an_extra_vote :
    (votesFor (insert (1, n1, n0) received.received) 1 n0).card = 2 := by decide

/-- Same-term RequestVote for a different candidate is rejected even with an up-to-date log. -/
theorem second_candidate_rejected : ¬ mayVote (granted.servers n1) n2 0 0 := by
  intro h
  rcases h.1 with h | h <;> change some n0 = _ at h <;> cases h

/-- A short duplicate batch retains the follower's longer suffix. -/
theorem short_batch_preserves_suffix :
    appendEntriesLog [⟨1, 1, 7⟩, ⟨2, 1, 8⟩, ⟨3, 2, 9⟩] 1 [⟨2, 1, 8⟩] =
      [⟨1, 1, 7⟩, ⟨2, 1, 8⟩, ⟨3, 2, 9⟩] := by decide

/-- A genuine conflicting term replaces the suffix, including its old final entry. -/
theorem conflicting_batch_replaces_suffix :
    appendEntriesLog [⟨1, 1, 7⟩, ⟨2, 1, 8⟩, ⟨3, 1, 9⟩] 1 [⟨2, 2, 10⟩] =
      [⟨1, 1, 7⟩, ⟨2, 2, 10⟩] := by decide

end Examples


/-- The suite exposes the exact boundary: election invariants are reachable-state
results; Log Matching preservation still has explicit input-log compatibility premises. -/
structure RaftStateMachineFormalSuite : Prop where
  h_term : ∀ {C : Cluster} {s s' : GlobalState C}, Step s s' → ∀ n,
    (s.servers n).currentTerm ≤ (s'.servers n).currentTerm
  h_vote : ∀ {C : Cluster} {s : GlobalState C}, Reachable s → ∀ t v a b,
    (t, v, a) ∈ s.cast → (t, v, b) ∈ s.cast → a = b
  h_election : ∀ {C : Cluster} {s : GlobalState C}, Reachable s → ∀ t a b,
    (t, a) ∈ s.elected → (t, b) ∈ s.elected → a = b
  h_leader : ∀ {C : Cluster} {s s' : GlobalState C}, Step s s' → ∀ n,
    (s.servers n).role = .leader → (s'.servers n).role = .leader →
    (s.servers n).currentTerm = (s'.servers n).currentTerm →
    (s.servers n).log.IsPrefix (s'.servers n).log
  h_matching : ∀ old source other prev count,
    old.take prev = source.take prev →
    CompatibleEntries (old.drop prev) ((source.drop prev).take count) →
    LogMatching old other → LogMatching source other →
    LogMatching (appendEntriesLog old prev ((source.drop prev).take count)) other
  h_fresh_append : ∀ {old other : List LogEntry}, LogMatching old other → ∀ e,
    (∀ y, other[old.length]? = some y → e.term ≠ y.term) →
    LogMatching (old ++ [e]) other
  h_heartbeat : ∀ old prev, appendEntriesLog old prev [] = old
  h_nonempty : Reachable Examples.committed ∧
    (Examples.committed.servers Examples.n0).commitIndex = 1 ∧
    (Examples.committed.servers Examples.n1).log = [⟨1, 1, 7⟩]

theorem raft_state_machine_master_suite : RaftStateMachineFormalSuite := {
  h_term := term_step_monotone
  h_vote := single_vote_preserved
  h_election := election_history_safety
  h_leader := leader_append_only_step
  h_matching := log_matching_step
  h_fresh_append := log_matching_append
  h_heartbeat := heartbeat_preserves_log
  h_nonempty := ⟨Examples.committed_reachable, Examples.replicated_and_committed⟩
}

end DistributedRaftStateMachine
