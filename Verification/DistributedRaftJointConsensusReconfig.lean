/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedRaftStateMachine
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Sort

/-!
# Operational Raft joint-consensus reconfiguration

One fixed old → joint → new transition, with immediate local configuration activation,
partial AppendEntries batches, rollback, delayed replies, and leader retirement.
Reachability implies election safety, log matching, historical commit-index soundness,
and leader completeness. The proof nests induction on leader terms inside induction
on execution steps; the auxiliary history hypotheses are discharged before export.
No transition guard assumes a desired safety invariant. Repeated reconfiguration,
snapshots, crash/recovery, Byzantine behavior, and liveness are outside this model.
-/
namespace DistributedRaftJointConsensusReconfig

abbrev NodeId := ℕ
open DistributedRaftLeaderCompleteness (Role)

inductive Config where
  | stable (members : Finset NodeId)
  | joint (oldMembers newMembers : Finset NodeId)
  deriving DecidableEq

inductive EntryPayload where
  | command (data : ℕ)
  | config (cfg : Config)
  deriving DecidableEq

structure LogEntry where
  index : ℕ
  term : ℕ
  payload : EntryPayload
  deriving DecidableEq

def Config.members : Config → Finset NodeId
  | .stable c => c
  | .joint a b => a ∪ b

def is_stable_quorum (Q C : Finset NodeId) : Prop :=
  Q ⊆ C ∧ C.card < 2 * (Q ∩ C).card

def is_joint_quorum (Q A B : Finset NodeId) : Prop :=
  A.card < 2 * (Q ∩ A).card ∧ B.card < 2 * (Q ∩ B).card

def has_quorum (Q : Finset NodeId) : Config → Prop
  | .stable C => is_stable_quorum Q C
  | .joint A B => is_joint_quorum Q A B

instance (Q C : Finset NodeId) : Decidable (is_stable_quorum Q C) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (Q A B : Finset NodeId) : Decidable (is_joint_quorum Q A B) :=
  inferInstanceAs (Decidable (_ ∧ _))
instance (Q : Finset NodeId) (cfg : Config) : Decidable (has_quorum Q cfg) := by
  cases cfg <;> unfold has_quorum <;> infer_instance

def active_config (log : List LogEntry) (default_cfg : Config) : Config :=
  log.foldl (fun cfg e => match e.payload with
    | .command _ => cfg
    | .config next => next) default_cfg

@[simp] theorem active_config_nil (cfg : Config) : active_config [] cfg = cfg := rfl

theorem active_config_append (a b : List LogEntry) (cfg : Config) :
    active_config (a ++ b) cfg = active_config b (active_config a cfg) :=
  List.foldl_append

@[simp] theorem active_config_command (log : List LogEntry) (cfg : Config) (i t cmd : ℕ) :
    active_config (log ++ [⟨i, t, .command cmd⟩]) cfg = active_config log cfg := by
  rw [active_config_append]; rfl

@[simp] theorem active_config_write (log : List LogEntry) (cfg next : Config) (i t : ℕ) :
    active_config (log ++ [⟨i, t, .config next⟩]) cfg = next := by
  rw [active_config_append]; rfl

/-- No commit-index test is part of activation. -/
theorem raft_reconfig_rollback_on_truncate (pre suffix : List LogEntry) (cfg : Config) :
    active_config ((pre ++ suffix).take pre.length) cfg = active_config pre cfg := by
  simp

/-- Index/term fields of the last entry are the ordinary Raft voting fields. -/
def lastTerm (log : List LogEntry) : ℕ := (log.getLast?).map LogEntry.term |>.getD 0
def lastIndex (log : List LogEntry) : ℕ := (log.getLast?).map LogEntry.index |>.getD 0

/-- One transition, with a fixed ambient universe independent of voting membership. -/
structure Transition where
  oldMembers : Finset NodeId
  newMembers : Finset NodeId
  old_nonempty : oldMembers.Nonempty
  new_nonempty : newMembers.Nonempty
  deriving DecidableEq

def Transition.nodes (C : Transition) := C.oldMembers ∪ C.newMembers

def Transition.initial (C : Transition) : Config := .stable C.oldMembers

def Transition.jointConfig (C : Transition) : Config := .joint C.oldMembers C.newMembers

def Transition.finalConfig (C : Transition) : Config := .stable C.newMembers

variable {C : Transition}
structure ServerState (C : Transition) where
  currentTerm : ℕ := 0
  votedFor : Option (NodeId) := none
  role : Role := .follower
  log : List LogEntry := []
  commitIndex : ℕ := 0
  matchIndex : NodeId → ℕ := fun _ => 0

inductive NetworkMessage (C : Transition) where
  | requestVote (term : ℕ) (candidate : NodeId) (lastIndex lastTerm : ℕ)
  | requestVoteReply (term : ℕ) (granted : Bool) (voter : NodeId)
  | appendEntries (term : ℕ) (leader : NodeId) (prevIndex prevTerm : ℕ)
      (entries : List LogEntry) (leaderCommit : ℕ)
  | appendEntriesReply (term : ℕ) (success : Bool) (matchIndex : ℕ) (follower : NodeId)
  deriving DecidableEq

structure Envelope (C : Transition) where
  destination : NodeId
  body : NetworkMessage C
  deriving DecidableEq

/-- A historical vote: term, voter, candidate. -/
abbrev BallotRecord (_C : Transition) := ℕ × NodeId × NodeId

structure GlobalState (C : Transition) where
  servers : NodeId → ServerState C
  network : List (Envelope C)
  cast : Finset (BallotRecord C)
  received : Finset (BallotRecord C)
  elected : Finset (ℕ × NodeId × Config)

def initState (C : Transition) : GlobalState C :=
  ⟨fun _ => {}, [], ∅, ∅, ∅⟩

def setServer (s : GlobalState C) (n : NodeId) (p : ServerState C) : GlobalState C :=
  { s with servers := Function.update s.servers n p }

/-- Distinct authenticated deliveries are counted once; duplicates cannot add votes. -/
def votesFor (records : Finset (BallotRecord C)) (t : ℕ) (c : NodeId) :
    Finset (NodeId) := (records.image (fun b => b.2.1)).filter (fun v => (t, v, c) ∈ records)

@[simp] theorem mem_votesFor (r : Finset (BallotRecord C)) (t : ℕ) (c v : NodeId) :
    v ∈ votesFor r t c ↔ (t, v, c) ∈ r := by
  simp only [votesFor, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨Finset.mem_image.mpr ⟨(t, v, c), h, rfl⟩, h⟩⟩

def broadcast (sender : NodeId) (body : NetworkMessage C) : List (Envelope C) :=
  ((C.nodes.sort (· ≤ ·)).filter (fun n => n ≠ sender)).map (fun n => ⟨n, body⟩)

def rpcTerm (m : NetworkMessage C) : ℕ :=
  match m with
  | .requestVote t _ _ _ | .requestVoteReply t _ _ => t
  | .appendEntries t _ _ _ _ _ | .appendEntriesReply t _ _ _ => t

/-- A delivery removes one occurrence at any position; scheduling is asynchronous. -/
def consume (s : GlobalState C) (before after : List (Envelope C)) : GlobalState C :=
  { s with network := before ++ after }

def termAt (log : List LogEntry) (i : ℕ) : ℕ :=
  if i = 0 then 0 else ((log[i - 1]?).getD ⟨0, 0, .command 0⟩).term

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
def mayVote (p : ServerState C) (candidate : NodeId) (li lt : ℕ) : Prop :=
  (p.votedFor = none ∨ p.votedFor = some candidate) ∧ upToDateFields p li lt

/-- Observe a strictly newer RPC term without consuming that RPC. -/
def observeTerm (s : GlobalState C) (n : NodeId) (t : ℕ) : GlobalState C :=
  setServer s n { s.servers n with currentTerm := t, votedFor := none, role := .follower }

def startElection (s : GlobalState C) (n : NodeId) : GlobalState C :=
  let p := s.servers n
  let t := p.currentTerm + 1
  let s' := setServer s n { p with currentTerm := t, votedFor := some n, role := .candidate }
  { s' with
    cast := insert (t, n, n) s.cast
    received := insert (t, n, n) s.received
    network := s.network ++ broadcast n (.requestVote t n (lastIndex p.log) (lastTerm p.log)) }

def grantVote (s : GlobalState C) (v c : NodeId)
    (before after : List (Envelope C)) : GlobalState C :=
  let t := (s.servers v).currentTerm
  let s' := setServer s v { s.servers v with votedFor := some c }
  { s' with cast := insert (t, v, c) s.cast
            network := before ++ after ++ [⟨c, .requestVoteReply t true v⟩] }

def receiveVote (s : GlobalState C) (v c : NodeId) (t : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  { s with received := insert (t, v, c) s.received, network := before ++ after }

def active (p : ServerState C) : Config := active_config p.log C.initial

def eligibleVotes (s : GlobalState C) (n : NodeId) : Finset NodeId :=
  votesFor s.received (s.servers n).currentTerm n ∩ (active (s.servers n)).members

/-- Stable new may only be appended once the joint entry is locally committed.
    Replaying commands does not change the configuration. -/
def mayAppend (p : ServerState C) : EntryPayload → Prop
  | .command _ => True
  | .config cfg =>
      (active p = C.initial ∧ cfg = C.jointConfig ∧
        ∀ e ∈ p.log, ∀ prior, e.payload ≠ .config prior) ∨
      (active p = C.jointConfig ∧ cfg = C.finalConfig ∧
        ∃ e ∈ p.log.take p.commitIndex, e.payload = .config C.jointConfig)

def becomeLeader (s : GlobalState C) (n : NodeId) : GlobalState C :=
  let p := s.servers n
  let s' := setServer s n { p with role := .leader, matchIndex := fun _ => 0 }
  { s' with elected := insert (p.currentTerm, n, active p) s.elected }

def leaderAppend (s : GlobalState C) (n : NodeId) (cmd : EntryPayload) : GlobalState C :=
  let p := s.servers n
  let e : LogEntry := ⟨p.log.length + 1, p.currentTerm, cmd⟩
  let s' := setServer s n { p with log := p.log ++ [e] }
  let messages := broadcast n (.appendEntries p.currentTerm n p.log.length
    (termAt p.log p.log.length) [e] p.commitIndex)
  { s' with network := s.network ++ messages }

def handleAppend (s : GlobalState C) (v leader : NodeId)
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

def denyAppend (s : GlobalState C) (v leader : NodeId) (t : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  let p := s.servers v
  let s' := setServer s v
    { p with role := if t = p.currentTerm then .follower else p.role }
  { s' with network := before ++ after ++
      [⟨leader, .appendEntriesReply p.currentTerm false 0 v⟩] }

def receiveAppendReply (s : GlobalState C) (leader v : NodeId) (matched : ℕ)
    (before after : List (Envelope C)) : GlobalState C :=
  let p := s.servers leader
  let s' := setServer s leader
    { p with matchIndex := Function.update p.matchIndex v (max (p.matchIndex v) matched) }
  { s' with network := before ++ after }

def commitLeader (s : GlobalState C) (n : NodeId) (i : ℕ) : GlobalState C :=
  let p := s.servers n
  let c := max p.commitIndex i
  let retire := n ∉ C.newMembers ∧ ∃ e ∈ p.log.take c, e.payload = .config C.finalConfig
  setServer s n { p with commitIndex := c, role := if retire then .follower else p.role }

def replicationQuorum (s : GlobalState C) (leader : NodeId) (i : ℕ) : Finset (NodeId) :=
  ((active (s.servers leader)).members).filter
    (fun v => v = leader ∨ i ≤ (s.servers leader).matchIndex v)

/-- Operational rules. Guards are local Raft tests, never desired global invariants. -/
inductive Step : GlobalState C → GlobalState C → Prop where
  | observe {s : GlobalState C} {m : Envelope C} : m ∈ s.network →
      (s.servers m.destination).currentTerm < rpcTerm m.body →
      Step s (observeTerm s m.destination (rpcTerm m.body))
  | timeout (s : GlobalState C) (n : NodeId) :
      (s.servers n).role ≠ .leader → n ∈ (active (s.servers n)).members →
      Step s (startElection s n)
  | vote {s : GlobalState C} {v c : NodeId} {t li lt : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .requestVote t c li lt⟩ :: after →
      t = (s.servers v).currentTerm → mayVote (s.servers v) c li lt →
      Step s (grantVote s v c before after)
  | voteReply {s : GlobalState C} {v c : NodeId} {t : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨c, .requestVoteReply t true v⟩ :: after →
      t = (s.servers c).currentTerm → (s.servers c).role = .candidate →
      Step s (receiveVote s v c t before after)
  | elect {s : GlobalState C} {n : NodeId} :
      (s.servers n).role = .candidate →
      has_quorum (eligibleVotes s n) (active (s.servers n)) →
      Step s (becomeLeader s n)
  | append {s : GlobalState C} {n : NodeId} (cmd : EntryPayload) :
      (s.servers n).role = .leader → mayAppend (s.servers n) cmd →
      Step s (leaderAppend s n cmd)
  | commit {s : GlobalState C} {n : NodeId} (i : ℕ) :
      (s.servers n).role = .leader → i ≤ (s.servers n).log.length →
      termAt (s.servers n).log i = (s.servers n).currentTerm →
      has_quorum (replicationQuorum s n i) (active (s.servers n)) → Step s (commitLeader s n i)
  | replicate {s : GlobalState C} {n v : NodeId} (prev count : ℕ) :
      (s.servers n).role = .leader → n ≠ v → prev ≤ (s.servers n).log.length →
      Step s { s with network := s.network ++ [⟨v,
        .appendEntries (s.servers n).currentTerm n prev (termAt (s.servers n).log prev)
          (((s.servers n).log.drop prev).take count) (s.servers n).commitIndex⟩] }
  | appendEntries {s : GlobalState C} {v leader : NodeId} {t prev pt lc : ℕ}
      {entries : List LogEntry} {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after →
      t = (s.servers v).currentTerm → prevMatches (s.servers v).log prev pt →
      Step s (handleAppend s v leader prev entries lc before after)
  | appendReply {s : GlobalState C} {leader v : NodeId} {t matched : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨leader, .appendEntriesReply t true matched v⟩ :: after →
      t = (s.servers leader).currentTerm → (s.servers leader).role = .leader →
      Step s (receiveAppendReply s leader v matched before after)
  | rejectVote {s : GlobalState C} {v c : NodeId} {t li lt : ℕ}
      {before after : List (Envelope C)} :
      s.network = before ++ ⟨v, .requestVote t c li lt⟩ :: after →
      t ≤ (s.servers v).currentTerm →
      (t < (s.servers v).currentTerm ∨ ¬ mayVote (s.servers v) c li lt) →
      Step s { s with network := before ++ after ++
        [⟨c, .requestVoteReply (s.servers v).currentTerm false v⟩] }
  | rejectAppend {s : GlobalState C} {v leader : NodeId} {t prev pt lc : ℕ}
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
    (n : NodeId) (p : ServerState C)
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
    (v c : NodeId) (hv : (s.servers v).votedFor = some c) :
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
  | timeout n _ _ =>
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
    (t : ℕ) (v a b : NodeId) (ha : (t, v, a) ∈ s.cast) (hb : (t, v, b) ∈ s.cast) :
    a = b := (vote_history_reachable h).unique t v a b ha hb

theorem term_step_monotone {s s' : GlobalState C} (h : Step s s') (n : NodeId) :
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

theorem replyVotes_map (nodes : List (NodeId)) (body : NetworkMessage C)
    (h : ∀ t v, body ≠ .requestVoteReply t true v) :
    replyVotes (nodes.map (fun n => ⟨n, body⟩)) = ∅ := by
  induction nodes with
  | nil => rfl
  | cons n ns ih =>
    cases body <;> simp [replyVotes, ih]

theorem replyVotes_broadcast (n : NodeId) (body : NetworkMessage C)
    (h : ∀ t v, body ≠ .requestVoteReply t true v) :
    replyVotes (broadcast n body) = ∅ := replyVotes_map _ body h

@[simp] theorem replyVotes_requestBroadcast (n c : NodeId) (t li lt : ℕ) :
    replyVotes (broadcast (C := C) n (.requestVote t c li lt)) = ∅ :=
  replyVotes_broadcast n _ (by intros; intro he; cases he)

@[simp] theorem replyVotes_appendBroadcast (n leader : NodeId) (t pi pt lc : ℕ)
    (entries : List LogEntry) :
    replyVotes (broadcast (C := C) n (.appendEntries t leader pi pt entries lc)) = ∅ :=
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
    | timeout n _ _ =>
      simpa [startElection] using oldNetwork
    | @vote v c t li lt before after he _ _ =>
      have rem := (h.remainder he).trans grow
      simpa [grantVote, replyVotes] using
        (Finset.insert_subset (Finset.mem_insert_self ((s.servers v).currentTerm, v, c) s.cast) rem)
    | voteReply he _ _ => exact (h.remainder he).trans grow
    | elect => exact oldNetwork
    | append cmd _ _ =>
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
    | timeout n _ _ =>
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


/-- Both majorities are measured inside the same configuration. -/
theorem majority_overlap {A B C : Finset NodeId}
    (ha : C.card < 2 * (A ∩ C).card) (hb : C.card < 2 * (B ∩ C).card) :
    (A ∩ B ∩ C).Nonempty := by
  have hit : ((A ∩ C) ∩ (B ∩ C)).Nonempty :=
    Finset.inter_nonempty_of_card_lt_card_add_card
      (Finset.inter_subset_right) (Finset.inter_subset_right) (by omega)
  obtain ⟨v, hv⟩ := hit
  simp only [Finset.mem_inter] at hv
  exact ⟨v, Finset.mem_inter.mpr ⟨Finset.mem_inter.mpr ⟨hv.1.1, hv.2.1⟩, hv.1.2⟩⟩

theorem quorum_intersection_stable_joint {Q₁ Q₂ A B : Finset NodeId}
    (h₁ : is_stable_quorum Q₁ A) (h₂ : is_joint_quorum Q₂ A B) :
    (Q₁ ∩ Q₂).Nonempty := by
  obtain ⟨v, hv⟩ := majority_overlap h₁.2 h₂.1
  exact ⟨v, (Finset.mem_inter.mp hv).1⟩

theorem quorum_intersection_joint_new {Q₁ Q₂ A B : Finset NodeId}
    (h₁ : is_joint_quorum Q₁ A B) (h₂ : is_stable_quorum Q₂ B) :
    (Q₁ ∩ Q₂).Nonempty := by
  obtain ⟨v, hv⟩ := majority_overlap h₁.2 h₂.2
  exact ⟨v, (Finset.mem_inter.mp hv).1⟩

theorem quorum_intersection_joint_joint {Q₁ Q₂ A B : Finset NodeId}
    (h₁ : is_joint_quorum Q₁ A B) (h₂ : is_joint_quorum Q₂ A B) :
    (Q₁ ∩ Q₂ ∩ A).Nonempty ∧ (Q₁ ∩ Q₂ ∩ B).Nonempty :=
  ⟨majority_overlap h₁.1 h₂.1, majority_overlap h₁.2 h₂.2⟩

theorem quorum_intersection_same {Q₁ Q₂ : Finset NodeId} {cfg : Config}
    (h₁ : has_quorum Q₁ cfg) (h₂ : has_quorum Q₂ cfg) : (Q₁ ∩ Q₂).Nonempty := by
  cases cfg with
  | stable c =>
    obtain ⟨v, hv⟩ := majority_overlap h₁.2 h₂.2
    exact ⟨v, (Finset.mem_inter.mp hv).1⟩
  | joint a b =>
    obtain ⟨v, hv⟩ := (quorum_intersection_joint_joint h₁ h₂).1
    exact ⟨v, (Finset.mem_inter.mp hv).1⟩

theorem counterexample_direct_switch_disjoint :
    is_stable_quorum {0} {0} ∧ is_stable_quorum {1} {1} ∧
    ({0} ∩ {1} : Finset NodeId) = ∅ := by decide

/-- No node needs to cast two votes in this unsafe direct-switch example. -/
theorem direct_switch_split_vote :
    let votes : NodeId → Option NodeId := fun v => if v = 0 then some 0 else some 1
    (∀ v ∈ ({0} : Finset NodeId), votes v = some 0) ∧
    (∀ v ∈ ({1} : Finset NodeId), votes v = some 1) ∧ (0 : NodeId) ≠ 1 := by
  simp

/-- Intersecting certificates plus operational single voting suffice for uniqueness.
This is conditional: compatibility of old/new election certificates is not assumed
by the operational model; the completed reachability proof appears below. -/
theorem election_unique_of_intersection {s : GlobalState C} (hr : Reachable s)
    {t a b : ℕ} {Q₁ Q₂ : Finset NodeId}
    (ha : ∀ v ∈ Q₁, (t, v, a) ∈ s.cast)
    (hb : ∀ v ∈ Q₂, (t, v, b) ∈ s.cast)
    (hit : (Q₁ ∩ Q₂).Nonempty) : a = b := by
  obtain ⟨v, hv⟩ := hit
  exact single_vote_preserved hr t v a b
    (ha v (Finset.mem_inter.mp hv).1) (hb v (Finset.mem_inter.mp hv).2)

/-- All votes of two same-configuration election certificates name one candidate. -/
theorem election_unique_same_config {s : GlobalState C} (hr : Reachable s)
    {t a b : ℕ} {Q₁ Q₂ : Finset NodeId} {cfg : Config}
    (ha : ∀ v ∈ Q₁, (t, v, a) ∈ s.cast)
    (hb : ∀ v ∈ Q₂, (t, v, b) ∈ s.cast)
    (hq₁ : has_quorum Q₁ cfg) (hq₂ : has_quorum Q₂ cfg) : a = b :=
  election_unique_of_intersection hr ha hb (quorum_intersection_same hq₁ hq₂)

/-- Each historical election has an actual configuration and a set of authentic votes. -/
def ElectionsSound (s : GlobalState C) : Prop :=
  ∀ t c cfg, (t, c, cfg) ∈ s.elected → ∃ Q : Finset NodeId,
    has_quorum Q cfg ∧ ∀ v ∈ Q, (t, v, c) ∈ s.cast

theorem elections_step {s s' : GlobalState C} (h : ElectionsSound s)
    (ht : TransportSound s) (step : Step s s') : ElectionsSound s' := by
  have grow := cast_step_monotone step
  have old : ∀ t c cfg, (t, c, cfg) ∈ s.elected → ∃ Q : Finset NodeId,
      has_quorum Q cfg ∧ ∀ v ∈ Q, (t, v, c) ∈ s'.cast := by
    intro t c cfg he
    obtain ⟨Q, hq, hv⟩ := h t c cfg he
    exact ⟨Q, hq, fun v hm => grow (hv v hm)⟩
  cases step with
  | @elect n _ hq =>
    intro t c cfg hc
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hc
    rcases hc with ⟨rfl, rfl, rfl⟩ | hc
    · refine ⟨_, hq, ?_⟩
      intro v hv
      exact ht.received ((mem_votesFor _ _ _ _).mp (Finset.mem_inter.mp hv).1)
    · exact old _ _ _ hc
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

theorem elections_reachable {s : GlobalState C} (h : Reachable s) : ElectionsSound s := by
  induction h with
  | init => simp [ElectionsSound, initState]
  | step reach step ih => exact elections_step ih (transport_reachable reach) step

/-- Historical safety when the two successful elections used the same configuration.
The mixed stable-old/stable-new case is deliberately not asserted here. -/
theorem same_configuration_election_safety {s : GlobalState C} (hr : Reachable s)
    {t a b : ℕ} {cfg : Config} (ha : (t, a, cfg) ∈ s.elected)
    (hb : (t, b, cfg) ∈ s.elected) : a = b := by
  obtain ⟨Q₁, hq₁, hv₁⟩ := elections_reachable hr t a cfg ha
  obtain ⟨Q₂, hq₂, hv₂⟩ := elections_reachable hr t b cfg hb
  exact election_unique_same_config hr hv₁ hv₂ hq₁ hq₂

theorem old_joint_election_safety {s : GlobalState C} (hr : Reachable s)
    {t a b : ℕ} (ha : (t, a, C.initial) ∈ s.elected)
    (hb : (t, b, C.jointConfig) ∈ s.elected) : a = b := by
  obtain ⟨Q₁, hq₁, hv₁⟩ := elections_reachable hr t a C.initial ha
  obtain ⟨Q₂, hq₂, hv₂⟩ := elections_reachable hr t b C.jointConfig hb
  exact election_unique_of_intersection hr hv₁ hv₂
    (quorum_intersection_stable_joint hq₁ hq₂)

theorem joint_new_election_safety {s : GlobalState C} (hr : Reachable s)
    {t a b : ℕ} (ha : (t, a, C.jointConfig) ∈ s.elected)
    (hb : (t, b, C.finalConfig) ∈ s.elected) : a = b := by
  obtain ⟨Q₁, hq₁, hv₁⟩ := elections_reachable hr t a C.jointConfig ha
  obtain ⟨Q₂, hq₂, hv₂⟩ := elections_reachable hr t b C.finalConfig hb
  exact election_unique_of_intersection hr hv₁ hv₂
    (quorum_intersection_joint_new hq₁ hq₂)

/-- A newly appended joint entry activates before commitIndex changes. -/
theorem joint_activates_before_commit (s : GlobalState C) (n : NodeId) :
    active ((leaderAppend s n (.config C.jointConfig)).servers n) = C.jointConfig ∧
    ((leaderAppend s n (.config C.jointConfig)).servers n).commitIndex =
      (s.servers n).commitIndex := by
  simp [leaderAppend, setServer, active]

/-- Heartbeats do not discard a locally newer configuration suffix. -/
theorem heartbeat_preserves_config (log : List LogEntry) (prev : ℕ) (cfg : Config) :
    active_config (appendEntriesLog log prev []) cfg = active_config log cfg := by simp

/-- Local retirement uses the committed prefix, not mere receipt of a new configuration. -/
theorem excluded_leader_retires (s : GlobalState C) (n i : ℕ)
    (hn : n ∉ C.newMembers)
    (hc : ∃ e ∈ (s.servers n).log.take (max (s.servers n).commitIndex i),
      e.payload = .config C.finalConfig) :
    ((commitLeader s n i).servers n).role = .follower := by
  simp [commitLeader, setServer, hn, hc]

/-- Loss may discard an arbitrary suffix, without changing any server or evidence. -/
theorem reachable_drop_suffix (s : GlobalState C) (pre tail : List (Envelope C))
    (h : Reachable { s with network := pre ++ tail }) :
    Reachable { s with network := pre } := by
  induction tail with
  | nil => simpa using h
  | cons m ms ih =>
    apply ih
    exact h.step (Step.drop (before := pre) (after := ms) (m := m) rfl)

theorem reachable_drop_prefix (s : GlobalState C) (pre tail : List (Envelope C))
    (h : Reachable { s with network := pre ++ tail }) :
    Reachable { s with network := tail } := by
  induction pre with
  | nil => exact h
  | cons m ms ih =>
    apply ih
    exact h.step (Step.drop (before := []) (after := ms ++ tail) (m := m) rfl)

/-- Keep a real queued packet and drop all others. No new packet is injected. -/
theorem reachable_isolate {s : GlobalState C} (h : Reachable s) {m : Envelope C}
    (hm : m ∈ s.network) : Reachable { s with network := [m] } := by
  obtain ⟨pre, tail, he⟩ := List.mem_iff_append.mp hm
  have hsplit : Reachable { s with network := pre ++ m :: tail } := by simpa [← he] using h
  have hhead := reachable_drop_prefix s pre (m :: tail) hsplit
  exact reachable_drop_suffix s [m] tail hhead

/-- Broadcast enumerates exactly the ambient nodes other than the sender. -/
theorem mem_broadcast (sender dst : NodeId) (body : NetworkMessage C)
    (hdst : dst ∈ C.nodes) (hne : dst ≠ sender) : ⟨dst, body⟩ ∈ broadcast sender body := by
  simp [broadcast, hdst, hne]

/-- Inject command-only fixed-cluster entries, preserving both voting fields. -/
def ofFixedEntry (e : DistributedRaftLeaderCompleteness.LogEntry) : LogEntry :=
  ⟨e.index, e.term, .command e.cmd⟩

/-- Exact compatibility of conflict-sensitive merge on command-only logs.
This is a local operation bridge, not a simulation of the entire automaton. -/
theorem fixed_cluster_command_merge_bridge
    (a b : List DistributedRaftLeaderCompleteness.LogEntry) :
    mergeSuffix (a.map ofFixedEntry) (b.map ofFixedEntry) =
      (DistributedRaftStateMachine.mergeSuffix a b).map ofFixedEntry := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons x xs ih =>
    cases b with
    | nil => rfl
    | cons y ys =>
      simp only [List.map_cons, mergeSuffix, ofFixedEntry,
        DistributedRaftStateMachine.mergeSuffix]
      split_ifs <;> simp_all [ofFixedEntry]

theorem fixed_cluster_append_entries_bridge
    (a b : List DistributedRaftLeaderCompleteness.LogEntry) (prev : ℕ) :
    appendEntriesLog (a.map ofFixedEntry) prev (b.map ofFixedEntry) =
      (DistributedRaftStateMachine.appendEntriesLog a prev b).map ofFixedEntry := by
  simp only [appendEntriesLog, DistributedRaftStateMachine.appendEntriesLog,
    ← List.map_take, ← List.map_drop, fixed_cluster_command_merge_bridge, List.map_append]

/-- Empty/command-only fixed-cluster logs retain the initial configuration. -/
theorem fixed_cluster_command_config
    (a : List DistributedRaftLeaderCompleteness.LogEntry) (cfg : Config) :
    active_config (a.map ofFixedEntry) cfg = cfg := by
  induction a generalizing cfg with
  | nil => rfl
  | cons e es ih => exact ih cfg

/-- Decoding is lossless for embedded command entries. -/
theorem fixed_entry_embedding_injective : Function.Injective ofFixedEntry := by
  intro a b h
  cases a; cases b
  cases h
  rfl

namespace Examples

def disjoint : Transition := ⟨{0}, {1}, by simp, by simp⟩
@[simp] theorem broadcast_zero (body : NetworkMessage disjoint) :
    broadcast 0 body = [⟨1, body⟩] := by
  have hn : disjoint.nodes = Finset.range 2 := by decide
  simp only [broadcast, hn, Finset.sort_range]
  rfl

def jointEntry : LogEntry := ⟨1, 1, .config disjoint.jointConfig⟩
def newEntry : LogEntry := ⟨2, 1, .config disjoint.finalConfig⟩

def s₀ : GlobalState disjoint := initState disjoint
def s₁ := startElection s₀ 0
def s₂ := becomeLeader s₁ 0
def s₃ := consume s₂ [] []
def s₄ := leaderAppend s₃ 0 (.config disjoint.jointConfig)
def s₅ := observeTerm s₄ 1 1
def s₆ := handleAppend s₅ 1 0 0 [jointEntry] 0 [] []
def s₇ := receiveAppendReply s₆ 0 1 1 [] []
def s₈ := commitLeader s₇ 0 1
def s₉ := leaderAppend s₈ 0 (.config disjoint.finalConfig)
def s₁₀ := handleAppend s₉ 1 0 1 [newEntry] 1 [] []
def s₁₁ := receiveAppendReply s₁₀ 0 1 2 [] []
def s₁₂ := commitLeader s₁₁ 0 2

theorem reach₀ : Reachable s₀ := .init

theorem reach₁ : Reachable s₁ :=
  .step reach₀ (.timeout s₀ 0 (by decide) (by decide))

theorem reach₂ : Reachable s₂ :=
  .step reach₁ (.elect (by decide) (by decide))

theorem reach₃ : Reachable s₃ :=
  .step reach₂ (.drop (m := ⟨1, .requestVote 1 0 0 0⟩) (by
    simp [s₂, s₁, s₀, becomeLeader, startElection, initState, setServer, lastIndex, lastTerm]))

theorem reach₄ : Reachable s₄ :=
  .step reach₃ (.append _ (by decide) (by
    left; exact ⟨by decide, rfl, by simp [s₃, s₂, s₁, s₀, consume, becomeLeader,
      startElection, initState, setServer]⟩))

theorem reach₅ : Reachable s₅ :=
  .step reach₄ (.observe
    (m := ⟨1, .appendEntries 1 0 0 0 [jointEntry] 0⟩) (by
      simp [s₄, s₃, s₂, s₁, s₀, leaderAppend, consume, becomeLeader, startElection,
        initState, setServer, termAt, jointEntry]) (by decide))

theorem reach₆ : Reachable s₆ :=
  .step reach₅ (.appendEntries (t := 1) (pt := 0) (by
    simp [s₅, s₄, s₃, s₂, s₁, s₀, observeTerm, leaderAppend, consume, becomeLeader,
      startElection, initState, setServer, termAt, jointEntry]) (by decide) (by decide))

theorem reach₇ : Reachable s₇ :=
  .step reach₆ (.appendReply (t := 1) (by decide) (by decide) (by decide))

theorem reach₈ : Reachable s₈ :=
  .step reach₇ (.commit 1 (by decide) (by decide) (by decide) (by decide))

theorem reach₉ : Reachable s₉ :=
  .step reach₈ (.append _ (by decide) (by
    right; exact ⟨by decide, rfl, jointEntry, by decide, rfl⟩))

theorem reach₁₀ : Reachable s₁₀ :=
  .step reach₉ (.appendEntries (t := 1) (pt := 1) (by
    simp only [s₉, leaderAppend, setServer, broadcast_zero]
    decide) (by decide) (by decide))

theorem reach₁₁ : Reachable s₁₁ :=
  .step reach₁₀ (.appendReply (t := 1) (by decide) (by decide) (by decide))

theorem reach₁₂ : Reachable s₁₂ :=
  .step reach₁₁ (.commit 2 (by decide) (by decide) (by decide) (by decide))

/-- A concrete successful transition; the two membership sets share no node. -/
theorem disjoint_transition_and_retirement :
    Reachable s₁₂ ∧ disjoint.oldMembers ∩ disjoint.newMembers = ∅ ∧
    (s₁₂.servers 0).commitIndex = 2 ∧ (s₁₂.servers 0).role = .follower ∧
    active (s₁₂.servers 0) = disjoint.finalConfig ∧
    active (s₁₂.servers 1) = disjoint.finalConfig := ⟨reach₁₂, by decide⟩

/-- A joint configuration is already active while its entry is uncommitted. -/
theorem local_uncommitted_activation :
    active (s₄.servers 0) = disjoint.jointConfig ∧ (s₄.servers 0).commitIndex = 0 := by
  decide

/-- New-only configuration cannot be appended before joint commitment. -/
theorem new_before_joint_commit_rejected :
    ¬ mayAppend (s₄.servers 0) (.config disjoint.finalConfig) := by
  simp [mayAppend, s₄, s₃, s₂, s₁, s₀, leaderAppend, consume, becomeLeader,
    startElection, initState, setServer, active, disjoint,
    Transition.initial, Transition.jointConfig, Transition.finalConfig]

/-- One-node stable quorum really elects a reachable leader. -/
theorem singleton_election : Reachable s₂ ∧ (s₂.servers 0).role = .leader :=
  ⟨reach₂, by decide⟩

/-- Replacing the conflicting uncommitted entry restores the preceding configuration. -/
theorem conflicting_suffix_restores_old :
    active_config (appendEntriesLog [jointEntry] 0 [⟨1, 2, .command 9⟩])
      disjoint.initial = disjoint.initial := by decide


/-- The new singleton can campaign and elect its own leader in the next term. -/
def s₁₃ := startElection s₁₂ 1
def s₁₄ := becomeLeader s₁₃ 1

theorem reach₁₃ : Reachable s₁₃ :=
  .step reach₁₂ (.timeout _ _ (by decide) (by decide))
theorem reach₁₄ : Reachable s₁₄ := .step reach₁₃ (.elect (by decide) (by decide))

theorem new_leader_after_disjoint_handover : Reachable s₁₄ ∧
    (s₁₄.servers 1).role = .leader ∧ (s₁₄.servers 1).currentTerm = 2 ∧
    active (s₁₄.servers 1) = disjoint.finalConfig := ⟨reach₁₄, by decide⟩

end Examples

namespace RollbackExample

def cfg : Transition := ⟨{0, 1, 2}, {3}, by simp, by simp⟩
def jointEntry : LogEntry := ⟨1, 1, .config cfg.jointConfig⟩
def replacement : LogEntry := ⟨1, 2, .command 9⟩
def request₁ : Envelope cfg := ⟨1, .requestVote 1 0 0 0⟩
def request₂ : Envelope cfg := ⟨2, .requestVote 2 1 0 0⟩
def packet : Envelope cfg := ⟨0, .appendEntries 2 1 0 0 [replacement] 0⟩

def r₀ : GlobalState cfg := initState cfg
def r₁ := startElection r₀ 0
def r₂ : GlobalState cfg := { r₁ with network := [request₁] }
def r₃ := observeTerm r₂ 1 1
def r₄ := grantVote r₃ 1 0 [] []
def r₅ := receiveVote r₄ 1 0 1 [] []
def r₆ := becomeLeader r₅ 0
def r₇ := leaderAppend r₆ 0 (.config cfg.jointConfig)
def r₈ := startElection r₇ 1
def r₉ : GlobalState cfg := { r₈ with network := [request₂] }
def r₁₀ := observeTerm r₉ 2 2
def r₁₁ := grantVote r₁₀ 2 1 [] []
def r₁₂ := receiveVote r₁₁ 2 1 2 [] []
def r₁₃ := becomeLeader r₁₂ 1
def r₁₄ := leaderAppend r₁₃ 1 (.command 9)
def r₁₅ : GlobalState cfg := { r₁₄ with network := [packet] }
def r₁₆ := observeTerm r₁₅ 0 2
def r₁₇ := handleAppend r₁₆ 0 1 0 [replacement] 0 [] []

theorem reach₀ : Reachable r₀ := .init
theorem reach₁ : Reachable r₁ := .step reach₀ (.timeout _ _ (by decide) (by decide))
theorem reach₂ : Reachable r₂ := by
  apply reachable_isolate reach₁
  change request₁ ∈ [] ++ broadcast 0 (.requestVote 1 0 0 0)
  exact List.mem_append_right _ (mem_broadcast 0 1 _ (by decide) (by decide))
theorem reach₃ : Reachable r₃ :=
  .step reach₂ (.observe (m := request₁) (by decide) (by decide))
theorem reach₄ : Reachable r₄ :=
  .step reach₃ (.vote (t := 1) (li := 0) (lt := 0) (by decide) (by decide)
    ⟨Or.inl (by decide), Or.inr ⟨by decide, by decide⟩⟩)
theorem reach₅ : Reachable r₅ :=
  .step reach₄ (.voteReply (by decide) (by decide) (by decide))
theorem reach₆ : Reachable r₆ := .step reach₅ (.elect (by decide) (by decide))
theorem reach₇ : Reachable r₇ :=
  .step reach₆ (.append _ (by decide) (by
    left; exact ⟨by decide, rfl, by simp [r₆, r₅, r₄, r₃, r₂, r₁, r₀,
      becomeLeader, receiveVote, grantVote, observeTerm, startElection, initState, setServer]⟩))
theorem reach₈ : Reachable r₈ := .step reach₇ (.timeout _ _ (by decide) (by decide))
theorem reach₉ : Reachable r₉ := by
  apply reachable_isolate reach₈
  change request₂ ∈ r₇.network ++ broadcast 1 (.requestVote 2 1 0 0)
  exact List.mem_append_right _ (mem_broadcast 1 2 _ (by decide) (by decide))
theorem reach₁₀ : Reachable r₁₀ :=
  .step reach₉ (.observe (m := request₂) (by decide) (by decide))
theorem reach₁₁ : Reachable r₁₁ :=
  .step reach₁₀ (.vote (t := 2) (li := 0) (lt := 0) (by decide) (by decide)
    ⟨Or.inl (by decide), Or.inr ⟨by decide, by decide⟩⟩)
theorem reach₁₂ : Reachable r₁₂ :=
  .step reach₁₁ (.voteReply (by decide) (by decide) (by decide))
theorem reach₁₃ : Reachable r₁₃ := .step reach₁₂ (.elect (by decide) (by decide))
theorem reach₁₄ : Reachable r₁₄ := .step reach₁₃ (.append _ (by decide) True.intro)
theorem reach₁₅ : Reachable r₁₅ := by
  apply reachable_isolate reach₁₄
  change packet ∈ r₁₃.network ++ broadcast 1 (.appendEntries 2 1 0 0 [replacement] 0)
  exact List.mem_append_right _ (mem_broadcast 1 0 _ (by decide) (by decide))
theorem reach₁₆ : Reachable r₁₆ :=
  .step reach₁₅ (.observe (m := packet) (by decide) (by decide))
theorem reach₁₇ : Reachable r₁₇ :=
  .step reach₁₆ (.appendEntries (t := 2) (pt := 0) (by decide) (by decide) (by decide))

/-- A leader lacking the uncommitted joint entry wins in the next term and
replaces that entry. The old leader activates stable-old again on delivery. -/
theorem leader_change_rolls_back_uncommitted_joint :
    Reachable r₇ ∧ Reachable r₁₇ ∧
    active (r₇.servers 0) = cfg.jointConfig ∧ (r₇.servers 0).commitIndex = 0 ∧
    (r₁₇.servers 1).role = .leader ∧ (r₁₇.servers 1).currentTerm = 2 ∧
    (r₁₇.servers 0).role = .follower ∧ (r₁₇.servers 0).log = [replacement] ∧
    active (r₁₇.servers 0) = cfg.initial := ⟨reach₇, reach₁₇, by decide⟩

end RollbackExample


/-- Removing a delivered packet preserves membership of the remaining packets. -/
theorem packet_remainder {s : GlobalState C} {before after : List (Envelope C)}
    {removed m : Envelope C} (h : s.network = before ++ removed :: after)
    (hm : m ∈ before ++ after) : m ∈ s.network := by
  rw [h]
  simp only [List.mem_append, List.mem_cons] at hm ⊢
  tauto

theorem termAt_prefix {a b : List LogEntry} (hp : a.IsPrefix b)
    (i : ℕ) (hi : i ≤ a.length) : termAt a i = termAt b i := by
  by_cases hz : i = 0
  · simp [termAt, hz]
  obtain ⟨suffix, rfl⟩ := hp
  simp only [termAt]
  rw [List.getElem?_append_left (by omega : i - 1 < a.length)]

theorem mergeSuffix_mem {e : LogEntry} {a b : List LogEntry}
    (h : e ∈ mergeSuffix a b) : e ∈ a ∨ e ∈ b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => simp [mergeSuffix] at h
    | cons x xs => exact Or.inr h
  | cons x xs ih =>
    cases b with
    | nil => exact Or.inl h
    | cons y ys =>
      simp only [mergeSuffix] at h
      split_ifs at h with ht
      · rcases List.mem_cons.mp h with he | he
        · exact Or.inl (List.mem_cons.mpr (Or.inl he))
        · rcases ih he with ha | hb
          · exact Or.inl (List.mem_cons_of_mem _ ha)
          · exact Or.inr (List.mem_cons_of_mem _ hb)
      · exact Or.inr h

theorem appendEntriesLog_mem {e : LogEntry} {a b : List LogEntry} {prev : ℕ}
    (h : e ∈ appendEntriesLog a prev b) : e ∈ a ∨ e ∈ b := by
  rcases List.mem_append.mp h with ha | hb
  · exact Or.inl (List.mem_of_mem_take ha)
  · rcases mergeSuffix_mem hb with ha | hb
    · exact Or.inl (List.mem_of_mem_drop ha)
    · exact Or.inr hb

structure Execution (C : Transition) where
  length : ℕ
  state : ℕ → GlobalState C
  initial : state 0 = initState C
  transition : ∀ i, i < length → Step (state i) (state (i + 1))


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
def RequestWitness (run : Execution C) (k t : ℕ) (c : NodeId) (li lt : ℕ) : Prop :=
  ∃ i, i < k ∧ ((run.state i).servers c).role ≠ .leader ∧
    t = ((run.state i).servers c).currentTerm + 1 ∧
    li = lastIndex ((run.state i).servers c).log ∧
    lt = lastTerm ((run.state i).servers c).log ∧
    run.state (i + 1) = startElection (run.state i) c

/-- Positive acknowledgments are generated only by actual successful deliveries. -/
def AckWitness (run : Execution C) (k t : ℕ) (leader v : NodeId) (matched : ℕ) : Prop :=
  ∃ i prev pt entries lc before after, i < k ∧
    (run.state i).network = before ++ ⟨v, .appendEntries t leader prev pt entries lc⟩ :: after ∧
    t = ((run.state i).servers v).currentTerm ∧
    prevMatches ((run.state i).servers v).log prev pt ∧
    matched = prev + entries.length ∧
    run.state (i + 1) = handleAppend (run.state i) v leader prev entries lc before after

theorem RequestWitness.mono {run : Execution C} {k k' t : ℕ} {c : NodeId} {li lt : ℕ}
    (h : RequestWitness run k t c li lt) (hk : k ≤ k') : RequestWitness run k' t c li lt := by
  obtain ⟨i, hi, rest⟩ := h
  exact ⟨i, by omega, rest⟩

theorem AckWitness.mono {run : Execution C} {k k' t : ℕ} {c v : NodeId} {matched : ℕ}
    (h : AckWitness run k t c v matched) (hk : k ≤ k') : AckWitness run k' t c v matched := by
  obtain ⟨i, prev, pt, entries, lc, before, after, hi, rest⟩ := h
  exact ⟨i, prev, pt, entries, lc, before, after, by omega, rest⟩

/-- The contiguous batch was sent from a leader snapshot in this same execution. -/
def AppendWitness (run : Execution C) (k t : ℕ) (leader : NodeId)
    (prev pt : ℕ) (entries : List LogEntry) (lc : ℕ) : Prop :=
  ∃ j count, j ≤ k ∧ ((run.state j).servers leader).role = .leader ∧
    ((run.state j).servers leader).currentTerm = t ∧
    prev ≤ ((run.state j).servers leader).log.length ∧
    pt = termAt ((run.state j).servers leader).log prev ∧
    entries = (((run.state j).servers leader).log.drop prev).take count ∧
    lc = ((run.state j).servers leader).commitIndex

theorem AppendWitness.mono {run : Execution C} {k k' t : ℕ} {leader : NodeId}
    {prev pt lc : ℕ} {entries : List LogEntry}
    (h : AppendWitness run k t leader prev pt entries lc) (hk : k ≤ k') :
    AppendWitness run k' t leader prev pt entries lc := by
  obtain ⟨j, count, hj, rest⟩ := h
  exact ⟨j, count, by omega, rest⟩

def PacketWitness (run : Execution C) (k : ℕ) (m : Envelope C) : Prop :=
  match m.body with
  | .requestVote t c li lt => RequestWitness run k t c li lt
  | .appendEntries t leader prev pt entries lc => AppendWitness run k t leader prev pt entries lc
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
  | timeout n hn _ =>
    simp only [startElection, List.mem_append] at hm
    rcases hm with hm | hm
    · exact old m hm
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
      exact ⟨k, by omega, hn, rfl, rfl, rfl, he⟩
  | @append leader cmd hn _ =>
    simp only [leaderAppend, List.mem_append] at hm
    rcases hm with hm | hm
    · exact old m hm
    · obtain ⟨v, _, rfl⟩ := List.mem_map.mp hm
      refine ⟨k + 1, 1, le_rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [he]; simp [leaderAppend, setServer, hn]
      · rw [he]; simp [leaderAppend, setServer]
      · rw [he]; simp [leaderAppend, setServer]
      · rw [he]
        simpa only [leaderAppend, setServer, Function.update_self] using
          termAt_prefix
            (List.prefix_append ((run.state k).servers leader).log
              [⟨((run.state k).servers leader).log.length + 1,
                ((run.state k).servers leader).currentTerm, cmd⟩]) _ le_rfl
      · rw [he]; simp [leaderAppend, setServer]
      · rw [he]; simp [leaderAppend, setServer]
  | @replicate leader v prev count hn hne hp =>
    simp only [List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · exact old m hm
    · exact ⟨k, count, by omega, hn, rfl, hp, rfl, rfl, rfl⟩
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


/-- The entry was created by one of this execution's actual client append steps. -/
def TraceGenerated (run : Execution C) (k : ℕ) (e : LogEntry) : Prop :=
  ∃ j, j < k ∧ ∃ owner cmd,
    ((run.state j).servers owner).role = .leader ∧
    mayAppend ((run.state j).servers owner) cmd ∧
    e = ⟨((run.state j).servers owner).log.length + 1,
      ((run.state j).servers owner).currentTerm, cmd⟩ ∧
    run.state (j + 1) = leaderAppend (run.state j) owner cmd

theorem TraceGenerated.mono {run : Execution C} {k k' : ℕ} {e : LogEntry}
    (h : TraceGenerated run k e) (hk : k ≤ k') : TraceGenerated run k' e := by
  obtain ⟨j, hj, rest⟩ := h
  exact ⟨j, by omega, rest⟩

/-- Every stored entry has an earlier creation event on this very trace. -/
theorem trace_generated (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (n : NodeId) (e : LogEntry) (he : e ∈ ((run.state k).servers n).log) :
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
      | @append owner cmd hl hg =>
        by_cases hn : n = owner
        · subst n
          simp only [leaderAppend, setServer, Function.update_self, List.mem_append,
            List.mem_singleton] at he
          rcases he with he | he
          · exact old owner he
          · exact ⟨k, by omega, owner, cmd, hl, hg, he, hnext⟩
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
            have hw : AppendWitness run k t leader prev pt entries lc :=
              network_witness run k (by omega) _ hpacket
            obtain ⟨j, count, hj, _hrole, _hterm, _hprev, _hpt, hentries, _hlc⟩ := hw
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
    (n : NodeId) (e : LogEntry) (he : e ∈ ((run.state k).servers n).log) :
    ∃ j, j ≤ k ∧ ∃ owner,
      ((run.state j).servers owner).role = .leader ∧
      ((run.state j).servers owner).currentTerm = e.term ∧
      e ∈ ((run.state j).servers owner).log := by
  obtain ⟨j, hj, owner, cmd, hr, _hg, heq, hnext⟩ := trace_generated run k hk n e he
  refine ⟨j+1, by omega, owner, ?_, ?_, ?_⟩
  all_goals rw [hnext]; simp [leaderAppend, setServer, hr, heq]


/-- Every persistent ballot is tied to its actual local vote event. -/
inductive VoteWitness (run : Execution C) (k t : ℕ) (v c : NodeId) : Prop where
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

theorem VoteWitness.mono {run : Execution C} {k k' t : ℕ} {v c : NodeId}
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
  | timeout n hn _ =>
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
    (t : ℕ) (v c : NodeId) (hm : (t, v, c) ∈ (run.state k).received) :
    VoteWitness run k t v c :=
  cast_witness run k hk t v c ((transport_reachable (run.reachable k hk)).received hm)

/-- A directly enabled commit step, including the actual local quorum test. -/
structure CommitEvent (run : Execution C) (k leader index : ℕ) : Prop where
  within : k < run.length
  leaderRole : ((run.state k).servers leader).role = .leader
  withinLog : index ≤ ((run.state k).servers leader).log.length
  currentTerm : termAt ((run.state k).servers leader).log index =
    ((run.state k).servers leader).currentTerm
  quorum : has_quorum (replicationQuorum (run.state k) leader index)
    (active ((run.state k).servers leader))
  next : run.state (k + 1) = commitLeader (run.state k) leader index

/-- Numeric provenance is weaker than committed-prefix preservation:
this conclusion identifies a real earlier commit covering the index, without
yet identifying the receiver's current prefix with the committed snapshot. -/
def CommitIndexWitness (run : Execution C) (k node index : ℕ) : Prop :=
  ∃ j owner bound, j < k ∧ CommitEvent run j owner bound ∧ index ≤ bound ∧
    ((run.state j).servers owner).currentTerm ≤ ((run.state k).servers node).currentTerm

theorem commit_index_history (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (node index : ℕ) (hp : 0 < index)
    (hi : index ≤ ((run.state k).servers node).commitIndex) :
    CommitIndexWitness run k node index := by
  induction k using Nat.strong_induction_on generalizing node with
  | h k ih =>
    cases k with
    | zero => rw [run.initial] at hi; simp [initState] at hi; omega
    | succ k =>
      have st := run.transition k (by omega)
      have mono := term_step_monotone st node
      have old : index ≤ ((run.state k).servers node).commitIndex →
          CommitIndexWitness run (k + 1) node index := by
        intro hindex
        obtain ⟨j, owner, bound, hj, hc, hb, ht⟩ :=
          ih k (by omega) (by omega) node hindex
        exact ⟨j, owner, bound, by omega, hc, hb, ht.trans mono⟩
      generalize he : run.state (k + 1) = next at st hi mono ⊢
      cases st with
      | @commit leader bound hrole hlen hterm hquorum =>
        by_cases hn : node = leader
        · subst node
          simp only [commitLeader, setServer, Function.update_self] at hi
          rcases le_max_iff.mp hi with hold | hbound
          · exact old hold
          · refine ⟨k, leader, bound, by omega,
              ⟨by omega, hrole, hlen, hterm, hquorum, he⟩, hbound, ?_⟩
            rw [he]; simp [commitLeader, setServer]
        · apply old
          simpa [commitLeader, setServer, Function.update_of_ne hn] using hi
      | @appendEntries v leader t prev pt lc entries before after hnet ht hprev =>
        by_cases hn : node = v
        · subst node
          simp only [handleAppend, setServer, Function.update_self] at hi
          rcases le_max_iff.mp hi with hold | hincoming
          · exact old hold
          · have packet : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈
                (run.state k).network := by rw [hnet]; simp
            obtain ⟨j, count, hj, _hrole, hjt, _hlen, _hpt, _hentries, hlc⟩ :=
              (network_witness run k (by omega) _ packet :
                AppendWitness run k t leader prev pt entries lc)
            have hindex : index ≤ ((run.state j).servers leader).commitIndex := by
              rw [← hlc]; exact (le_min_iff.mp hincoming).1
            obtain ⟨a, owner, bound, ha, hc, hb, hat⟩ :=
              ih j (by omega) (by omega) leader hindex
            refine ⟨a, owner, bound, by omega, hc, hb, ?_⟩
            rw [he]
            simpa only [handleAppend, setServer, Function.update_self, hjt, ht] using hat
        · apply old
          simpa [handleAppend, setServer, Function.update_of_ne hn] using hi
      | _ =>
        apply old
        simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
          leaderAppend, receiveAppendReply, denyAppend, consume, setServer,
          Function.update_apply] at hi
        (try split_ifs at hi) <;> simp_all

/-- An actual creation of stable-new has a joint entry in the creator's local
committed prefix. This is an origin theorem, not a global retention theorem. -/
theorem new_entry_has_local_joint_origin (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (node : ℕ) (e : LogEntry)
    (he : e ∈ ((run.state k).servers node).log) (hnew : e.payload = .config C.finalConfig) :
    ∃ j owner, j < k ∧ ((run.state j).servers owner).role = .leader ∧
      active ((run.state j).servers owner) = C.jointConfig ∧
      (∃ joint ∈ ((run.state j).servers owner).log.take
        ((run.state j).servers owner).commitIndex, joint.payload = .config C.jointConfig) ∧
      run.state (j + 1) = leaderAppend (run.state j) owner (.config C.finalConfig) := by
  obtain ⟨j, hj, owner, cmd, hrole, hguard, heq, hnext⟩ := trace_generated run k hk node e he
  have hcmd : cmd = .config C.finalConfig := by simpa [heq] using hnew
  subst cmd
  rcases hguard with ⟨_, heqcfg, _⟩ | ⟨hactive, _, hcommitted⟩
  · cases heqcfg
  · exact ⟨j, owner, hj, hrole, hactive, hcommitted, hnext⟩

/-- Stable-new creation has an earlier real commit event. Until global matching
is proved, this does not assert equality of that event's prefix with the current
local joint prefix, or that the earlier event used a joint quorum. -/
theorem new_entry_has_historical_commit (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (node : ℕ) (e : LogEntry)
    (he : e ∈ ((run.state k).servers node).log) (hnew : e.payload = .config C.finalConfig) :
    ∃ j owner a committer bound,
      a < j ∧ j < k ∧ CommitEvent run a committer bound ∧
      active ((run.state j).servers owner) = C.jointConfig ∧
      run.state (j + 1) = leaderAppend (run.state j) owner (.config C.finalConfig) := by
  obtain ⟨j, owner, hj, _hrole, hactive, ⟨joint, hmem, _hpayload⟩, hnext⟩ :=
    new_entry_has_local_joint_origin run k hk node e he hnew
  have hp : 0 < ((run.state j).servers owner).commitIndex := by
    by_contra h
    have hz : ((run.state j).servers owner).commitIndex = 0 := by omega
    simp [hz] at hmem
  obtain ⟨a, committer, bound, ha, hc, _hb, _ht⟩ :=
    commit_index_history run j (by omega) owner
      ((run.state j).servers owner).commitIndex hp le_rfl
  exact ⟨j, owner, a, committer, bound, ha, hj, hc, hactive, hnext⟩

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

theorem ServerBounds.observe {p : ServerState C} (h : ServerBounds p) {t : ℕ}
    (ht : p.currentTerm ≤ t) :
    ServerBounds (C := C) { p with currentTerm := t, votedFor := none, role := .follower } := by
  constructor
  · intro e he; exact (h.bound e he).trans ht
  · simp
  · simp

theorem ServerBounds.timeout {p : ServerState C} (h : ServerBounds p) (n : NodeId) :
    ServerBounds (C := C) { p with
      currentTerm := p.currentTerm + 1
      votedFor := some n
      role := .candidate } := by
  constructor
  · intro e he; exact (h.bound e he).trans (Nat.le_succ _)
  · intro _ e he; exact Nat.lt_succ_of_le (h.bound e he)
  · simp

theorem ServerBounds.elect {p : ServerState C} (h : ServerBounds p)
    (hc : p.role = .candidate) :
    ServerBounds (C := C) { p with role := .leader, matchIndex := fun _ => 0 } := by
  constructor
  · exact h.bound
  · simp
  · intro _; exact h.active (by simp [hc])

theorem ServerBounds.append {p : ServerState C} (h : ServerBounds p)
    (hl : p.role = .leader) (cmd : EntryPayload) :
    ServerBounds (C := C) { p with log := p.log ++ [⟨p.log.length + 1, p.currentTerm, cmd⟩] } := by
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
    ServerBounds (C := C) { p with
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
    (n : NodeId) (p : ServerState C) (hp : ServerBounds p) :
    ∀ v, ServerBounds ((setServer s n p).servers v) := by
  intro v
  by_cases hv : v = n
  · subst v; simpa [setServer] using hp
  · simpa [setServer, Function.update_of_ne hv] using h v

theorem bounds_step {s s' : GlobalState C} (h : Bounds s) (st : Step s s') : Bounds s' := by
  constructor
  · cases st with
    | observe _ ht => exact servers_set h.servers _ _ ((h.servers _).observe ht.le)
    | timeout n _ _ => exact servers_set h.servers _ _ ((h.servers n).timeout n)
    | elect hc _ => exact servers_set h.servers _ _ ((h.servers _).elect hc)
    | append cmd hl _ => exact servers_set h.servers _ _ ((h.servers _).append hl cmd)
    | @appendEntries v leader t prev pt lc entries before after he ht _ =>
      apply servers_set h.servers v _ ((h.servers v).handle prev lc entries ?_)
      have hm : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈ s.network := by
        rw [he]; simp
      simpa [PacketBounds, ht] using h.network _ hm
    | @commit n index _ _ _ _ =>
      apply servers_set h.servers n
      constructor
      · exact (h.servers n).bound
      · dsimp; split_ifs <;> simp_all
      · dsimp; split_ifs <;> simp_all [ServerBounds.active (h.servers n)]
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
        simp only [grantVote, receiveVote, receiveAppendReply, consume,
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
    | @append n cmd hl _ =>
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
    (n : NodeId) (e : LogEntry) (he : e ∈ (s.servers n).log) :
    e.term ≤ (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.bound e he

theorem reachable_candidate_strict {s : GlobalState C} (hr : Reachable s)
    (n : NodeId) (hc : (s.servers n).role = .candidate)
    (e : LogEntry) (he : e ∈ (s.servers n).log) :
    e.term < (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.candidate hc e he

theorem reachable_active_positive {s : GlobalState C} (hr : Reachable s)
    (n : NodeId) (hc : (s.servers n).role ≠ .follower) :
    0 < (s.servers n).currentTerm := (reachable_bounds hr).servers n |>.active hc


/-- Every non-default active configuration is supplied by a surviving log entry. -/
theorem active_config_origin (log : List LogEntry) (cfg : Config) :
    active_config log cfg = cfg ∨
      ∃ e ∈ log, e.payload = .config (active_config log cfg) := by
  induction log generalizing cfg with
  | nil => exact Or.inl rfl
  | cons e es ih =>
    have he : active_config (e :: es) cfg = active_config es
        (match e.payload with | .command _ => cfg | .config next => next) := rfl
    rw [he]
    cases hp : e.payload with
    | command cmd =>
      have hi := ih cfg
      change active_config es cfg = cfg ∨
        ∃ x ∈ e :: es, x.payload = .config (active_config es cfg)
      rcases hi with hi | ⟨x, hx, hp⟩
      · exact Or.inl hi
      · exact Or.inr ⟨x, List.mem_cons_of_mem e hx, hp⟩
    | config next =>
      have hi := ih next
      change active_config es next = cfg ∨
        ∃ x ∈ e :: es, x.payload = .config (active_config es next)
      rcases hi with hi | ⟨x, hx, hp⟩
      · exact Or.inr ⟨e, by simp, by rw [hi]; exact hp⟩
      · exact Or.inr ⟨x, List.mem_cons_of_mem e hx, hp⟩

/-- A real positive commit is based on successful deliveries for every counted
nonleader. These are historical receipts, not statements about current replicas. -/
theorem commit_quorum_ack_origin {run : Execution C} {k leader index : ℕ}
    (hc : CommitEvent run k leader index) (v : ℕ)
    (hv : v ∈ replicationQuorum (run.state k) leader index) (hne : v ≠ leader)
    (hi : 0 < index) : ∃ matched, index ≤ matched ∧
      AckWitness run k ((run.state k).servers leader).currentTerm leader v matched := by
  have hmatch : index ≤ ((run.state k).servers leader).matchIndex v := by
    simp only [replicationQuorum, Finset.mem_filter] at hv
    exact hv.2.resolve_left hne
  exact match_witness run k (by have := hc.within; omega) leader hc.leaderRole v index hi hmatch

/-- A new-only candidate must depend on a real commit of a strictly smaller term.
The proof uses entry creation, candidate term bounds and historical commitIndex
provenance. Identifying that committed prefix with joint is a further obligation. -/
theorem new_candidate_has_earlier_commit (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (candidate : ℕ)
    (hc : ((run.state k).servers candidate).role = .candidate)
    (ha : active ((run.state k).servers candidate) = C.finalConfig)
    (hne : C.initial ≠ C.finalConfig) :
    ∃ j owner a committer bound, a < j ∧ j < k ∧ CommitEvent run a committer bound ∧
      ((run.state a).servers committer).currentTerm <
        ((run.state k).servers candidate).currentTerm ∧
      active ((run.state j).servers owner) = C.jointConfig := by
  obtain hdefault | ⟨e, he, hcfg⟩ :=
    active_config_origin ((run.state k).servers candidate).log C.initial
  · exact False.elim (hne (hdefault.symm.trans ha))
  have hnew : e.payload = .config C.finalConfig := hcfg.trans (congrArg EntryPayload.config ha)
  obtain ⟨j, hj, owner, cmd, hrole, hguard, heq, hnext⟩ :=
    trace_generated run k hk candidate e he
  have hcmd : cmd = .config C.finalConfig := by simpa [heq] using hnew
  subst cmd
  rcases hguard with ⟨_, heqcfg, _⟩ | ⟨hactive, _, joint, hmem, _hpayload⟩
  · cases heqcfg
  have hjterm : ((run.state j).servers owner).currentTerm <
      ((run.state k).servers candidate).currentTerm := by
    have hb := reachable_candidate_strict (run.reachable k hk) candidate hc e he
    simpa [heq] using hb
  have hp : 0 < ((run.state j).servers owner).commitIndex := by
    by_contra h
    have hz : ((run.state j).servers owner).commitIndex = 0 := by omega
    simp [hz] at hmem
  obtain ⟨a, committer, bound, hat, hcommit, _hbound, hterm⟩ :=
    commit_index_history run j (by omega) owner
      ((run.state j).servers owner).commitIndex hp le_rfl
  exact ⟨j, owner, a, committer, bound, hat, hj, hcommit, hterm.trans_lt hjterm, hactive⟩

/-- Append one actual transition to a finite execution. -/
def Execution.extend (run : Execution C) (next : GlobalState C)
    (hstep : Step (run.state run.length) next) : Execution C where
  length := run.length + 1
  state := fun i => if i ≤ run.length then run.state i else next
  initial := by simp [run.initial]
  transition := by
    intro i hi
    by_cases hlt : i < run.length
    · simpa [show i ≤ run.length by omega, show i + 1 ≤ run.length by omega]
        using run.transition i hlt
    · have he : i = run.length := by omega
      subst i
      simpa [show ¬ run.length + 1 ≤ run.length by omega] using hstep

theorem reachable_execution {s : GlobalState C} (hr : Reachable s) :
    ∃ run : Execution C, run.state run.length = s := by
  induction hr with
  | init => exact ⟨⟨0, fun _ => initState C, rfl, by omega⟩, rfl⟩
  | @step s next _ hstep ih =>
    obtain ⟨run, hend⟩ := ih
    refine ⟨run.extend next (hend ▸ hstep), ?_⟩
    simp [Execution.extend, show ¬ run.length + 1 ≤ run.length by omega]

/-- Only these configurations can occur; this does not assert their temporal compatibility. -/
def AllowedConfig (C : Transition) (cfg : Config) : Prop :=
  cfg = C.initial ∨ cfg = C.jointConfig ∨ cfg = C.finalConfig

theorem log_config_origin (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (node : ℕ) (e : LogEntry) (he : e ∈ ((run.state k).servers node).log)
    (cfg : Config) (hcfg : e.payload = .config cfg) :
    cfg = C.jointConfig ∨ cfg = C.finalConfig := by
  obtain ⟨j, _hj, owner, cmd, _hrole, hguard, heq, _hnext⟩ :=
    trace_generated run k hk node e he
  have hcmd : cmd = .config cfg := by simpa [heq] using hcfg
  subst cmd
  rcases hguard with ⟨_, he, _⟩ | ⟨_, he, _⟩
  · exact Or.inl he
  · exact Or.inr he

theorem active_config_reachable {s : GlobalState C} (hr : Reachable s) (node : ℕ) :
    AllowedConfig C (active (s.servers node)) := by
  obtain ⟨run, hend⟩ := reachable_execution hr
  obtain h | ⟨e, he, hcfg⟩ := active_config_origin (s.servers node).log C.initial
  · exact Or.inl h
  · apply Or.inr
    apply log_config_origin run run.length le_rfl node e (hend ▸ he)
    exact hcfg

theorem elected_config_reachable {s : GlobalState C} (hr : Reachable s) :
    ∀ t n cfg, (t, n, cfg) ∈ s.elected → AllowedConfig C cfg := by
  induction hr with
  | init => simp [initState]
  | @step s next hr st ih =>
    cases st with
    | @elect n _ _ =>
      intro t node cfg hm
      simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hm
      rcases hm with ⟨rfl, rfl, rfl⟩ | hm
      · exact active_config_reachable hr node
      · exact ih t node cfg hm
    | _ => exact ih

/-- A joint quorum intersects every permitted election configuration. -/
theorem joint_quorum_intersects_any_allowed {Q J : Finset NodeId} {cfg : Config}
    (hj : is_joint_quorum J C.oldMembers C.newMembers)
    (hq : has_quorum Q cfg) (hc : AllowedConfig C cfg) : (J ∩ Q).Nonempty := by
  rcases hc with rfl | rfl | rfl
  · have hi := quorum_intersection_stable_joint hq hj
    simpa [Finset.inter_comm] using hi
  · obtain ⟨v, hv⟩ := (quorum_intersection_joint_joint hj hq).1
    exact ⟨v, (Finset.mem_inter.mp hv).1⟩
  · exact quorum_intersection_joint_new hj hq

/-- Before any final-configuration election, all certificates share old membership.
This is conditional on history, not an extra operational transition guard. -/
theorem election_safety_without_new_certificate {s : GlobalState C} (hr : Reachable s)
    (hphase : ∀ t n cfg, (t, n, cfg) ∈ s.elected →
      cfg = C.initial ∨ cfg = C.jointConfig)
    {t a b : ℕ} {cfgA cfgB : Config} (ha : (t, a, cfgA) ∈ s.elected)
    (hb : (t, b, cfgB) ∈ s.elected) : a = b := by
  rcases hphase t a cfgA ha with rfl | rfl <;>
    rcases hphase t b cfgB hb with rfl | rfl
  · exact same_configuration_election_safety hr ha hb
  · exact old_joint_election_safety hr ha hb
  · exact (old_joint_election_safety hr hb ha).symm
  · exact same_configuration_election_safety hr ha hb

/-- Proven lower layers only. In particular, numeric commit origin is not
substituted for the requested CommitPrefixReplicated invariant. -/
structure ProvenHistoryInvariant (run : Execution C) (k : ℕ) : Prop where
  votes : VoteHistoryValid (run.state k)
  transport : TransportSound (run.state k)
  ballots : CastWitness run k
  packets : NetworkWitness run k
  termBounds : Bounds (run.state k)
  entries : ∀ node e, e ∈ ((run.state k).servers node).log → TraceGenerated run k e
  commitIndices : ∀ node index, 0 < index →
    index ≤ ((run.state k).servers node).commitIndex → CommitIndexWitness run k node index
  configs : ∀ node, AllowedConfig C (active ((run.state k).servers node))

theorem proven_history_invariant (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    ProvenHistoryInvariant run k where
  votes := vote_history_reachable (run.reachable k hk)
  transport := transport_reachable (run.reachable k hk)
  ballots := cast_witness run k hk
  packets := network_witness run k hk
  termBounds := reachable_bounds (run.reachable k hk)
  entries := trace_generated run k hk
  commitIndices := fun node index hp hi => commit_index_history run k hk node index hp hi
  configs := active_config_reachable (run.reachable k hk)

theorem term_path_monotone {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') (n : ℕ) :
    (s.servers n).currentTerm ≤ (s'.servers n).currentTerm := by
  induction path with
  | refl => exact le_rfl
  | tail _ st ih => exact ih.trans (term_step_monotone st n)
/-- A step ending as candidate in the same term preserves both candidacy and log. -/
theorem candidate_step_backwards {s s' : GlobalState C} (step : Step s s')
    (n : NodeId) (hc : (s'.servers n).role = .candidate)
    (ht : (s.servers n).currentTerm = (s'.servers n).currentTerm) :
    (s.servers n).role = .candidate ∧ (s.servers n).log = (s'.servers n).log := by
  cases step <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader, leaderAppend,
      handleAppend, denyAppend, receiveAppendReply, consume, commitLeader, setServer,
      Function.update_apply] at hc ht ⊢ <;>
    (try split_ifs at hc ht ⊢) <;> simp_all

theorem candidate_path_log_eq {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') (n : NodeId)
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
    (c : NodeId) (li lt : ℕ) (hw : RequestWitness run k t c li lt)
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


/-- A counted vote certifies freshness of the candidate's actual campaign log
against the voter's log at the historical vote event. It does not assert a prefix
inclusion, which additionally requires the global log invariants. -/
theorem candidate_vote_historical_freshness (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (candidate voter : ℕ)
    (hc : ((run.state k).servers candidate).role = .candidate)
    (hv : (((run.state k).servers candidate).currentTerm, voter, candidate) ∈
      (run.state k).cast) :
    ∃ j, j < k ∧ upToDateFields ((run.state j).servers voter)
      (lastIndex ((run.state k).servers candidate).log)
      (lastTerm ((run.state k).servers candidate).log) := by
  have hw := cast_witness run k hk _ voter candidate hv
  cases hw with
  | selfVote j hj he hrole hterm hnext =>
    subst voter
    have request : RequestWitness run k ((run.state k).servers candidate).currentTerm
        candidate (lastIndex ((run.state j).servers candidate).log)
        (lastTerm ((run.state j).servers candidate).log) :=
      ⟨j, hj, hrole, hterm, rfl, rfl, hnext⟩
    obtain ⟨hli, hlt⟩ := request_candidate_snapshot run k _ hk candidate _ _ request hc rfl
    refine ⟨j, hj, Or.inr ⟨hlt, ?_⟩⟩
    exact Nat.le_of_eq hli
  | granted j li lt before after hj hnet hterm hguard request hnext =>
    obtain ⟨hli, hlt⟩ := request_candidate_snapshot run k _ hk candidate li lt
      (request.mono (by omega)) hc rfl
    refine ⟨j, hj, ?_⟩
    simpa only [hli, hlt] using hguard.2

/-- The vote snapshot also fixes the voter's term immediately after casting it. -/
theorem candidate_vote_timed_freshness (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (candidate voter : ℕ)
    (hc : ((run.state k).servers candidate).role = .candidate)
    (hv : (((run.state k).servers candidate).currentTerm, voter, candidate) ∈
      (run.state k).cast) :
    ∃ j, j < k ∧
      ((run.state (j + 1)).servers voter).currentTerm =
        ((run.state k).servers candidate).currentTerm ∧
      upToDateFields ((run.state j).servers voter)
        (lastIndex ((run.state k).servers candidate).log)
        (lastTerm ((run.state k).servers candidate).log) := by
  have hw := cast_witness run k hk _ voter candidate hv
  cases hw with
  | selfVote j hj he hrole hterm hnext =>
    subst voter
    have request : RequestWitness run k ((run.state k).servers candidate).currentTerm
        candidate (lastIndex ((run.state j).servers candidate).log)
        (lastTerm ((run.state j).servers candidate).log) :=
      ⟨j, hj, hrole, hterm, rfl, rfl, hnext⟩
    obtain ⟨hli, hlt⟩ := request_candidate_snapshot run k _ hk candidate _ _ request hc rfl
    refine ⟨j, hj, ?_, Or.inr ⟨hlt, Nat.le_of_eq hli⟩⟩
    rw [hnext]
    simpa [startElection, setServer] using hterm.symm
  | granted j li lt before after hj hnet hterm hguard request hnext =>
    obtain ⟨hli, hlt⟩ := request_candidate_snapshot run k _ hk candidate li lt
      (request.mono (by omega)) hc rfl
    refine ⟨j, hj, ?_, ?_⟩
    · rw [hnext]
      simpa [grantVote, setServer] using hterm.symm
    · simpa only [hli, hlt] using hguard.2

/-- An acknowledgment in an older term necessarily precedes a later-term vote.
This is a temporal statement about actual events, without a log-retention premise. -/
theorem ack_precedes_later_vote (run : Execution C) (k t : ℕ)
    (hk : k ≤ run.length) (leader voter matched j : ℕ)
    (ha : AckWitness run k t leader voter matched) (_hj : j < run.length)
    (ht : t < ((run.state (j + 1)).servers voter).currentTerm) :
    ∃ a prev pt entries lc before after, a < j ∧
      (run.state a).network = before ++
        ⟨voter, .appendEntries t leader prev pt entries lc⟩ :: after ∧
      t = ((run.state a).servers voter).currentTerm ∧
      prevMatches ((run.state a).servers voter).log prev pt ∧
      matched = prev + entries.length ∧
      run.state (a + 1) = handleAppend (run.state a) voter leader prev entries lc before after := by
  obtain ⟨a, prev, pt, entries, lc, before, after, ha, hnet, hterm, hp, hm, hnext⟩ := ha
  have hpost : ((run.state (a + 1)).servers voter).currentTerm = t := by
    rw [hnext]
    simpa [handleAppend, setServer] using hterm.symm
  have haj : a < j := by
    by_contra hn
    have hmono := term_path_monotone
      (run.path (j + 1) (a + 1) (by omega) (by omega)) voter
    rw [hpost] at hmono
    omega
  exact ⟨a, prev, pt, entries, lc, before, after, haj, hnet, hterm, hp, hm, hnext⟩

/-- A joint commit quorum and a subsequently eligible candidate share a real
voter. Its successful replication receipt is older than its vote. Prefix equality
and retention are deliberately not part of this intermediate conclusion. -/
theorem joint_commit_election_common_voter (run : Execution C) (a k : ℕ)
    (hk : k ≤ run.length) (committer index candidate : ℕ)
    (hcommit : CommitEvent run a committer index) (hindex : 0 < index)
    (hjoint : active ((run.state a).servers committer) = C.jointConfig)
    (hc : ((run.state k).servers candidate).role = .candidate)
    (helect : has_quorum (eligibleVotes (run.state k) candidate)
      (active ((run.state k).servers candidate)))
    (hterm : ((run.state a).servers committer).currentTerm <
      ((run.state k).servers candidate).currentTerm) :
    ∃ voter j, voter ∈ replicationQuorum (run.state a) committer index ∧
      voter ∈ eligibleVotes (run.state k) candidate ∧ j < k ∧
      upToDateFields ((run.state j).servers voter)
        (lastIndex ((run.state k).servers candidate).log)
        (lastTerm ((run.state k).servers candidate).log) ∧
      (voter = committer ∧ a ≤ j ∨ ∃ b matched, b < j ∧ index ≤ matched ∧
        AckWitness run (b + 1) ((run.state a).servers committer).currentTerm
          committer voter matched) := by
  have hjq : is_joint_quorum (replicationQuorum (run.state a) committer index)
      C.oldMembers C.newMembers := by
    have hq := hcommit.quorum
    rw [hjoint] at hq
    exact hq
  obtain ⟨voter, hv⟩ := joint_quorum_intersects_any_allowed hjq helect
    (active_config_reachable (run.reachable k hk) candidate)
  obtain ⟨hvr, hve⟩ := Finset.mem_inter.mp hv
  have hreceived : (((run.state k).servers candidate).currentTerm, voter, candidate) ∈
      (run.state k).received := by
    exact (mem_votesFor _ _ _ _).mp (Finset.mem_inter.mp hve).1
  have hcast := (transport_reachable (run.reachable k hk)).received hreceived
  obtain ⟨j, hj, htj, hfresh⟩ := candidate_vote_timed_freshness run k hk candidate voter hc hcast
  refine ⟨voter, j, hvr, hve, hj, hfresh, ?_⟩
  by_cases hvc : voter = committer
  · subst voter
    refine Or.inl ⟨rfl, ?_⟩
    by_contra hn
    have hmono := term_path_monotone
      (run.path (j + 1) a (by omega) hcommit.within.le) committer
    rw [htj] at hmono
    omega
  · obtain ⟨matched, hmatched, hack⟩ := commit_quorum_ack_origin hcommit voter hvr hvc hindex
    obtain ⟨b, prev, pt, entries, lc, before, after, hbj, hnet, hbt, hp, hm, hnext⟩ :=
      ack_precedes_later_vote run a _ hcommit.within.le committer voter matched j hack
        (by omega) (htj ▸ hterm)
    exact Or.inr ⟨b, matched, hbj, hmatched,
      b, prev, pt, entries, lc, before, after, by omega, hnet, hbt, hp, hm, hnext⟩

/-! Auxiliary archive lemmas; no global safety conclusion is assumed by Step. -/
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


theorem matching_refl (a : List LogEntry) : LogMatching a a := by
  intro _ _ _ _ _ _
  rfl

theorem matching_symm {a b : List LogEntry} (h : LogMatching a b) : LogMatching b a := by
  intro i x y hx hy ht
  exact (h i y x hy hx ht.symm).symm

theorem matching_take_right {a b : List LogEntry} (h : LogMatching a b) (n : ℕ) :
    LogMatching a (b.take n) :=
  matching_symm ((matching_symm h).take_left n)

theorem matching_take_both {a b : List LogEntry} (h : LogMatching a b) (m n : ℕ) :
    LogMatching (a.take m) (b.take n) :=
  matching_take_right (h.take_left m) n

theorem matching_prefix_left {a b a' : List LogEntry} (h : LogMatching a b)
    (hp : a'.IsPrefix a) : LogMatching a' b := by
  have he := List.prefix_iff_eq_take.mp hp
  simpa only [← he] using h.take_left a'.length

theorem matching_prefix_right {a b b' : List LogEntry} (h : LogMatching a b)
    (hp : b'.IsPrefix b) : LogMatching a b' :=
  matching_symm (matching_prefix_left (matching_symm h) hp)

theorem matching_prefix_both {a b a' b' : List LogEntry} (h : LogMatching a b)
    (ha : a'.IsPrefix a) (hb : b'.IsPrefix b) : LogMatching a' b' :=
  matching_prefix_right (matching_prefix_left h ha) hb

/-- Equal terms at a shared position determine the entire entry, including command. -/
theorem matching_entry_eq {a b : List LogEntry} (h : LogMatching a b)
    {i : ℕ} {x y : LogEntry} (hx : a[i]? = some x) (hy : b[i]? = some y)
    (ht : x.term = y.term) : x = y := by
  have he := congrArg (fun l : List LogEntry => l[i]?) (h i x y hx hy ht)
  simpa only [List.getElem?_take_of_succ, hx, hy, Option.some.injEq] using he

theorem compatible_of_aligned (a b : List LogEntry)
    (h : ∀ (i : ℕ) (x y : LogEntry),
      a[i]? = some x → b[i]? = some y → x.term = y.term → x = y) :
    CompatibleEntries a b := by
  induction a generalizing b with
  | nil => cases b <;> trivial
  | cons x a ih =>
    cases b with
    | nil => trivial
    | cons y b =>
      constructor
      · exact h 0 x y rfl rfl
      · apply ih
        intro i u v hu hv ht
        exact h (i + 1) u v (by simpa using hu) (by simpa using hv) ht

theorem matching_compatible {a b : List LogEntry} (h : LogMatching a b) :
    CompatibleEntries a b :=
  compatible_of_aligned a b (fun _ _ _ hx hy ht => matching_entry_eq h hx hy ht)

/-- Compatibility is inherited by the aligned suffix and the finite incoming batch. -/
theorem matching_compatible_slice {old source : List LogEntry}
    (h : LogMatching old source) (prev count : ℕ) :
    CompatibleEntries (old.drop prev) ((source.drop prev).take count) := by
  apply compatible_of_aligned
  intro i x y hx hy ht
  have hi : i < count := by
    obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp hy
    simp only [List.length_take, List.length_drop] at hi
    omega
  rw [List.getElem?_drop] at hx
  rw [List.getElem?_take_of_lt hi, List.getElem?_drop] at hy
  exact matching_entry_eq h hx hy ht

/-- The predecessor test yields equality of complete prefixes, including at index zero. -/
theorem matching_predecessor_prefix {old source : List LogEntry}
    (h : LogMatching old source) (prev : ℕ) (hs : prev ≤ source.length)
    (hp : prevMatches old prev (termAt source prev)) :
    old.take prev = source.take prev := by
  by_cases hz : prev = 0
  · simp [hz]
  have ho : prev - 1 < old.length := by have := hp.1; omega
  have hi : prev - 1 < source.length := by omega
  have hgeto : old[prev - 1]? = some old[prev - 1] := List.getElem?_eq_getElem ho
  have hgets : source[prev - 1]? = some source[prev - 1] := List.getElem?_eq_getElem hi
  have ht : old[prev - 1].term = source[prev - 1].term := by
    simpa only [termAt, hz, ↓reduceIte, hgeto, hgets, Option.getD_some] using hp.2
  have hm := h (prev - 1) _ _ hgeto hgets ht
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ prev)] using hm

/-- A successful RPC leaves the old log or installs a prefix of its historical source. -/
theorem matching_append_entries_choice {old source : List LogEntry}
    (h : LogMatching old source) (prev count : ℕ) (hs : prev ≤ source.length)
    (hp : prevMatches old prev (termAt source prev)) :
    appendEntriesLog old prev ((source.drop prev).take count) = old ∨
    appendEntriesLog old prev ((source.drop prev).take count) =
      source.take (prev + count) :=
  append_entries_log_choice old source prev count
    (matching_predecessor_prefix h prev hs hp) (matching_compatible_slice h prev count)



/-- Historical election uniqueness, used only as an auxiliary proof hypothesis. -/
def ElectionHistorySafe (s : GlobalState C) : Prop :=
  ∀ t a b cfgA cfgB, (t, a, cfgA) ∈ s.elected → (t, b, cfgB) ∈ s.elected → a = b

def LeadersCovered (s : GlobalState C) : Prop :=
  ∀ n, (s.servers n).role = .leader →
    ∃ cfg, ((s.servers n).currentTerm, n, cfg) ∈ s.elected

theorem leaders_step {s s' : GlobalState C} (h : LeadersCovered s)
    (step : Step s s') : LeadersCovered s' := by
  intro n hn
  cases step <;>
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
      leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer,
      Function.update_apply] at hn ⊢ <;>
    (try split_ifs at hn ⊢) <;> simp_all [LeadersCovered]

theorem leaders_covered_reachable {s : GlobalState C} (hr : Reachable s) : LeadersCovered s := by
  induction hr with
  | init => simp [LeadersCovered, initState]
  | step _ st ih => exact leaders_step ih st

theorem elected_step_monotone {s s' : GlobalState C} (step : Step s s') :
    s.elected ⊆ s'.elected := by
  cases step <;> simp [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
    leaderAppend, handleAppend, receiveAppendReply, denyAppend, consume, commitLeader, setServer]

theorem elected_bound_step {s s' : GlobalState C}
    (bound : ∀ t n cfg, (t, n, cfg) ∈ s.elected → t ≤ (s.servers n).currentTerm)
    (step : Step s s') : ∀ t n cfg, (t, n, cfg) ∈ s'.elected → t ≤ (s'.servers n).currentTerm := by
  have old : ∀ t n cfg, (t, n, cfg) ∈ s.elected → t ≤ (s'.servers n).currentTerm :=
    fun t n cfg hn => (bound t n cfg hn).trans (term_step_monotone step n)
  cases step <;> try exact old
  case elect n hl hm =>
    intro t v cfg hv
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hv
    rcases hv with ⟨rfl, rfl, rfl⟩ | hv
    · simp [becomeLeader, setServer]
    · exact old _ _ _ hv

theorem elected_bound_reachable {s : GlobalState C} (hr : Reachable s) :
    ∀ t n cfg, (t, n, cfg) ∈ s.elected → t ≤ (s.servers n).currentTerm := by
  induction hr with
  | init => simp [initState]
  | step _ st ih => exact elected_bound_step ih st

def MessageAuth (elected : Finset (ℕ × NodeId × Config)) (m : Envelope C) : Prop :=
  match m.body with
  | .appendEntries t leader _ _ _ _ => (∃ cfg, (t, leader, cfg) ∈ elected) ∧ m.destination ≠ leader
  | _ => True

def NetworkAuth (s : GlobalState C) : Prop := ∀ m ∈ s.network, MessageAuth s.elected m

theorem messageAuth_mono {a b : Finset (ℕ × NodeId × Config)} (h : a ⊆ b)
    {m : Envelope C} (hm : MessageAuth a m) : MessageAuth b m := by
  cases m with
  | mk dst body =>
    cases body <;> (dsimp [MessageAuth] at hm ⊢; try trivial)
    obtain ⟨⟨cfg, hc⟩, hn⟩ := hm
    exact ⟨⟨cfg, h hc⟩, hn⟩

theorem broadcast_member_ne {sender : NodeId} {body : NetworkMessage C}
    {m : Envelope C} (hm : m ∈ broadcast sender body) :
    m.body = body ∧ m.destination ≠ sender := by
  simp only [broadcast, List.mem_map, List.mem_filter] at hm
  obtain ⟨n, ⟨_, hn⟩, rfl⟩ := hm
  exact ⟨rfl, of_decide_eq_true hn⟩

theorem network_auth_step {s s' : GlobalState C} (hr : Reachable s)
    (h : NetworkAuth s) (step : Step s s') : NetworkAuth s' := by
  have grow := elected_step_monotone step
  have old : ∀ m ∈ s.network, MessageAuth s'.elected m :=
    fun m hm => messageAuth_mono grow (h m hm)
  have rem : ∀ before after removed, s.network = before ++ removed :: after →
      ∀ m ∈ before ++ after, MessageAuth s'.elected m := by
    intro before after removed he m hm
    apply old m
    rw [he]
    simp only [List.mem_append, List.mem_cons] at hm ⊢
    tauto
  cases step with
  | observe => exact old
  | timeout n _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · obtain ⟨hb, _⟩ := broadcast_member_ne hm
      simp [MessageAuth, hb]
  | @vote v c t li lt before after he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | voteReply he _ _ => exact rem _ _ _ he
  | elect => exact old
  | append cmd hl _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · obtain ⟨hb, hd⟩ := broadcast_member_ne hm
      simp only [MessageAuth, hb]
      exact ⟨(by obtain ⟨cfg, hc⟩ := leaders_covered_reachable hr _ hl; exact ⟨cfg, grow hc⟩), hd⟩
  | commit => exact old
  | @replicate n v prev count hl hne _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact old m hm
    · simp only [List.mem_singleton] at hm
      subst m
      obtain ⟨cfg, hc⟩ := leaders_covered_reachable hr _ hl
      exact ⟨⟨cfg, grow hc⟩, Ne.symm hne⟩
  | appendEntries he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | appendReply he _ _ => exact rem _ _ _ he
  | rejectVote he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | rejectAppend he _ _ =>
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact rem _ _ _ he m hm
    · simp only [List.mem_singleton] at hm
      subst m; trivial
  | drop he => exact rem _ _ _ he
  | @duplicate m hm =>
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact old _ hm
    · exact old a ha


theorem network_auth_reachable {s : GlobalState C} (hr : Reachable s) : NetworkAuth s := by
  induction hr with
  | init => simp [NetworkAuth, initState]
  | step hr st ih => exact network_auth_step hr ih st

/-- Retirement can end leadership within a term. This length property does not
assume that an elected server remains leader after its removal. -/
theorem active_elected_log_length_step {s s' : GlobalState C} (hr : Reachable s)
    (safe : ElectionHistorySafe s) (step : Step s s') (t n : ℕ) (cfg : Config)
    (hn : (t, n, cfg) ∈ s.elected) (he : t = (s'.servers n).currentTerm) :
    (s.servers n).log.length ≤ (s'.servers n).log.length := by
  have hb := elected_bound_reachable hr t n cfg hn
  have ht := term_step_monotone step n
  have hcurrent : (s.servers n).currentTerm = t := by omega
  cases step with
  | @appendEntries v leader tr prev pt lc entries before after hnet htr hp =>
    by_cases hv : n = v
    · subst v
      have packet : (⟨n, .appendEntries tr leader prev pt entries lc⟩ : Envelope C) ∈
          s.network := by rw [hnet]; simp
      obtain ⟨⟨cfgLeader, hleader⟩, hne⟩ := network_auth_reachable hr _ packet
      have heqt : tr = t := htr.trans hcurrent
      subst tr
      exact False.elim
        (hne (safe t n leader cfg cfgLeader hn (by simpa only [hcurrent] using hleader)))
    · simp [handleAppend, setServer, Function.update_of_ne hv]
  | _ =>
    clear safe hr hn he ht hb hcurrent
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader, leaderAppend,
      denyAppend, receiveAppendReply, consume, commitLeader, setServer, Function.update_apply]
    (try split_ifs) <;> simp_all

/-- The standard positional Log Matching condition, for every pair of servers. -/
def GlobalLogMatching (s : GlobalState C) : Prop :=
  ∀ i j, LogMatching (s.servers i).log (s.servers j).log

/-- An RPC's predecessor and contiguous batch come from one archived source log. -/
def Backed (s : GlobalState C) (A : List LogEntry → Prop)
    (t : ℕ) (leader : NodeId) (prev pt : ℕ) (entries : List LogEntry) : Prop :=
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
    (before.servers n).role = .leader ∧ mayAppend (before.servers n) cmd ∧
    i = (before.servers n).log.length ∧
    e = ⟨(before.servers n).log.length + 1, (before.servers n).currentTerm, cmd⟩ ∧
    Relation.ReflTransGen Step (leaderAppend before n cmd) s

theorem Generated.advance {s s' : GlobalState C} {i : ℕ} {e : LogEntry}
    (h : Generated s i e) (st : Step s s') : Generated s' i e := by
  obtain ⟨before, n, cmd, hr, hl, hg, hi, he, path⟩ := h
  exact ⟨before, n, cmd, hr, hl, hg, hi, he, path.tail st⟩

/-- Entries originated at an elected leader, and a same-term originating leader
has already advanced strictly past every index it generated. -/
def Origin (s : GlobalState C) (A : List LogEntry → Prop) : Prop :=
  ∀ l, A l → ∀ i e, l[i]? = some e →
    ∃ n cfg, (e.term, n, cfg) ∈ s.elected ∧
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
    (hab : ∀ l, A l → B l) {t prev pt : ℕ} {leader : NodeId}
    {entries : List LogEntry} (h : Backed s A t leader prev pt entries) :
    Backed s B t leader prev pt entries := by
  obtain ⟨source, count, hs, hp, ht, he, history⟩ := h
  exact ⟨source, count, hab source hs, hp, ht, he, history⟩

theorem Backed.advance {s s' : GlobalState C} {A : List LogEntry → Prop}
    {t prev pt : ℕ} {leader : NodeId} {entries : List LogEntry}
    (h : Backed s A t leader prev pt entries) (st : Step s s') :
    Backed s' A t leader prev pt entries := by
  obtain ⟨source, count, hs, hp, ht, he, generated, hr, path, role, term, log⟩ := h
  exact ⟨source, count, hs, hp, ht, he, generated, hr, path.tail st, role, term, log⟩

theorem NetworkBacked.mono {s : GlobalState C} {A B : List LogEntry → Prop}
    (h : NetworkBacked s A) (hab : ∀ l, A l → B l) : NetworkBacked s B := by
  intro dst t leader prev pt entries lc hm
  exact (h dst t leader prev pt entries lc hm).mono hab

/-- An existing archived entry retains its origin after any operational step. -/
theorem origin_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (safe : ElectionHistorySafe s) (st : Step s s')
    (h : Origin s A) : Origin s' A := by
  intro l hl i e he
  obtain ⟨n, cfg, hn, hb, hg⟩ := h l hl i e he
  refine ⟨n, cfg, elected_step_monotone st hn, ?_, hg.advance st⟩
  intro ht
  have bound := elected_bound_reachable hr e.term n cfg hn
  have mono := term_step_monotone st n
  have oldTerm : e.term = (s.servers n).currentTerm := by omega
  exact (hb oldTerm).trans_le (active_elected_log_length_step hr safe st e.term n cfg hn ht)

/-- A same-term entry cannot occur at the fresh append index anywhere in the archive. -/
theorem archive_fresh {s : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A) {n : NodeId}
    (leader : (s.servers n).role = .leader) {l : List LogEntry} (hl : A l)
    (e : LogEntry) (he : l[(s.servers n).log.length]? = some e) :
    (s.servers n).currentTerm ≠ e.term := by
  intro ht
  obtain ⟨owner, cfg, elected, bound, _generated⟩ := h.origin l hl _ e he
  obtain ⟨ourCfg, ours⟩ := leaders_covered_reachable hr n leader
  have same : owner = n := safe e.term owner n cfg ourCfg elected (ht ▸ ours)
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
  | @timeout n _ _ =>
    simp only [startElection, List.mem_append] at hm
    rcases hm with hm | hm
    · exact oldPacket dst t leader prev pt entries lc hm
    · simp [broadcast] at hm
  | @append n cmd hn allowed =>
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
      · refine ⟨leaderAppend s leader cmd, hr.step (.append cmd hn allowed), .refl, ?_, ?_, ?_⟩
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
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A) (st : Step s s')
    (logs : ∀ n, (s'.servers n).log = (s.servers n).log) : ArchiveInvariant s' A := by
  have hs : ∀ n, A (s'.servers n).log := by intro n; rw [logs]; exact h.servers n
  exact ⟨h.closed, h.matching, origin_step hr safe st h.origin, hs,
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
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A)
    (n : NodeId) (cmd : EntryPayload)
    (leader : (s.servers n).role = .leader) (allowed : mayAppend (s.servers n) cmd) :
    ArchiveInvariant (leaderAppend s n cmd)
      (extendArchive A ((s.servers n).log ++
        [⟨(s.servers n).log.length + 1, (s.servers n).currentTerm, cmd⟩])) := by
  let e : LogEntry := ⟨(s.servers n).log.length + 1, (s.servers n).currentTerm, cmd⟩
  let fresh := (s.servers n).log ++ [e]
  let B := extendArchive A fresh
  have st : Step s (leaderAppend s n cmd) := .append cmd leader allowed
  have inclusion : ∀ l, A l → B l := fun _ hl => Or.inl hl
  have matchFresh : ∀ l, A l → LogMatching fresh l := by
    intro l hl
    apply log_matching_append (h.matching _ _ (h.servers n) hl) e
    intro y hy
    exact archive_fresh hr safe h leader hl y hy
  have origOld := origin_step hr safe st h.origin
  have origFresh : ∀ i x, fresh[i]? = some x →
      ∃ owner cfg, (x.term, owner, cfg) ∈ (leaderAppend s n cmd).elected ∧
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
      obtain ⟨cfg, helected⟩ := leaders_covered_reachable hr n leader
      refine ⟨n, cfg, helected, ?_, ?_⟩
      · intro _
        simp [leaderAppend, setServer]
      · exact ⟨s, n, cmd, hr, leader, allowed, rfl, rfl, .refl⟩
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
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A)
    {v leader : NodeId} {t prev pt lc : ℕ} {entries : List LogEntry}
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
  exact ⟨h.closed, h.matching, origin_step hr safe st h.origin, logs,
    network_step hr h.network st h.servers logs⟩

/-- Every operational step admits a suitable updated ghost archive. -/
theorem archive_step {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B := by
  cases st with
  | append cmd leader allowed => exact ⟨_, archive_step_append hr safe h _ cmd leader allowed⟩
  | appendEntries he ht hp => exact ⟨_, archive_step_handle_append hr safe h he ht hp⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr safe h (.observe hm ht) ?_⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn member =>
    refine ⟨A, archive_frame hr safe h (.timeout _ n hn member) ?_⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr safe h (.vote he ht hv) ?_⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc => exact ⟨A, archive_frame hr safe h (.voteReply he ht hc) (by intros; rfl)⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr safe h (.elect hc hq) ?_⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr safe h (.commit i hl hi ht hq) ?_⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr safe h (.replicate prev count hl hn hp) (by intros; rfl)⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr safe h (.appendReply he ht hl) ?_⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv =>
    exact ⟨A, archive_frame hr safe h (.rejectVote he ht hv) (by intros; rfl)⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr safe h (.rejectAppend he ht hp) ?_⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr safe h (.drop he) (by intros; rfl)⟩
  | duplicate hm => exact ⟨A, archive_frame hr safe h (.duplicate hm) (by intros; rfl)⟩


/-- The archive at a step uses election uniqueness strictly before that step.
This is an auxiliary induction lemma, not the unconditional dynamic safety result. -/
theorem execution_archive (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) :
    ∃ A, ArchiveInvariant (run.state k) A := by
  induction k with
  | zero => rw [run.initial]; exact ⟨_, archive_init⟩
  | succ k ih =>
    obtain ⟨A, hA⟩ := ih (by omega) (fun j hj => safe j (by omega))
    exact archive_step (run.reachable k (by omega)) (safe k (by omega)) hA
      (run.transition k (by omega))

/-- Log Matching is derived from prior election safety, not assumed by a transition. -/
theorem log_matching_of_prior_election_safety (run : Execution C) (k : ℕ)
    (hk : k ≤ run.length) (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) :
    GlobalLogMatching (run.state k) := by
  obtain ⟨A, hA⟩ := execution_archive run k hk safe
  exact fun u v => hA.matching _ _ (hA.servers u) (hA.servers v)

/-- Even a batch ending inside the common prefix preserves the remaining old suffix. -/
theorem merge_common_prefix (p a b : List LogEntry) (count : ℕ) :
    p.IsPrefix (mergeSuffix (p ++ a) ((p ++ b).take count)) := by
  induction p generalizing count with
  | nil => simp
  | cons e p ih =>
    cases count with
    | zero => simp [List.prefix_append]
    | succ count =>
      simpa [mergeSuffix, List.cons_prefix_cons] using ih count

/-- A shared prefix survives any partial transmission from the source log. -/
theorem common_prefix_retained {p old source : List LogEntry}
    (ho : p.IsPrefix old) (hs : p.IsPrefix source) (prev count : ℕ) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) := by
  obtain ⟨a, rfl⟩ := ho
  obtain ⟨b, rfl⟩ := hs
  induction p generalizing prev with
  | nil => simp
  | cons e p ih =>
    cases prev with
    | zero =>
      simpa [appendEntriesLog] using merge_common_prefix (e :: p) a b count
    | succ prev =>
      simpa [appendEntriesLog, List.cons_prefix_cons] using ih prev

/-- Every incoming entry is retained by a compatible merge, including existing matches. -/
theorem incoming_prefix_merge {old incoming : List LogEntry}
    (hc : CompatibleEntries old incoming) : incoming.IsPrefix (mergeSuffix old incoming) := by
  induction old generalizing incoming with
  | nil => cases incoming <;> simp [mergeSuffix]
  | cons a old ih =>
    cases incoming with
    | nil => simp
    | cons b incoming =>
      dsimp [CompatibleEntries] at hc
      by_cases ht : a.term = b.term
      · have he := hc.1 ht
        subst b
        simpa [mergeSuffix, List.cons_prefix_cons] using ih hc.2
      · simp [mergeSuffix, ht]

/-- Successful matching delivery retains the entire transmitted source prefix. -/
theorem transmitted_prefix_retained {old source : List LogEntry}
    (hm : LogMatching old source) (prev count : ℕ) (hp : prev ≤ source.length)
    (hc : prevMatches old prev (termAt source prev)) :
    (source.take (prev + count)).IsPrefix
      (appendEntriesLog old prev ((source.drop prev).take count)) := by
  have heq := matching_predecessor_prefix hm prev hp hc
  have hmerge := incoming_prefix_merge (matching_compatible_slice hm prev count)
  obtain ⟨suffix, hs⟩ := hmerge
  refine ⟨suffix, ?_⟩
  rw [List.take_add]
  simp only [appendEntriesLog, heq, List.append_assoc, hs]

/-- A source prefix covered by the batch endpoint is installed even if absent locally. -/
theorem covered_prefix_installed {p old source : List LogEntry}
    (hs : p.IsPrefix source) (hm : LogMatching old source) (prev count : ℕ)
    (hp : prev ≤ source.length) (hc : prevMatches old prev (termAt source prev))
    (hlen : p.length ≤ prev + count) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) :=
  (List.prefix_take_iff.mpr ⟨hs, hlen⟩).trans
    (transmitted_prefix_retained hm prev count hp hc)


/-- Replaying an existing prefix leaves the entire local log unchanged. -/
theorem merge_prefix_identity {old incoming : List LogEntry} (h : incoming.IsPrefix old) :
    mergeSuffix old incoming = old := by
  obtain ⟨suffix, rfl⟩ := h
  induction incoming with
  | nil => simp
  | cons e incoming ih => simpa [mergeSuffix] using congrArg (List.cons e) ih

/-- A stale source snapshot that is already a local prefix cannot truncate the log. -/
theorem source_prefix_unchanged {old source : List LogEntry}
    (h : source.IsPrefix old) (prev count : ℕ) :
    appendEntriesLog old prev ((source.drop prev).take count) = old := by
  have hi := (List.take_prefix count (source.drop prev)).trans (h.drop prev)
  simp only [appendEntriesLog, merge_prefix_identity hi, List.take_append_drop]

/-- A common or older source preserves the selected local prefix. -/
theorem comparable_prefix_retained {p old source : List LogEntry}
    (ho : p.IsPrefix old) (hs : source.IsPrefix p ∨ p.IsPrefix source) (prev count : ℕ) :
    p.IsPrefix (appendEntriesLog old prev ((source.drop prev).take count)) := by
  rcases hs with hs | hs
  · rw [source_prefix_unchanged (hs.trans ho)]
    exact ho
  · exact common_prefix_retained ho hs prev count

theorem archive_step_mono {s s' : GlobalState C} {A : List LogEntry → Prop}
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B ∧ ∀ l, A l → B l := by
  cases st with
  | append cmd leader allowed =>
    exact ⟨_, archive_step_append hr safe h _ cmd leader allowed, fun _ hl => Or.inl hl⟩
  | appendEntries he ht hp =>
    exact ⟨_, archive_step_handle_append hr safe h he ht hp, fun _ hl => hl⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr safe h (.observe hm ht) ?_, fun _ hl => hl⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn member =>
    refine ⟨A, archive_frame hr safe h (.timeout _ n hn member) ?_, fun _ hl => hl⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr safe h (.vote he ht hv) ?_, fun _ hl => hl⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc =>
    exact ⟨A, archive_frame hr safe h (.voteReply he ht hc) (by intros; rfl), fun _ hl => hl⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr safe h (.elect hc hq) ?_, fun _ hl => hl⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr safe h (.commit i hl hi ht hq) ?_, fun _ h => h⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr safe h (.replicate prev count hl hn hp) (by intros; rfl),
      fun _ hl => hl⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr safe h (.appendReply he ht hl) ?_, fun _ h => h⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv =>
    exact ⟨A, archive_frame hr safe h (.rejectVote he ht hv) (by intros; rfl), fun _ hl => hl⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr safe h (.rejectAppend he ht hp) ?_, fun _ h => h⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr safe h (.drop he) (by intros; rfl), fun _ hl => hl⟩
  | duplicate hm =>
    exact ⟨A, archive_frame hr safe h (.duplicate hm) (by intros; rfl), fun _ hl => hl⟩


theorem active_elected_log_prefix_step {s s' : GlobalState C} (hr : Reachable s)
    (safe : ElectionHistorySafe s) (step : Step s s') (t n : ℕ) (cfg : Config)
    (hn : (t, n, cfg) ∈ s.elected) (he : t = (s'.servers n).currentTerm) :
    (s.servers n).log.IsPrefix (s'.servers n).log := by
  have hb := elected_bound_reachable hr t n cfg hn
  have ht := term_step_monotone step n
  have hcurrent : (s.servers n).currentTerm = t := by omega
  cases step with
  | @appendEntries v leader tr prev pt lc entries before after hnet htr hp =>
    by_cases hv : n = v
    · subst v
      have packet : (⟨n, .appendEntries tr leader prev pt entries lc⟩ : Envelope C) ∈
          s.network := by rw [hnet]; simp
      obtain ⟨⟨cfgLeader, hleader⟩, hne⟩ := network_auth_reachable hr _ packet
      have heqt : tr = t := htr.trans hcurrent
      subst tr
      exact False.elim
        (hne (safe t n leader cfg cfgLeader hn (by simpa only [hcurrent] using hleader)))
    · simp [handleAppend, setServer, Function.update_of_ne hv]
  | _ =>
    clear safe hr hn he ht hb hcurrent
    simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader, leaderAppend,
      denyAppend, receiveAppendReply, consume, commitLeader, setServer, Function.update_apply]
    (try split_ifs) <;> simp_all [List.prefix_append]


/-- An archive also retains all earlier server snapshots of the same execution. -/
theorem execution_historical_archive (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) :
    ∃ A, ArchiveInvariant (run.state k) A ∧
      ∀ j, j ≤ k → ∀ n, A ((run.state j).servers n).log := by
  induction k with
  | zero =>
    refine ⟨fun l => l = [], ?_, ?_⟩
    · rw [run.initial]; exact archive_init
    · intro j hj n; have : j = 0 := by omega
      subst j; rw [run.initial]; rfl
  | succ k ih =>
    obtain ⟨A, hA, history⟩ := ih (by omega) (fun j hj => safe j (by omega))
    obtain ⟨B, hB, grow⟩ := archive_step_mono (run.reachable k (by omega))
      (safe k (by omega)) hA (run.transition k (by omega))
    refine ⟨B, hB, ?_⟩
    intro j hj n
    by_cases h : j = k + 1
    · subst j; exact hB.servers n
    · exact grow _ (history j (by omega) n)

/-- Historical Log Matching requires election uniqueness only before the later snapshot. -/
theorem snapshot_matching (run : Execution C) (a b k : ℕ)
    (hk : k ≤ run.length) (ha : a ≤ k) (hb : b ≤ k)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) (u v : NodeId) :
    LogMatching ((run.state a).servers u).log ((run.state b).servers v).log := by
  obtain ⟨A, hA, history⟩ := execution_historical_archive run k hk safe
  exact hA.matching _ _ (history a ha u) (history b hb v)

theorem elected_path_monotone {s s' : GlobalState C}
    (path : Relation.ReflTransGen Step s s') : s.elected ⊆ s'.elected := by
  induction path with
  | refl => exact fun _ h => h
  | tail _ st ih => exact fun _ h => elected_step_monotone st (ih h)

/-- Retirement may change the role, but cannot truncate an elected node's log in its term. -/
theorem elected_same_term_log_prefix (run : Execution C) (a b : ℕ)
    (hab : a ≤ b) (hb : b ≤ run.length)
    (safe : ∀ j, j < b → ElectionHistorySafe (run.state j))
    (t : ℕ) (n : NodeId) (cfg : Config) (he : (t, n, cfg) ∈ (run.state a).elected)
    (ht : ((run.state b).servers n).currentTerm = t) :
    ((run.state a).servers n).log.IsPrefix ((run.state b).servers n).log := by
  induction b, hab using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ b hab ih =>
    have eb := elected_path_monotone (run.path a b hab (by omega)) he
    have bound := elected_bound_reachable (run.reachable b (by omega)) t n cfg eb
    have mono := term_step_monotone (run.transition b (by omega)) n
    have mid : ((run.state b).servers n).currentTerm = t := by omega
    exact (ih (by omega) (fun j hj => safe j (by omega)) mid).trans
      (active_elected_log_prefix_step (run.reachable b (by omega)) (safe b (by omega))
        (run.transition b (by omega)) t n cfg eb ht.symm)

/-- Leader snapshots in the same term are comparable under the explicit history hypothesis. -/
theorem same_term_snapshots_comparable (run : Execution C) (a b k : ℕ)
    (hk : k ≤ run.length) (ha : a ≤ k) (hb : b ≤ k)
    (safe : ∀ j, j ≤ k → ElectionHistorySafe (run.state j)) (u v : NodeId)
    (hu : ((run.state a).servers u).role = .leader)
    (hv : ((run.state b).servers v).role = .leader)
    (ht : ((run.state a).servers u).currentTerm = ((run.state b).servers v).currentTerm) :
    ((run.state a).servers u).log.IsPrefix ((run.state b).servers v).log ∨
    ((run.state b).servers v).log.IsPrefix ((run.state a).servers u).log := by
  obtain ⟨cu, eu⟩ := leaders_covered_reachable (run.reachable a (by omega)) u hu
  obtain ⟨cv, ev⟩ := leaders_covered_reachable (run.reachable b (by omega)) v hv
  have euk := elected_path_monotone (run.path a k ha hk) eu
  have evk := elected_path_monotone (run.path b k hb hk) ev
  have heq := safe k le_rfl _ u v cu cv euk (ht ▸ evk)
  subst v
  rcases le_total a b with hab | hba
  · exact Or.inl (elected_same_term_log_prefix run a b hab (by omega)
      (fun j hj => safe j (by omega)) _ u cu eu ht.symm)
  · exact Or.inr (elected_same_term_log_prefix run b a hba (by omega)
      (fun j hj => safe j (by omega)) _ u cv ev ht)

/-- A commit index in a reachable execution is strictly positive. -/
theorem CommitEvent.positive {run : Execution C} {k : ℕ} {n : NodeId} {i : ℕ}
    (hc : CommitEvent run k n i) : 0 < i := by
  have ht := reachable_active_positive (run.reachable k (by have := hc.within; omega)) n
    (by rw [hc.leaderRole]; decide)
  have he := hc.currentTerm
  by_contra hz
  have hi : i = 0 := by omega
  simp [hi, termAt] at he
  omega

/-- Under the explicit auxiliary election-history hypothesis, every member
counted by a real commit has a prior same-term replica
snapshot of the committed prefix. Delayed acknowledgments are kept historical. -/
theorem commit_quorum_replica {run : Execution C} {k : ℕ} {leader : NodeId}
    {index : ℕ} (hc : CommitEvent run k leader index)
    (safe : ∀ j, j ≤ k → ElectionHistorySafe (run.state j)) (v : NodeId)
    (hv : v ∈ replicationQuorum (run.state k) leader index) :
    ∃ a, a ≤ k ∧
      ((run.state a).servers v).currentTerm = ((run.state k).servers leader).currentTerm ∧
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state a).servers v).log := by
  have hk : k ≤ run.length := Nat.le_of_lt hc.within
  simp only [replicationQuorum, Finset.mem_filter] at hv
  rcases hv.2 with rfl | hv
  · exact ⟨k, le_rfl, rfl, List.take_prefix _ _⟩
  obtain ⟨matched, hmatched, a, prev, pt, entries, lc, before, after,
    ha, hnet, ht, hprev, hlen, hnext⟩ :=
    match_witness run k hk leader hc.leaderRole v index hc.positive hv
  have hpacket : (⟨v, .appendEntries ((run.state k).servers leader).currentTerm
      leader prev pt entries lc⟩ : Envelope C) ∈ (run.state a).network := by
    rw [hnet]; simp
  have hw : AppendWitness run a ((run.state k).servers leader).currentTerm
      leader prev pt entries lc := network_witness run a (by omega) _ hpacket
  obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
    hsourcePrev, hsourcePt, hentries, _hcommit⟩ := hw
  let source := ((run.state sourceTime).servers leader).log
  have sourceLength : index ≤ source.length := by
    rw [hentries] at hlen
    simp only [List.length_take, List.length_drop] at hlen
    dsimp [source]
    omega
  have hcomparable := same_term_snapshots_comparable run sourceTime k k hk (by omega) le_rfl safe
    leader leader hsourceRole hc.leaderRole hsourceTerm
  have hprefix : (((run.state k).servers leader).log.take index).IsPrefix source := by
    rcases hcomparable with hs | hs
    · exact List.prefix_of_prefix_length_le (List.take_prefix _ _) hs
        (by simp only [List.length_take]; omega)
    · exact (List.take_prefix _ _).trans hs
  have hmatching := snapshot_matching run a sourceTime k hk (by omega) (by omega)
    (fun j hj => safe j (by omega)) v leader
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



def lastEntry (log : List LogEntry) : LogEntry := log.getLast?.getD ⟨0, 0, .command 0⟩

theorem lastEntry_mem {log : List LogEntry} (h : log ≠ []) : lastEntry log ∈ log := by
  simp only [lastEntry, List.getLast?_eq_some_getLast h, Option.getD_some]
  exact List.getLast_mem h

theorem lastTerm_lastEntry (log : List LogEntry) : lastTerm log = (lastEntry log).term := by
  unfold lastTerm lastEntry
  cases log.getLast? <;> rfl

theorem lastIndex_lastEntry (log : List LogEntry) : lastIndex log = (lastEntry log).index := by
  unfold lastIndex lastEntry
  cases log.getLast? <;> rfl

structure WellFormed (log : List LogEntry) : Prop where
  indexed : ∀ (i : ℕ) (hi : i < log.length), (log[i]).index = i + 1
  positive_terms : ∀ e ∈ log, 0 < e.term
  unique_index : ∀ a ∈ log, ∀ b ∈ log, a.index = b.index → a = b
  last_bounds : ∀ e ∈ log, e.index ≤ lastIndex log ∧ e.term ≤ lastTerm log
  term_order : ∀ a ∈ log, ∀ b ∈ log, a.term < b.term → a.index < b.index
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
    (hr : Reachable s) (safe : ElectionHistorySafe s) (h : ArchiveInvariant s A)
    (ho : ∀ l, A l → OrderedPositive l) (st : Step s s') :
    ∃ B, ArchiveInvariant s' B ∧ ∀ l, B l → OrderedPositive l := by
  cases st with
  | @append n cmd leader allowed =>
    refine ⟨_, archive_step_append hr safe h n cmd leader allowed, ?_⟩
    intro l hl
    rcases hl with hl | hl
    · exact ho l hl
    · apply OrderedPositive.prefix _ hl
      apply (ho _ (h.servers n)).append
      · exact reachable_log_bound hr n
      · exact reachable_active_positive hr n (by simp [leader])
  | appendEntries he ht hp =>
    exact ⟨A, archive_step_handle_append hr safe h he ht hp, ho⟩
  | observe hm ht =>
    refine ⟨A, archive_frame hr safe h (.observe hm ht) ?_, ho⟩
    intro n
    simp only [observeTerm, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | timeout n hn member =>
    refine ⟨A, archive_frame hr safe h (.timeout _ n hn member) ?_, ho⟩
    intro node
    simp only [startElection, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | vote he ht hv =>
    refine ⟨A, archive_frame hr safe h (.vote he ht hv) ?_, ho⟩
    intro n
    simp only [grantVote, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | voteReply he ht hc =>
    exact ⟨A, archive_frame hr safe h (.voteReply he ht hc) (by intros; rfl), ho⟩
  | elect hc hq =>
    refine ⟨A, archive_frame hr safe h (.elect hc hq) ?_, ho⟩
    intro n
    simp only [becomeLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | commit i hl hi ht hq =>
    refine ⟨A, archive_frame hr safe h (.commit i hl hi ht hq) ?_, ho⟩
    intro n
    simp only [commitLeader, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | replicate prev count hl hn hp =>
    exact ⟨A, archive_frame hr safe h (.replicate prev count hl hn hp) (by intros; rfl), ho⟩
  | appendReply he ht hl =>
    refine ⟨A, archive_frame hr safe h (.appendReply he ht hl) ?_, ho⟩
    intro n
    simp only [receiveAppendReply, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | rejectVote he ht hv =>
    exact ⟨A, archive_frame hr safe h (.rejectVote he ht hv) (by intros; rfl), ho⟩
  | rejectAppend he ht hp =>
    refine ⟨A, archive_frame hr safe h (.rejectAppend he ht hp) ?_, ho⟩
    intro n
    simp only [denyAppend, setServer, Function.update_apply]
    split_ifs <;> simp_all
  | drop he => exact ⟨A, archive_frame hr safe h (.drop he) (by intros; rfl), ho⟩
  | duplicate hm => exact ⟨A, archive_frame hr safe h (.duplicate hm) (by intros; rfl), ho⟩


/-- Positive ordered logs, with the election-history dependency exposed. -/
theorem execution_ordered_archive (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) :
    ∃ A, ArchiveInvariant (run.state k) A ∧ ∀ l, A l → OrderedPositive l := by
  induction k with
  | zero =>
    rw [run.initial]
    refine ⟨_, archive_init, ?_⟩
    intro l hl; subst l; constructor <;> simp
  | succ k ih =>
    obtain ⟨A, hA, hO⟩ := ih (by omega) (fun j hj => safe j (by omega))
    exact ordered_archive_step (run.reachable k (by omega)) (safe k (by omega)) hA hO
      (run.transition k (by omega))

theorem execution_entry_index (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j))
    (n : NodeId) (i : ℕ) (e : LogEntry) (he : ((run.state k).servers n).log[i]? = some e) :
    e.index = i + 1 := by
  obtain ⟨A, hA⟩ := execution_archive run k hk safe
  obtain ⟨owner, cfg, _record, _length, before, creator, cmd,
    _hr, _role, _guard, hi, entry, _path⟩ :=
    hA.origin _ (hA.servers n) i e he
  rw [entry, hi]
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
    · rw [lastIndex_lastEntry]
      rw [hlastEq, hi i hilen, hi (log.length - 1) hlast]
      omega
    · rw [lastTerm_lastEntry]
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


theorem execution_wellFormed (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) (n : NodeId) :
    WellFormed ((run.state k).servers n).log := by
  obtain ⟨A, hA, hO⟩ := execution_ordered_archive run k hk safe
  apply wellFormed_of_ordered_indexed (hO _ (hA.servers n))
  intro i hi
  exact execution_entry_index run k hk safe n i _ (List.getElem?_eq_getElem hi)
/-- One-based consecutive indices identify the last index with the list length. -/
theorem wellFormed_lastIndex_eq_length {log : List LogEntry} (hw : WellFormed log) :
    lastIndex log = log.length := by
  by_cases hn : log = []
  · subst log; rfl
  · have hp := List.length_pos_iff.mpr hn
    have hl : log.length - 1 < log.length := by omega
    rw [lastIndex_lastEntry]
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

/-- Historical source snapshots of currently acceptable deliveries are comparable
with the protected prefix. This is an auxiliary proof premise, never a Step guard. -/
def ComparableSourcesAt (run : Execution C) (i : ℕ) (v : NodeId)
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

theorem voter_prefix_step (run : Execution C) (i : ℕ) (v : NodeId) (p : List LogEntry)
    (hp : p.IsPrefix ((run.state i).servers v).log)
    (sources : ComparableSourcesAt run i v p)
    (st : Step (run.state i) (run.state (i + 1))) :
    p.IsPrefix ((run.state (i + 1)).servers v).log := by
  generalize he : run.state (i + 1) = next at st ⊢
  cases st with
  | @append n cmd hn allowed =>
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
    (hb : b ≤ run.length) (v : NodeId) (p : List LogEntry)
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


/-- Every election record is backed by its actual candidate and quorum snapshot. -/
theorem election_record_origin (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (t node : ℕ) (cfg : Config) (he : (t, node, cfg) ∈ (run.state k).elected) :
    ∃ j, j < k ∧ ((run.state j).servers node).role = .candidate ∧
      t = ((run.state j).servers node).currentTerm ∧
      cfg = active ((run.state j).servers node) ∧
      has_quorum (eligibleVotes (run.state j) node) (active ((run.state j).servers node)) ∧
      run.state (j + 1) = becomeLeader (run.state j) node := by
  induction k with
  | zero => rw [run.initial] at he; simp [initState] at he
  | succ k ih =>
    have st := run.transition k (by omega)
    generalize hn : run.state (k + 1) = next at st he
    cases st with
    | @elect n hc hq =>
      simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl, rfl⟩ | he
      · exact ⟨k, by omega, hc, rfl, rfl, hq, hn⟩
      · obtain ⟨j, hj, rest⟩ := ih (by omega) he
        exact ⟨j, by omega, rest⟩
    | _ =>
      obtain ⟨j, hj, rest⟩ := ih (by omega) he
      exact ⟨j, by omega, rest⟩

/-- No first-term election can use a genuinely new stable configuration. -/
theorem first_term_elected_config {s : GlobalState C} (hr : Reachable s)
    (node : ℕ) (cfg : Config) (he : (1, node, cfg) ∈ s.elected) :
    cfg = C.initial ∨ cfg = C.jointConfig := by
  rcases elected_config_reachable hr 1 node cfg he with hi | hj | hn
  · exact Or.inl hi
  · exact Or.inr hj
  · by_cases hsame : C.initial = C.finalConfig
    · exact Or.inl (hn.trans hsame.symm)
    · obtain ⟨run, hend⟩ := reachable_execution hr
      obtain ⟨j, hj, hc, ht, ha, _hq, _hnext⟩ :=
        election_record_origin run run.length le_rfl 1 node cfg (hend ▸ he)
      obtain ⟨created, owner, a, committer, bound, _hac, _hcj, event, hterm, _hjoint⟩ :=
        new_candidate_has_earlier_commit run j (by omega) node hc (ha.symm.trans hn) hsame
      have hpositive := reachable_active_positive (run.reachable a event.within.le)
        committer (by rw [event.leaderRole]; decide)
      omega

/-- The base case of a term-stratified safety proof, for all configuration pairs. -/
theorem first_term_election_safety {s : GlobalState C} (hr : Reachable s)
    {a b : ℕ} {cfgA cfgB : Config}
    (ha : (1, a, cfgA) ∈ s.elected) (hb : (1, b, cfgB) ∈ s.elected) : a = b := by
  rcases first_term_elected_config hr a cfgA ha with rfl | rfl <;>
    rcases first_term_elected_config hr b cfgB hb with rfl | rfl
  · exact same_configuration_election_safety hr ha hb
  · exact old_joint_election_safety hr ha hb
  · exact (old_joint_election_safety hr hb ha).symm
  · exact same_configuration_election_safety hr ha hb

/-- A node cannot return to candidacy in a term in which it has already been elected.
Unlike leader tenure, this remains valid after retirement. -/
def ElectedNotCandidate (s : GlobalState C) : Prop :=
  ∀ t n cfg, (t, n, cfg) ∈ s.elected → (s.servers n).currentTerm = t →
    (s.servers n).role ≠ .candidate

theorem elected_not_candidate_step {s s' : GlobalState C} (hr : Reachable s)
    (h : ElectedNotCandidate s) (st : Step s s') : ElectedNotCandidate s' := by
  have old : ∀ t n cfg, (t, n, cfg) ∈ s.elected → (s'.servers n).currentTerm = t →
      (s'.servers n).role ≠ .candidate := by
    intro t n cfg he ht
    have hb := elected_bound_reachable hr t n cfg he
    have hm := term_step_monotone st n
    have mid : (s.servers n).currentTerm = t := by omega
    have hn := h t n cfg he mid
    clear h he hr
    cases st <;>
      simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
        leaderAppend, handleAppend, denyAppend, receiveAppendReply, consume, commitLeader,
        setServer, Function.update_apply] at ht ⊢ <;>
      (try split_ifs at ht ⊢) <;> simp_all
  cases st <;> try exact old
  case elect n hc hq =>
    intro t v cfg he ht
    simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at he
    rcases he with ⟨rfl, rfl, rfl⟩ | he
    · simp [becomeLeader, setServer]
    · exact old t v cfg he ht

theorem elected_not_candidate_reachable {s : GlobalState C} (hr : Reachable s) :
    ElectedNotCandidate s := by
  induction hr with
  | init => simp [ElectedNotCandidate, initState]
  | step hr st ih => exact elected_not_candidate_step hr ih st

theorem no_leader_before_election (run : Execution C) (election : ℕ)
    (helection : election < run.length)
    (safe : ElectionHistorySafe (run.state (election + 1))) (candidate : NodeId)
    (hcandidate : ((run.state election).servers candidate).role = .candidate)
    (hnext : run.state (election + 1) = becomeLeader (run.state election) candidate)
    (j : ℕ) (hj : j ≤ election) (n : NodeId)
    (hrole : ((run.state j).servers n).role = .leader) :
    ((run.state j).servers n).currentTerm ≠
      ((run.state election).servers candidate).currentTerm := by
  intro ht
  obtain ⟨cfg, ej⟩ := leaders_covered_reachable (run.reachable j (by omega)) n hrole
  have ee := elected_path_monotone (run.path j election hj (by omega)) ej
  have en := elected_path_monotone (run.path election (election + 1) (by omega)
    (by omega)) ee
  have ec : (((run.state election).servers candidate).currentTerm, candidate,
      active ((run.state election).servers candidate)) ∈
      (run.state (election + 1)).elected := by rw [hnext]; simp [becomeLeader]
  have eqn : n = candidate := safe _ n candidate cfg _ en (ht ▸ ec)
  subst n
  exact elected_not_candidate_reachable (run.reachable election (by omega)) _ candidate cfg
    ee ht.symm hcandidate

def logUpToDate (candidate voter : List LogEntry) : Prop :=
  lastTerm voter < lastTerm candidate ∨
    (lastTerm candidate = lastTerm voter ∧ lastIndex voter ≤ lastIndex candidate)
theorem CommitEvent.anchor {run : Execution C} {k : ℕ} {n : NodeId} {index : ℕ}
    (hc : CommitEvent run k n index)
    (safe : ∀ j, j < k → ElectionHistorySafe (run.state j)) :
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
  have hind := execution_entry_index run k (Nat.le_of_lt hc.within) safe n _ e he
  refine ⟨e, hm, by omega, ?_⟩
  have ht := hc.currentTerm
  simpa only [termAt, Nat.ne_of_gt hpos, ↓reduceIte, he, Option.getD_some] using ht

/-- Up-to-Date transfers the commit prefix using origin and historical matching.
Strictly newer last terms use the induction hypothesis for earlier leaders. -/
theorem candidate_prefix_of_upToDate (run : Execution C) (k : ℕ) (leader : NodeId)
    (index : ℕ) (hc : CommitEvent run k leader index)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (election : ℕ) (helection : election ≤ run.length) (candidate : NodeId)
    (hcandidate : ((run.state election).servers candidate).role = .candidate)
    (b : ℕ) (hb : b ≤ run.length) (v : NodeId)
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
  obtain ⟨anchor, hanchor, haindex, haterm⟩ :=
    hc.anchor (fun j hj => safe j (by have := hc.within; omega))
  have hvanchor : anchor ∈ vLog := hp.sublist.subset hanchor
  have wfv := execution_wellFormed run b hb (fun z hz => safe z (by omega)) v
  have wfc := execution_wellFormed run election helection (fun z hz => safe z (by omega)) candidate
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
    have hz : lastTerm cLog = 0 := by simp [he, lastTerm]
    omega
  have hlast : lastEntry cLog ∈ cLog := lastEntry_mem hcne
  obtain ⟨originTime, horiginTime, owner, hownerRole, hownerTerm, hownerEntry⟩ :=
    trace_record_origin run election helection candidate (lastEntry cLog) hlast
  have hoend : originTime ≤ run.length := by omega
  have wfo := execution_wellFormed run originTime hoend (fun z hz => safe z (by omega)) owner
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
        (by simpa only [lastIndex_lastEntry] using wellFormed_lastIndex_eq_length wfc)
      have hindexBound := (wfo.last_bounds _ hownerEntry).1
      rw [wellFormed_lastIndex_eq_length wfo, hlastIndex] at hindexBound
      have compare := same_term_snapshots_comparable run originTime k run.length le_rfl hoend
        (Nat.le_of_lt hc.within) safe owner leader hownerRole hc.leaderRole
        (hownerTerm.trans ((lastTerm_lastEntry cLog).symm.trans heq.symm))
      rcases compare with h | h
      · exact List.prefix_of_prefix_length_le (List.take_prefix _ _) h (by omega)
      · exact (List.take_prefix _ _).trans h
    · apply earlier originTime hoend owner hownerRole _ hupper
      rw [hownerTerm]
      rw [← lastTerm_lastEntry]
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
      rw [← lastTerm_lastEntry] at heq
      have hpl := hp.length_le
      change p.length ≤ vLog.length at hpl
      change lastIndex cLog = cLog.length at hci
      change lastIndex vLog = vLog.length at hvi
      rw [← lastIndex_lastEntry]
      rcases hup with h | ⟨_, hlen⟩ <;> omega
    · have htne : anchor.term ≠ lastTerm cLog := by simpa only [lastTerm_lastEntry] using heq
      have hord := wfo.term_order anchor hanchorOrigin _ hownerEntry
        (by rw [← lastTerm_lastEntry]; rw [haterm] at htne ⊢; omega)
      omega
  exact matching_transfers_prefix wfo wfc
    (snapshot_matching run originTime election run.length le_rfl hoend helection
      (fun z hz => safe z hz.le) owner candidate)
    hpOrigin _ _ hownerEntry hlast rfl rfl hposition


/-- A counted ballot supplies a same-execution voter snapshot satisfying the
actual comparison rule against the candidate's unchanged campaign log. -/
theorem winning_voter_snapshot (run : Execution C) (election : ℕ)
    (helection : election ≤ run.length) (c : NodeId)
    (hc : ((run.state election).servers c).role = .candidate) (v : NodeId)
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


theorem leader_election_witness (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (c : NodeId) (hc : ((run.state k).servers c).role = .leader) :
    ∃ i, i < k ∧ ((run.state i).servers c).role = .candidate ∧
      ((run.state k).servers c).currentTerm = ((run.state i).servers c).currentTerm ∧
      has_quorum (eligibleVotes (run.state i) c) (active ((run.state i).servers c)) ∧
      run.state (i + 1) = becomeLeader (run.state i) c := by
  obtain ⟨cfg, he⟩ := leaders_covered_reachable (run.reachable k hk) c hc
  obtain ⟨i, hi, hc, ht, _cfg, hq, hn⟩ := election_record_origin run k hk _ c cfg he
  exact ⟨i, hi, hc, ht, hq, hn⟩
/-- Auxiliary strong induction with an explicit election-safety hypothesis.
This is not unconditional Leader Completeness. The joint commit quorum and
winning vote quorum intersect in a real replica and a real later vote event. -/
theorem joint_commit_prefix_in_later_leader_aux (run : Execution C) (k : ℕ)
    (leader : NodeId) (index : ℕ) (hc : CommitEvent run k leader index)
    (joint : active ((run.state k).servers leader) = C.jointConfig)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j)) :
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
    have commitQuorum : has_quorum (replicationQuorum (run.state k) leader index)
        C.jointConfig := joint ▸ hc.quorum
    obtain ⟨v, hv⟩ := joint_quorum_intersects_any_allowed commitQuorum hmajority
      (active_config_reachable (run.reachable election electionEnd) n)
    obtain ⟨hvCommit, hvVote⟩ := Finset.mem_inter.mp hv
    have hvBallot : v ∈ votesFor (run.state election).received
        ((run.state election).servers n).currentTerm n := (Finset.mem_inter.mp hvVote).1
    obtain ⟨a, ha, hat, hap⟩ :=
      commit_quorum_replica hc
        (fun z hz => safe z (by have := hc.within; omega)) v hvCommit
    obtain ⟨b, hb, hbt, hup⟩ :=
      winning_voter_snapshot run election electionEnd n hcandidate v hvBallot
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
        have hw : AppendWitness run i t sender prev pt entries lc :=
          network_witness run i hiEnd _ packet
        obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries, _hlc⟩ := hw
        refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries, ?_⟩
        have sourceEnd : sourceTime ≤ run.length := by omega
        have low := term_path_monotone (run.path a i hai hiEnd) v
        have high := term_path_monotone (run.path i b (by omega) bEnd) v
        rw [hat, ← ht] at low
        rw [← ht, hbt] at high
        have hne := no_leader_before_election run election (by omega)
          (safe (election + 1) (by omega)) n hcandidate
          hnext sourceTime (by omega) sender hsourceRole
        have strictHigh : ((run.state sourceTime).servers sender).currentTerm <
            ((run.state election).servers n).currentTerm := by
          rw [hsourceTerm] at hne ⊢
          omega
        by_cases heq : t = ((run.state k).servers leader).currentTerm
        · have comparable :=
            same_term_snapshots_comparable run sourceTime k run.length le_rfl sourceEnd
            (Nat.le_of_lt hc.within) safe sender leader hsourceRole hc.leaderRole
            (hsourceTerm.trans heq)
          rcases comparable with h | h
          · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
          · exact Or.inr ((List.take_prefix _ _).trans h)
        · exact Or.inr (earlier sourceTime sourceEnd sender hsourceRole
            (by rw [hsourceTerm]; omega) strictHigh))
    have candidatePrefix := candidate_prefix_of_upToDate run k leader index hc safe
      election electionEnd n hcandidate b bEnd v voterPrefix hup earlier
    have postElection : ((run.state (election + 1)).servers n).role = .leader := by
      rw [hnext]; simp [becomeLeader, setServer]
    have postTerm : ((run.state (election + 1)).servers n).currentTerm = u := by
      rw [hnext]; simpa [becomeLeader, setServer] using electionTerm
    obtain ⟨cfg, elected⟩ := leaders_covered_reachable
      (run.reachable (election + 1) (by omega)) n postElection
    have hfinalPrefix := elected_same_term_log_prefix run (election + 1) j (by omega) hj
      (fun z hz => safe z (by omega)) u n cfg (by simpa only [postTerm] using elected) hnt
    apply List.IsPrefix.trans _ hfinalPrefix
    simpa only [hnext, becomeLeader, setServer, Function.update_self] using candidatePrefix



/-- A joint prefix is already in a quorum-backed campaign log before the election step.
Only election safety in the supplied (pre-election) execution is assumed. In-flight
messages from earlier leaders of the candidate's own term are handled explicitly. -/
theorem joint_prefix_in_candidate_aux (run : Execution C) (k : ℕ)
    (leader : NodeId) (index : ℕ) (hc : CommitEvent run k leader index)
    (joint : active ((run.state k).servers leader) = C.jointConfig)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (election : ℕ) (electionEnd : election ≤ run.length) (n : NodeId)
    (hcandidate : ((run.state election).servers n).role = .candidate)
    (hmajority : has_quorum (eligibleVotes (run.state election) n)
      (active ((run.state election).servers n)))
    (htu : ((run.state k).servers leader).currentTerm <
      ((run.state election).servers n).currentTerm) :
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state election).servers n).log := by
  have commitQuorum : has_quorum (replicationQuorum (run.state k) leader index)
      C.jointConfig := joint ▸ hc.quorum
  obtain ⟨v, hv⟩ := joint_quorum_intersects_any_allowed commitQuorum hmajority
    (active_config_reachable (run.reachable election electionEnd) n)
  obtain ⟨hvCommit, hvVote⟩ := Finset.mem_inter.mp hv
  have hvBallot : v ∈ votesFor (run.state election).received
      ((run.state election).servers n).currentTerm n := (Finset.mem_inter.mp hvVote).1
  obtain ⟨a, ha, hat, hap⟩ :=
    commit_quorum_replica hc
      (fun z hz => safe z (by have := hc.within; omega)) v hvCommit
  obtain ⟨b, hb, hbt, hup⟩ :=
    winning_voter_snapshot run election electionEnd n hcandidate v hvBallot
  have aEnd : a ≤ run.length := by have := hc.within; omega
  have bEnd : b ≤ run.length := by omega
  have hab : a ≤ b := by
    by_contra h
    have mono := term_path_monotone (run.path b a (by omega) aEnd) v
    rw [hat, hbt] at mono
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
    exact joint_commit_prefix_in_later_leader_aux run k leader index hc joint safe
      _ hlow z hz owner hrole rfl
  have voterPrefix := voter_prefix_retained run a b hab bEnd v
    (((run.state k).servers leader).log.take index) hap (by
      intro i hai hib t sender prev pt entries lc packet ht
      have hiEnd : i ≤ run.length := by omega
      have hw : AppendWitness run i t sender prev pt entries lc :=
        network_witness run i hiEnd _ packet
      obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
        hsourcePrev, hsourcePt, hentries, _hlc⟩ := hw
      refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
        hsourcePrev, hsourcePt, hentries, ?_⟩
      have sourceEnd : sourceTime ≤ run.length := by omega
      have low := term_path_monotone (run.path a i hai hiEnd) v
      have high := term_path_monotone (run.path i b (by omega) bEnd) v
      rw [hat, ← ht] at low
      rw [← ht, hbt] at high
      by_cases heq : t = ((run.state k).servers leader).currentTerm
      · have comparable :=
          same_term_snapshots_comparable run sourceTime k run.length le_rfl sourceEnd
          (Nat.le_of_lt hc.within) safe sender leader hsourceRole hc.leaderRole
          (hsourceTerm.trans heq)
        rcases comparable with h | h
        · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
        · exact Or.inr ((List.take_prefix _ _).trans h)
      · exact Or.inr (joint_commit_prefix_in_later_leader_aux run k leader index hc joint safe
          t (by omega) sourceTime sourceEnd sender hsourceRole hsourceTerm))
  have candidatePrefix := candidate_prefix_of_upToDate run k leader index hc safe
    election electionEnd n hcandidate b bEnd v voterPrefix hup earlier
  exact candidatePrefix

/-- With distinct old and new memberships, any surviving configuration entry
prevents a log from activating the initial configuration. -/
theorem config_entry_excludes_initial (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (n : NodeId) (e : LogEntry) (he : e ∈ ((run.state k).servers n).log)
    (cfg : Config) (hc : e.payload = .config cfg) (hne : C.initial ≠ C.finalConfig) :
    active ((run.state k).servers n) ≠ C.initial := by
  have notInitial : ∀ x ∈ ((run.state k).servers n).log, ∀ c,
      x.payload = .config c → c ≠ C.initial := by
    intro x hx c hp
    rcases log_config_origin run k hk n x hx c hp with rfl | rfl
    · simp [Transition.jointConfig, Transition.initial]
    · exact Ne.symm hne
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp he
  change active_config ((run.state k).servers n).log C.initial ≠ C.initial
  rw [hsplit, active_config_append]
  have hpost : active_config post cfg ≠ C.initial := by
    intro heq
    rcases active_config_origin post cfg with hd | ⟨x, hx, hp⟩
    · exact notInitial e he cfg hc (hd.symm.trans heq)
    · exact notInitial x (by rw [hsplit]; simp [hx]) _ hp heq
  simpa only [active_config, List.foldl_cons, hc] using hpost

/-- A concrete joint commit forbids a later-term old-only quorum-backed candidate,
under the explicit prior-history hypothesis. No old/new intersection is claimed. -/
theorem joint_commit_blocks_old_candidate_aux (run : Execution C) (k : ℕ)
    (leader : NodeId) (index : ℕ) (hc : CommitEvent run k leader index)
    (joint : active ((run.state k).servers leader) = C.jointConfig)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (he : ∃ e ∈ (((run.state k).servers leader).log.take index),
      e.payload = .config C.jointConfig)
    (hne : C.initial ≠ C.finalConfig)
    (election : ℕ) (hEnd : election ≤ run.length) (n : NodeId)
    (hCand : ((run.state election).servers n).role = .candidate)
    (hq : has_quorum (eligibleVotes (run.state election) n)
      (active ((run.state election).servers n)))
    (ht : ((run.state k).servers leader).currentTerm <
      ((run.state election).servers n).currentTerm) :
    active ((run.state election).servers n) ≠ C.initial := by
  have hp := joint_prefix_in_candidate_aux run k leader index hc joint safe
    election hEnd n hCand hq ht
  obtain ⟨e, he, hcfg⟩ := he
  exact config_entry_excludes_initial run election hEnd n e (hp.mem he) C.jointConfig hcfg hne

/-- The same operational completeness argument for any real commit whose quorum
intersects later successful campaigns. Intersection remains an explicit proof
obligation here; it is not added to the protocol's election rule. -/
theorem commit_prefix_with_intersecting_elections_aux (run : Execution C) (k : ℕ)
    (leader : NodeId) (index : ℕ) (hc : CommitEvent run k leader index)
    (intersects : ∀ election, election ≤ run.length → ∀ candidate,
      ((run.state election).servers candidate).role = .candidate →
      has_quorum (eligibleVotes (run.state election) candidate)
        (active ((run.state election).servers candidate)) →
      ((run.state k).servers leader).currentTerm <
        ((run.state election).servers candidate).currentTerm →
      (replicationQuorum (run.state k) leader index ∩
        eligibleVotes (run.state election) candidate).Nonempty)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j)) :
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
    obtain ⟨v, hv⟩ := intersects election electionEnd n hcandidate hmajority
      (by rw [electionTerm]; exact htu)
    obtain ⟨hvCommit, hvVote⟩ := Finset.mem_inter.mp hv
    have hvBallot : v ∈ votesFor (run.state election).received
        ((run.state election).servers n).currentTerm n := (Finset.mem_inter.mp hvVote).1
    obtain ⟨a, ha, hat, hap⟩ :=
      commit_quorum_replica hc
        (fun z hz => safe z (by have := hc.within; omega)) v hvCommit
    obtain ⟨b, hb, hbt, hup⟩ :=
      winning_voter_snapshot run election electionEnd n hcandidate v hvBallot
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
        have hw : AppendWitness run i t sender prev pt entries lc :=
          network_witness run i hiEnd _ packet
        obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries, _hlc⟩ := hw
        refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
          hsourcePrev, hsourcePt, hentries, ?_⟩
        have sourceEnd : sourceTime ≤ run.length := by omega
        have low := term_path_monotone (run.path a i hai hiEnd) v
        have high := term_path_monotone (run.path i b (by omega) bEnd) v
        rw [hat, ← ht] at low
        rw [← ht, hbt] at high
        have hne := no_leader_before_election run election (by omega)
          (safe (election + 1) (by omega)) n hcandidate
          hnext sourceTime (by omega) sender hsourceRole
        have strictHigh : ((run.state sourceTime).servers sender).currentTerm <
            ((run.state election).servers n).currentTerm := by
          rw [hsourceTerm] at hne ⊢
          omega
        by_cases heq : t = ((run.state k).servers leader).currentTerm
        · have comparable :=
            same_term_snapshots_comparable run sourceTime k run.length le_rfl sourceEnd
            (Nat.le_of_lt hc.within) safe sender leader hsourceRole hc.leaderRole
            (hsourceTerm.trans heq)
          rcases comparable with h | h
          · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
          · exact Or.inr ((List.take_prefix _ _).trans h)
        · exact Or.inr (earlier sourceTime sourceEnd sender hsourceRole
            (by rw [hsourceTerm]; omega) strictHigh))
    have candidatePrefix := candidate_prefix_of_upToDate run k leader index hc safe
      election electionEnd n hcandidate b bEnd v voterPrefix hup earlier
    have postElection : ((run.state (election + 1)).servers n).role = .leader := by
      rw [hnext]; simp [becomeLeader, setServer]
    have postTerm : ((run.state (election + 1)).servers n).currentTerm = u := by
      rw [hnext]; simpa [becomeLeader, setServer] using electionTerm
    obtain ⟨cfg, elected⟩ := leaders_covered_reachable
      (run.reachable (election + 1) (by omega)) n postElection
    have hfinalPrefix := elected_same_term_log_prefix run (election + 1) j (by omega) hj
      (fun z hz => safe z (by omega)) u n cfg (by simpa only [postTerm] using elected) hnt
    apply List.IsPrefix.trans _ hfinalPrefix
    simpa only [hnext, becomeLeader, setServer, Function.update_self] using candidatePrefix

/-- Auxiliary completeness premise used to separate content provenance from the
remaining mutual induction. This is not an invariant supplied to `Step`. -/
def CommitLeaderPrefixes (run : Execution C) (ceiling : ℕ) : Prop :=
  ∀ a owner bound, CommitEvent run a owner bound →
    ∀ b, b ≤ run.length → ∀ leader,
      ((run.state b).servers leader).role = .leader →
      ((run.state b).servers leader).currentTerm ≤ ceiling →
      ((run.state a).servers owner).currentTerm <
        ((run.state b).servers leader).currentTerm →
      (((run.state a).servers owner).log.take bound).IsPrefix
        ((run.state b).servers leader).log

/-- A content witness names a real commit on this execution, its current-term
anchor and quorum, and the exact local prefix. The inherited prefix may be
shorter than the original commit, as happens with partial AppendEntries batches. -/
def HistoricalCommitPrefix (run : Execution C) (k node index : ℕ) : Prop :=
  ∃ a owner bound, a < k ∧ CommitEvent run a owner bound ∧ index ≤ bound ∧
    (((run.state a).servers owner).log.take index).IsPrefix
      ((run.state k).servers node).log ∧
    ((run.state a).servers owner).currentTerm ≤ ((run.state k).servers node).currentTerm

/-- Preserve even a partial inherited prefix. The explicit term lower bound is
necessary: a short prefix need not contain the original current-term anchor. -/
theorem committed_subprefix_retained_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (ceiling : ℕ) (complete : CommitLeaderPrefixes run ceiling)
    (k owner bound : ℕ) (hc : CommitEvent run k owner bound)
    (index : ℕ) (hi : index ≤ bound)
    (a b : ℕ) (hab : a ≤ b) (hb : b ≤ run.length) (node : NodeId)
    (hp : (((run.state k).servers owner).log.take index).IsPrefix
      ((run.state a).servers node).log)
    (hupper : ((run.state b).servers node).currentTerm ≤ ceiling)
    (ht : ((run.state k).servers owner).currentTerm ≤
      ((run.state a).servers node).currentTerm) :
    (((run.state k).servers owner).log.take index).IsPrefix
      ((run.state b).servers node).log := by
  apply voter_prefix_retained run a b hab hb node _ hp
  intro i hai hib t sender prev pt entries lc packet heq
  obtain ⟨sourceTime, count, hsourceTime, hrole, hterm, hprev, hpt, hentries, _hlc⟩ :=
    (network_witness run i (by omega) _ packet :
      AppendWitness run i t sender prev pt entries lc)
  refine ⟨sourceTime, count, hsourceTime, hrole, hterm, hprev, hpt, hentries, ?_⟩
  have sourceEnd : sourceTime ≤ run.length := by omega
  have lower := term_path_monotone (run.path a i hai (by omega)) node
  rw [← heq] at lower
  have upper := term_path_monotone (run.path i b (by omega) hb) node
  have sourceUpper : ((run.state sourceTime).servers sender).currentTerm ≤ ceiling := by
    rw [hterm, heq]; omega
  by_cases same : t = ((run.state k).servers owner).currentTerm
  · have comparable := same_term_snapshots_comparable run sourceTime k run.length le_rfl
      sourceEnd (Nat.le_of_lt hc.within) safe sender owner hrole hc.leaderRole
      (hterm.trans same)
    rcases comparable with h | h
    · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
    · exact Or.inr ((List.take_prefix _ _).trans h)
  · have small : (((run.state k).servers owner).log.take index).IsPrefix
        (((run.state k).servers owner).log.take bound) := by
      simpa only [List.take_take, Nat.min_eq_left hi] using
        List.take_prefix index (((run.state k).servers owner).log.take bound)
    exact Or.inr (small.trans
      (complete k owner bound hc sourceTime sourceEnd sender hrole sourceUpper
        (by rw [hterm]; omega)))


/-- Content-sensitive origin of local commit indices, conditional only at this
auxiliary stage on the global completeness and election-history obligations.
In particular the AppendEntries case installs a prefix from the actual sender
snapshot; it does not treat a numeric leaderCommit as a proof of its contents. -/
theorem commit_index_content_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (ceiling : ℕ) (complete : CommitLeaderPrefixes run ceiling)
    (k : ℕ) (hk : k ≤ run.length) (node index : ℕ) (hp : 0 < index)
    (hi : index ≤ ((run.state k).servers node).commitIndex)
    (hupper : ((run.state k).servers node).currentTerm ≤ ceiling) :
    HistoricalCommitPrefix run k node index := by
  induction k using Nat.strong_induction_on generalizing node with
  | h k ih =>
    cases k with
    | zero => rw [run.initial] at hi; simp [initState] at hi; omega
    | succ k =>
      have st := run.transition k (by omega)
      have mono := term_step_monotone st node
      have old : index ≤ ((run.state k).servers node).commitIndex →
          HistoricalCommitPrefix run (k + 1) node index := by
        intro hindex
        obtain ⟨a, owner, bound, ha, hc, hbound, hprefix, hterm⟩ :=
          ih k (by omega) (by omega) node hindex (by omega)
        exact ⟨a, owner, bound, by omega, hc, hbound,
          committed_subprefix_retained_aux run safe ceiling complete a owner bound hc index hbound
            k (k + 1) (by omega) hk node hprefix hupper hterm, hterm.trans mono⟩
      generalize he : run.state (k + 1) = next at st hi mono ⊢
      cases st with
      | @commit leader bound hrole hlen hterm hquorum =>
        by_cases hn : node = leader
        · subst node
          simp only [commitLeader, setServer, Function.update_self] at hi
          rcases le_max_iff.mp hi with hold | hbound
          · exact old hold
          · refine ⟨k, leader, bound, by omega,
              ⟨by omega, hrole, hlen, hterm, hquorum, he⟩, hbound, ?_, ?_⟩
            · rw [he]; simpa only [commitLeader, setServer, Function.update_self] using
                List.take_prefix index ((run.state k).servers leader).log
            · rw [he]; simp [commitLeader, setServer]
        · apply old
          simpa [commitLeader, setServer, Function.update_of_ne hn] using hi
      | @appendEntries v leader t prev pt lc entries before after hnet ht hprev =>
        by_cases hn : node = v
        · subst node
          simp only [handleAppend, setServer, Function.update_self] at hi
          rcases le_max_iff.mp hi with hold | hincoming
          · exact old hold
          · have packet : (⟨v, .appendEntries t leader prev pt entries lc⟩ : Envelope C) ∈
                (run.state k).network := by rw [hnet]; simp
            obtain ⟨j, count, hj, _hrole, hjt, hlen, hpt, hentries, hlc⟩ :=
              (network_witness run k (by omega) _ packet :
                AppendWitness run k t leader prev pt entries lc)
            have hindex : index ≤ ((run.state j).servers leader).commitIndex := by
              rw [← hlc]; exact (le_min_iff.mp hincoming).1
            obtain ⟨a, owner, bound, ha, hc, hb, hprefix, hat⟩ :=
              ih j (by omega) (by omega) leader hindex (by
                rw [hjt, ht]
                exact le_trans mono (he ▸ hupper))
            have install := covered_prefix_installed hprefix
              (snapshot_matching run k j k (by omega) le_rfl hj
                (fun z hz => safe z (by omega)) v leader)
              prev count hlen (hpt ▸ hprev) (by
                have endpoint := (le_min_iff.mp hincoming).2
                rw [hentries] at endpoint
                simp only [List.length_take, List.length_drop] at endpoint ⊢
                have hbound := hc.withinLog
                omega)
            refine ⟨a, owner, bound, by omega, hc, hb, ?_, ?_⟩
            · rw [he]
              simpa only [handleAppend, setServer, Function.update_self, hentries] using install
            · rw [he]
              simpa only [handleAppend, setServer, Function.update_self, hjt, ht] using hat
        · apply old
          simpa [handleAppend, setServer, Function.update_of_ne hn] using hi
      | _ =>
        apply old
        simp only [observeTerm, startElection, grantVote, receiveVote, becomeLeader,
          leaderAppend, receiveAppendReply, denyAppend, consume, setServer,
          Function.update_apply] at hi
        (try split_ifs at hi) <;> simp_all

/-- Transfer at one actual election, using smaller-term completeness and an
explicit common voter. No completeness at the candidate's term is assumed. -/
theorem candidate_prefix_of_election_intersection_aux (run : Execution C)
    (k leader index : ℕ) (hc : CommitEvent run k leader index)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (election : ℕ) (helection : election < run.length) (n : NodeId)
    (hcandidate : ((run.state election).servers n).role = .candidate)
    (hnext : run.state (election + 1) = becomeLeader (run.state election) n)
    (htu : ((run.state k).servers leader).currentTerm <
      ((run.state election).servers n).currentTerm)
    (intersects : (replicationQuorum (run.state k) leader index ∩
      eligibleVotes (run.state election) n).Nonempty)
    (earlier : ∀ z, z ≤ run.length → ∀ owner,
      ((run.state z).servers owner).role = .leader →
      ((run.state k).servers leader).currentTerm <
        ((run.state z).servers owner).currentTerm →
      ((run.state z).servers owner).currentTerm <
        ((run.state election).servers n).currentTerm →
      (((run.state k).servers leader).log.take index).IsPrefix
        ((run.state z).servers owner).log) :
    (((run.state k).servers leader).log.take index).IsPrefix
      ((run.state election).servers n).log := by
  have electionEnd : election ≤ run.length := Nat.le_of_lt helection
  obtain ⟨v, hv⟩ := intersects
  obtain ⟨hvCommit, hvVote⟩ := Finset.mem_inter.mp hv
  have hvBallot : v ∈ votesFor (run.state election).received
      ((run.state election).servers n).currentTerm n := (Finset.mem_inter.mp hvVote).1
  obtain ⟨a, ha, hat, hap⟩ :=
    commit_quorum_replica hc
      (fun z hz => safe z (by have := hc.within; omega)) v hvCommit
  obtain ⟨b, hb, hbt, hup⟩ :=
    winning_voter_snapshot run election electionEnd n hcandidate v hvBallot
  have aEnd : a ≤ run.length := by have := hc.within; omega
  have bEnd : b ≤ run.length := by omega
  have hab : a ≤ b := by
    by_contra h
    have mono := term_path_monotone (run.path b a (by omega) aEnd) v
    rw [hat, hbt] at mono
    omega
  have voterPrefix := voter_prefix_retained run a b hab bEnd v
    (((run.state k).servers leader).log.take index) hap (by
      intro i hai hib t sender prev pt entries lc packet ht
      have hiEnd : i ≤ run.length := by omega
      have hw : AppendWitness run i t sender prev pt entries lc :=
        network_witness run i hiEnd _ packet
      obtain ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
        hsourcePrev, hsourcePt, hentries, _hlc⟩ := hw
      refine ⟨sourceTime, count, hsourceTime, hsourceRole, hsourceTerm,
        hsourcePrev, hsourcePt, hentries, ?_⟩
      have sourceEnd : sourceTime ≤ run.length := by omega
      have low := term_path_monotone (run.path a i hai hiEnd) v
      have high := term_path_monotone (run.path i b (by omega) bEnd) v
      rw [hat, ← ht] at low
      rw [← ht, hbt] at high
      have hne := no_leader_before_election run election (by omega)
        (safe (election + 1) (by omega)) n hcandidate
        hnext sourceTime (by omega) sender hsourceRole
      have strictHigh : ((run.state sourceTime).servers sender).currentTerm <
          ((run.state election).servers n).currentTerm := by
        rw [hsourceTerm] at hne ⊢
        omega
      by_cases heq : t = ((run.state k).servers leader).currentTerm
      · have comparable :=
          same_term_snapshots_comparable run sourceTime k run.length le_rfl sourceEnd
          (Nat.le_of_lt hc.within) safe sender leader hsourceRole hc.leaderRole
          (hsourceTerm.trans heq)
        rcases comparable with h | h
        · exact List.prefix_or_prefix_of_prefix h (List.take_prefix _ _)
        · exact Or.inr ((List.take_prefix _ _).trans h)
      · exact Or.inr (earlier sourceTime sourceEnd sender hsourceRole
          (by rw [hsourceTerm]; omega) strictHigh))
  have candidatePrefix := candidate_prefix_of_upToDate run k leader index hc safe
    election electionEnd n hcandidate b bEnd v voterPrefix hup earlier
  exact candidatePrefix

/-- A joint barrier is an actual joint-quorum commit whose protected prefix
contains the joint entry. Its term is bounded explicitly. -/
def JointBarrier (run : Execution C) (termBound : ℕ) : Prop :=
  ∃ a owner bound, CommitEvent run a owner bound ∧
    active ((run.state a).servers owner) = C.jointConfig ∧
    (∃ e ∈ (((run.state a).servers owner).log.take bound),
      e.payload = .config C.jointConfig) ∧
    ((run.state a).servers owner).currentTerm ≤ termBound

/-- Once content provenance is available through a term, every new-configuration
entry through that term has a real joint barrier. A final-config commit reduces
to the strictly earlier creation of its own final entry, not to an assumed barrier. -/
theorem new_entry_joint_barrier_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (ceiling : ℕ) (complete : CommitLeaderPrefixes run ceiling)
    (distinct : C.initial ≠ C.finalConfig)
    (k : ℕ) (hk : k ≤ run.length) (node : NodeId) (entry : LogEntry)
    (hentry : entry ∈ ((run.state k).servers node).log)
    (hnew : entry.payload = .config C.finalConfig) (hupper : entry.term ≤ ceiling) :
    JointBarrier run entry.term := by
  induction k using Nat.strong_induction_on generalizing node entry with
  | h k ih =>
    obtain ⟨j, hj, owner, cmd, hrole, hguard, heq, hnext⟩ :=
      trace_generated run k hk node entry hentry
    have cmdEq : cmd = .config C.finalConfig := by simpa [heq] using hnew
    subst cmd
    have entryTerm : entry.term = ((run.state j).servers owner).currentTerm := by simp [heq]
    rcases hguard with ⟨_, bad, _⟩ | ⟨hactive, _, e, he, hcfg⟩
    · cases bad
    have ciPos : 0 < ((run.state j).servers owner).commitIndex := by
      by_contra h
      have hz : ((run.state j).servers owner).commitIndex = 0 := by omega
      simp [hz] at he
    obtain ⟨a, committer, bound, ha, hc, hbound, hprefix, hterm⟩ :=
      commit_index_content_aux run safe ceiling complete j (by omega) owner
        ((run.state j).servers owner).commitIndex ciPos le_rfl (by simpa [entryTerm] using hupper)
    have localPrefix : (((run.state a).servers committer).log.take
        ((run.state j).servers owner).commitIndex) =
        ((run.state j).servers owner).log.take ((run.state j).servers owner).commitIndex := by
      have takeEq := hprefix.take ((run.state j).servers owner).commitIndex
      have len : ((run.state j).servers owner).commitIndex ≤
          ((run.state a).servers committer).log.length := hbound.trans hc.withinLog
      have localLen := hprefix.length_le
      simp only [List.length_take, Nat.min_eq_left len] at localLen
      have eqLen := List.IsPrefix.eq_of_length takeEq (by simp [len, localLen])
      simpa only [List.take_take, Nat.min_self] using eqLen
    have histEntry : e ∈ ((run.state a).servers committer).log.take bound := by
      rw [← localPrefix] at he
      have small : (((run.state a).servers committer).log.take
          ((run.state j).servers owner).commitIndex).IsPrefix
          (((run.state a).servers committer).log.take bound) := by
        simpa only [List.take_take, Nat.min_eq_left hbound] using
          List.take_prefix ((run.state j).servers owner).commitIndex
            (((run.state a).servers committer).log.take bound)
      exact small.mem he
    have histMem := (List.take_prefix bound ((run.state a).servers committer).log).mem histEntry
    rcases active_config_reachable (run.reachable a (by omega)) committer with
      hold | hjoint | hfinal
    · exact False.elim (config_entry_excludes_initial run a (by omega) committer e histMem
        C.jointConfig hcfg distinct hold)
    · exact ⟨a, committer, bound, hc, hjoint, ⟨e, histEntry, hcfg⟩,
        by rw [entryTerm]; exact hterm⟩
    · rcases active_config_origin ((run.state a).servers committer).log C.initial with
        default | ⟨e', he', hp'⟩
      · exact False.elim (distinct (default.symm.trans hfinal))
      · have hpnew : e'.payload = .config C.finalConfig := by
          change e'.payload = .config (active ((run.state a).servers committer)) at hp'
          exact hp'.trans (congrArg EntryPayload.config hfinal)
        have termBound := reachable_log_bound (run.reachable a (by omega)) committer e' he'
        obtain ⟨b, l, i, hc', ha', he'', ht'⟩ := ih a (by omega) (by omega) committer
          e' he' hpnew (by rw [entryTerm] at hupper; omega)
        exact ⟨b, l, i, hc', ha', he'', by rw [entryTerm]; omega⟩

/-- Term-bounded creation evidence, used in the term induction below. -/
def NewEntryBarriersThrough (run : Execution C) (ceiling : ℕ) : Prop :=
  ∀ k, k ≤ run.length → ∀ node entry, entry ∈ ((run.state k).servers node).log →
    entry.payload = .config C.finalConfig → entry.term ≤ ceiling → JointBarrier run entry.term

theorem active_final_barrier_aux (run : Execution C) (ceiling : ℕ)
    (barriers : NewEntryBarriersThrough run ceiling) (distinct : C.initial ≠ C.finalConfig)
    (k : ℕ) (hk : k ≤ run.length) (node : NodeId)
    (hfinal : active ((run.state k).servers node) = C.finalConfig)
    (termBound : ∀ e ∈ ((run.state k).servers node).log, e.term ≤ ceiling) :
    JointBarrier run ceiling := by
  rcases active_config_origin ((run.state k).servers node).log C.initial with
    default | ⟨e, he, hp⟩
  · exact False.elim (distinct (default.symm.trans hfinal))
  · change e.payload = .config (active ((run.state k).servers node)) at hp
    obtain ⟨a, owner, index, hc, hj, he', ht⟩ := barriers k hk node e he
      (hp.trans (congrArg EntryPayload.config hfinal)) (termBound e he)
    exact ⟨a, owner, index, hc, hj, he', ht.trans (termBound e he)⟩

/-- An old-config leader's same-term prefix precedes a committed joint prefix.
The proof uses log comparability and the absence of a configuration in an
old-only log, rather than a false direct old/new quorum intersection. -/
theorem old_commit_before_same_term_joint_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (distinct : C.initial ≠ C.finalConfig)
    (k owner index : ℕ) (hc : CommitEvent run k owner index)
    (hold : active ((run.state k).servers owner) = C.initial)
    (a leader bound : ℕ) (hj : CommitEvent run a leader bound)
    (hentry : ∃ e ∈ (((run.state a).servers leader).log.take bound),
      e.payload = .config C.jointConfig)
    (hterm : ((run.state k).servers owner).currentTerm =
      ((run.state a).servers leader).currentTerm) :
    (((run.state k).servers owner).log.take index).IsPrefix
      (((run.state a).servers leader).log.take bound) := by
  obtain ⟨e, he, hp⟩ := hentry
  have exclude : ¬ (((run.state a).servers leader).log.take bound).IsPrefix
      ((run.state k).servers owner).log := by
    intro h
    exact config_entry_excludes_initial run k (Nat.le_of_lt hc.within) owner e (h.mem he)
      C.jointConfig hp distinct hold
  have compare := same_term_snapshots_comparable run k a run.length le_rfl
    (Nat.le_of_lt hc.within) (Nat.le_of_lt hj.within) safe owner leader hc.leaderRole
    hj.leaderRole hterm
  rcases compare with h | h
  · rcases List.prefix_or_prefix_of_prefix ((List.take_prefix index _).trans h)
      (List.take_prefix bound _) with small | large
    · exact small
    · exact False.elim (exclude (large.trans (List.take_prefix index _)))
  · exact False.elim (exclude ((List.take_prefix bound _).trans h))

/-- Successor step for completeness. All final configurations used in the
proof originate below the newly considered leader term. -/
theorem commit_leader_prefixes_succ_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (distinct : C.initial ≠ C.finalConfig) (ceiling : ℕ)
    (complete : CommitLeaderPrefixes run ceiling)
    (barriers : NewEntryBarriersThrough run ceiling) : CommitLeaderPrefixes run (ceiling + 1) := by
  intro k owner index hc j hj n hn upper low
  by_cases small : ((run.state j).servers n).currentTerm ≤ ceiling
  · exact complete k owner index hc j hj n hn small low
  have termEq : ((run.state j).servers n).currentTerm = ceiling + 1 := by omega
  obtain ⟨election, helection, hcandidate, het, hmajority, hnext⟩ :=
    leader_election_witness run j hj n hn
  have electionEnd : election ≤ run.length := by omega
  have electionTerm : ((run.state election).servers n).currentTerm = ceiling + 1 :=
    het.symm.trans termEq
  have candidatePrefix : (((run.state k).servers owner).log.take index).IsPrefix
      ((run.state election).servers n).log := by
    have viaIntersection : (replicationQuorum (run.state k) owner index ∩
        eligibleVotes (run.state election) n).Nonempty →
        (((run.state k).servers owner).log.take index).IsPrefix
          ((run.state election).servers n).log := by
      intro intersects
      apply candidate_prefix_of_election_intersection_aux run k owner index hc safe
        election (by omega) n hcandidate hnext (by omega) intersects
      intro z hz leader hrole hlo hhi
      exact complete k owner index hc z hz leader hrole (by omega) hlo
    rcases active_config_reachable (run.reachable k (Nat.le_of_lt hc.within)) owner with
      oldCommit | jointCommit | newCommit
    · rcases active_config_reachable (run.reachable election electionEnd) n with
        oldElection | jointElection | newElection
      · exact viaIntersection (quorum_intersection_same (oldCommit ▸ hc.quorum)
          (oldElection ▸ hmajority))
      · exact viaIntersection (quorum_intersection_stable_joint (oldCommit ▸ hc.quorum)
          (jointElection ▸ hmajority))
      · obtain ⟨a, leader, bound, joint, jointActive, jointEntry, jointTerm⟩ :=
          active_final_barrier_aux run ceiling barriers distinct election electionEnd n
            newElection (by
              intro e he
              have ht := reachable_candidate_strict (run.reachable election electionEnd)
                n hcandidate e he
              omega)
        have carry := joint_prefix_in_candidate_aux run a leader bound joint jointActive safe
          election electionEnd n hcandidate hmajority (by omega)
        rcases lt_trichotomy ((run.state k).servers owner).currentTerm
            ((run.state a).servers leader).currentTerm with earlier | same | later
        · have prior := complete k owner index hc a (Nat.le_of_lt joint.within) leader
            joint.leaderRole jointTerm earlier
          have protectedPrefix : (((run.state k).servers owner).log.take index).IsPrefix
              (((run.state a).servers leader).log.take bound) := by
            rcases List.prefix_or_prefix_of_prefix prior (List.take_prefix bound _) with h | h
            · exact h
            · obtain ⟨e, he, hp⟩ := jointEntry
              exact False.elim (config_entry_excludes_initial run k (Nat.le_of_lt hc.within)
                owner e ((h.trans (List.take_prefix index _)).mem he) C.jointConfig
                hp distinct oldCommit)
          exact protectedPrefix.trans carry
        · exact (old_commit_before_same_term_joint_aux run safe distinct k owner index hc
            oldCommit a leader bound joint jointEntry same).trans carry
        · have forbidden := joint_commit_prefix_in_later_leader_aux run a leader bound joint
            jointActive safe _ later k (Nat.le_of_lt hc.within) owner hc.leaderRole rfl
          obtain ⟨e, he, hp⟩ := jointEntry
          exact False.elim (config_entry_excludes_initial run k (Nat.le_of_lt hc.within)
            owner e (forbidden.mem he) C.jointConfig hp distinct oldCommit)
    · exact viaIntersection (joint_quorum_intersects_any_allowed (by
        simpa only [jointCommit, has_quorum, Transition.jointConfig] using hc.quorum)
        hmajority (active_config_reachable (run.reachable election electionEnd) n))
    · rcases active_config_reachable (run.reachable election electionEnd) n with
        oldElection | jointElection | newElection
      · obtain ⟨a, leader, bound, joint, jointActive, jointEntry, jointTerm⟩ :=
          active_final_barrier_aux run ceiling barriers distinct k (Nat.le_of_lt hc.within)
            owner newCommit (by
              intro e he
              have ht := reachable_log_bound (run.reachable k (Nat.le_of_lt hc.within)) owner e he
              omega)
        exact False.elim (joint_commit_blocks_old_candidate_aux run a leader bound joint
          jointActive safe jointEntry distinct election electionEnd n hcandidate hmajority
          (by omega) oldElection)
      · have intersect := quorum_intersection_joint_new (jointElection ▸ hmajority)
          (newCommit ▸ hc.quorum)
        exact viaIntersection (by simpa only [Finset.inter_comm] using intersect)
      · exact viaIntersection (quorum_intersection_same (newCommit ▸ hc.quorum)
          (newElection ▸ hmajority))
  have postElection : ((run.state (election + 1)).servers n).role = .leader := by
    rw [hnext]; simp [becomeLeader, setServer]
  have postTerm : ((run.state (election + 1)).servers n).currentTerm = ceiling + 1 := by
    rw [hnext]; simpa [becomeLeader, setServer] using electionTerm
  obtain ⟨cfg, elected⟩ := leaders_covered_reachable
    (run.reachable (election + 1) (by omega)) n postElection
  have retained := elected_same_term_log_prefix run (election + 1) j (by omega) hj
    (fun z hz => safe z (by omega)) (ceiling + 1) n cfg
    (by simpa only [postTerm] using elected) termEq
  apply List.IsPrefix.trans _ retained
  simpa only [hnext, becomeLeader, setServer, Function.update_self] using candidatePrefix

/-- Completeness and configuration provenance are built together by term.
Election uniqueness is assumed only for this finite history, not for its extension. -/
theorem term_layers_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (distinct : C.initial ≠ C.finalConfig) (ceiling : ℕ) :
    CommitLeaderPrefixes run ceiling ∧ NewEntryBarriersThrough run ceiling := by
  induction ceiling with
  | zero =>
    have complete : CommitLeaderPrefixes run 0 := by
      intro k owner index hc j hj n hn upper low
      have pos := reachable_active_positive (run.reachable j hj) n (by rw [hn]; decide)
      omega
    exact ⟨complete, new_entry_joint_barrier_aux run safe 0 complete distinct⟩
  | succ ceiling ih =>
    have complete := commit_leader_prefixes_succ_aux run safe distinct ceiling ih.1 ih.2
    exact ⟨complete, new_entry_joint_barrier_aux run safe (ceiling + 1) complete distinct⟩

/-- Successful old and new campaigns of the same term cannot coexist in the
same prior execution. The joint barrier can occur later in trace order than
one campaign: its strictly lower term supplies the required event ordering. -/
theorem old_new_campaigns_incompatible_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (distinct : C.initial ≠ C.finalConfig)
    (a b : ℕ) (ha : a ≤ run.length) (hb : b ≤ run.length) (oldNode newNode : NodeId)
    (oldCandidate : ((run.state a).servers oldNode).role = .candidate)
    (newCandidate : ((run.state b).servers newNode).role = .candidate)
    (oldQuorum : has_quorum (eligibleVotes (run.state a) oldNode)
      (active ((run.state a).servers oldNode)))
    (_newQuorum : has_quorum (eligibleVotes (run.state b) newNode)
      (active ((run.state b).servers newNode)))
    (oldActive : active ((run.state a).servers oldNode) = C.initial)
    (newActive : active ((run.state b).servers newNode) = C.finalConfig)
    (sameTerm : ((run.state a).servers oldNode).currentTerm =
      ((run.state b).servers newNode).currentTerm) : False := by
  let t := ((run.state b).servers newNode).currentTerm
  have pos : 0 < t := reachable_active_positive (run.reachable b hb) newNode
    (by rw [newCandidate]; decide)
  obtain ⟨k, owner, index, hc, hjoint, hentry, ht⟩ := active_final_barrier_aux run (t - 1)
    (term_layers_aux run safe distinct (t - 1)).2 distinct b hb newNode newActive (by
      intro e he
      have h := reachable_candidate_strict (run.reachable b hb) newNode newCandidate e he
      change e.term < t at h
      omega)
  exact joint_commit_blocks_old_candidate_aux run k owner index hc hjoint safe hentry distinct
    a ha oldNode oldCandidate oldQuorum (by dsimp [t] at ht; omega) oldActive

/-- Authentic campaign votes are compared in the common final snapshot of the
prior trace. This lemma does not assume uniqueness of a not-yet-executed election. -/
theorem campaigns_same_term_unique_aux (run : Execution C)
    (safe : ∀ j, j ≤ run.length → ElectionHistorySafe (run.state j))
    (a b : ℕ) (ha : a ≤ run.length) (hb : b ≤ run.length) (u v : NodeId)
    (hu : ((run.state a).servers u).role = .candidate)
    (hv : ((run.state b).servers v).role = .candidate)
    (qu : has_quorum (eligibleVotes (run.state a) u) (active ((run.state a).servers u)))
    (qv : has_quorum (eligibleVotes (run.state b) v) (active ((run.state b).servers v)))
    (ht : ((run.state a).servers u).currentTerm = ((run.state b).servers v).currentTerm) :
    u = v := by
  have castAt : ∀ k, k ≤ run.length → ∀ n w, w ∈ eligibleVotes (run.state k) n →
      (((run.state k).servers n).currentTerm, w, n) ∈ (run.state run.length).cast := by
    intro k hk n w hw
    have ballot := (mem_votesFor _ _ _ _).mp (Finset.mem_inter.mp hw).1
    have cast := (transport_reachable (run.reachable k hk)).received ballot
    have grow : ∀ {s s' : GlobalState C}, Relation.ReflTransGen Step s s' → s.cast ⊆ s'.cast := by
      intro s s' path
      induction path with
      | refl => exact fun _ h => h
      | tail _ st ih => exact fun _ h => cast_step_monotone st (ih h)
    exact grow (run.path k run.length hk le_rfl) cast
  have intersect : (eligibleVotes (run.state a) u ∩ eligibleVotes (run.state b) v).Nonempty →
      u = v := by
    intro hi
    exact election_unique_of_intersection (run.reachable run.length le_rfl)
      (castAt a ha u) (fun w hw => ht ▸ castAt b hb v w hw) hi
  rcases active_config_reachable (run.reachable a ha) u with oldU | jointU | newU <;>
    rcases active_config_reachable (run.reachable b hb) v with oldV | jointV | newV
  · exact intersect (quorum_intersection_same (oldU ▸ qu) (oldV ▸ qv))
  · exact intersect (quorum_intersection_stable_joint (oldU ▸ qu) (jointV ▸ qv))
  · by_cases same : C.initial = C.finalConfig
    · exact intersect (quorum_intersection_same (oldU ▸ qu) ((newV.trans same.symm) ▸ qv))
    · exact False.elim (old_new_campaigns_incompatible_aux run safe same a b ha hb u v
        hu hv qu qv oldU newV ht)
  · have h := quorum_intersection_stable_joint
      (show is_stable_quorum (eligibleVotes (run.state b) v) C.oldMembers from by
        simpa only [oldV, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qv)
      (show is_joint_quorum (eligibleVotes (run.state a) u) C.oldMembers C.newMembers from by
        simpa only [jointU, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qu)
    exact intersect (by rw [Finset.inter_comm]; exact h)
  · exact intersect (quorum_intersection_same (jointU ▸ qu) (jointV ▸ qv))
  · exact intersect (quorum_intersection_joint_new
      (show is_joint_quorum (eligibleVotes (run.state a) u) C.oldMembers C.newMembers from by
        simpa only [jointU, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qu)
      (show is_stable_quorum (eligibleVotes (run.state b) v) C.newMembers from by
        simpa only [newV, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qv))
  · by_cases same : C.initial = C.finalConfig
    · exact intersect (quorum_intersection_same (newU ▸ qu) ((oldV.trans same) ▸ qv))
    · exact False.elim (old_new_campaigns_incompatible_aux run safe same b a hb ha v u
        hv hu qv qu oldV newU ht.symm)
  · have h := quorum_intersection_joint_new
      (show is_joint_quorum (eligibleVotes (run.state b) v) C.oldMembers C.newMembers from by
        simpa only [jointV, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qv)
      (show is_stable_quorum (eligibleVotes (run.state a) u) C.newMembers from by
        simpa only [newU, has_quorum, Transition.initial, Transition.jointConfig,
          Transition.finalConfig] using qu)
    exact intersect (by rw [Finset.inter_comm]; exact h)
  · exact intersect (quorum_intersection_same (newU ▸ qu) (newV ▸ qv))

/-- Restrict a real execution; the state function and all earlier steps are unchanged. -/
def Execution.prefix (run : Execution C) (k : ℕ) (hk : k ≤ run.length) : Execution C :=
  ⟨k, run.state, run.initial, fun i hi => run.transition i (by omega)⟩

/-- Unconditional election safety, by strong induction on the actual transition
trace. Term-layer arguments inspect only the prefix ending before the new election. -/
theorem execution_election_safety (run : Execution C) (k : ℕ) (hk : k ≤ run.length) :
    ElectionHistorySafe (run.state k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => rw [run.initial]; simp [ElectionHistorySafe, initState]
    | succ k =>
      have prior : ElectionHistorySafe (run.state k) := ih k (by omega) (by omega)
      have priorTrace : ∀ z, z ≤ (run.prefix k (by omega)).length →
          ElectionHistorySafe ((run.prefix k (by omega)).state z) := by
        intro z hz
        exact ih z (by change z ≤ k at hz; omega) (by change z ≤ k at hz; omega)
      have st := run.transition k (by omega)
      generalize he : run.state (k + 1) = next at st ⊢
      cases st with
      | @elect n hn hq =>
        have compatible : ∀ t m cfg, (t, m, cfg) ∈ (run.state k).elected →
            t = ((run.state k).servers n).currentTerm → n = m := by
          intro t m cfg record termEq
          obtain ⟨a, ha, hCand, hTerm, _hCfg, hQuorum, _hNext⟩ :=
            election_record_origin run k (by omega) t m cfg record
          exact campaigns_same_term_unique_aux (run.prefix k (by omega)) priorTrace
            k a le_rfl (by exact Nat.le_of_lt ha) n m hn hCand hq hQuorum
            (termEq.symm.trans hTerm)
        intro t u v cfgU cfgV hu hv
        simp only [becomeLeader, Finset.mem_insert, Prod.mk.injEq] at hu hv
        rcases hu with ⟨rfl, rfl, rfl⟩ | hu <;>
          rcases hv with ⟨ht, rfl, rfl⟩ | hv
        · rfl
        · exact compatible _ _ _ hv rfl
        · exact (compatible _ _ _ hu ht).symm
        · exact prior _ _ _ _ _ hu hv
      | _ => exact prior

/-- Reachability alone implies historical election uniqueness in every term. -/
theorem raft_reconfig_election_safety {s : GlobalState C} (hr : Reachable s) :
    ElectionHistorySafe s := by
  obtain ⟨run, hend⟩ := reachable_execution hr
  rw [← hend]
  exact execution_election_safety run run.length le_rfl

/-- Global Log Matching is derived from the now-proved election invariant. -/
theorem raft_reconfig_log_matching {s : GlobalState C} (hr : Reachable s) :
    GlobalLogMatching s := by
  obtain ⟨run, hend⟩ := reachable_execution hr
  rw [← hend]
  exact log_matching_of_prior_election_safety run run.length le_rfl
    (fun j hj => execution_election_safety run j (Nat.le_of_lt hj))

/-- All configurations have overlapping quorums when the old and new sets coincide. -/
theorem allowed_quorums_intersect_of_same_members {cfg₁ cfg₂ : Config}
    {Q₁ Q₂ : Finset NodeId} (same : C.initial = C.finalConfig)
    (hc₁ : AllowedConfig C cfg₁) (hc₂ : AllowedConfig C cfg₂)
    (hq₁ : has_quorum Q₁ cfg₁) (hq₂ : has_quorum Q₂ cfg₂) : (Q₁ ∩ Q₂).Nonempty := by
  have phase : ∀ cfg, AllowedConfig C cfg → cfg = C.initial ∨ cfg = C.jointConfig := by
    intro cfg h
    rcases h with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact Or.inl same.symm
  rcases phase cfg₁ hc₁ with rfl | rfl <;> rcases phase cfg₂ hc₂ with rfl | rfl
  · exact quorum_intersection_same hq₁ hq₂
  · exact quorum_intersection_stable_joint hq₁ hq₂
  · have h := quorum_intersection_stable_joint hq₂ hq₁
    rw [Finset.inter_comm]; exact h
  · exact quorum_intersection_same hq₁ hq₂

/-- Operational Leader Completeness for every actual stable or joint commit.
No election-safety, configuration-barrier or prefix-retention premise is exported. -/
theorem raft_reconfig_leader_completeness (run : Execution C)
    (k owner index : ℕ) (hc : CommitEvent run k owner index)
    (j : ℕ) (hj : j ≤ run.length) (leader : NodeId)
    (hrole : ((run.state j).servers leader).role = .leader)
    (hlater : ((run.state k).servers owner).currentTerm <
      ((run.state j).servers leader).currentTerm) :
    (((run.state k).servers owner).log.take index).IsPrefix
      ((run.state j).servers leader).log := by
  have safe := fun i hi => execution_election_safety run i hi
  by_cases same : C.initial = C.finalConfig
  · exact commit_prefix_with_intersecting_elections_aux run k owner index hc (by
      intro election he candidate _hqRole hq _ht
      exact allowed_quorums_intersect_of_same_members same
        (active_config_reachable (run.reachable k (Nat.le_of_lt hc.within)) owner)
        (active_config_reachable (run.reachable election he) candidate) hc.quorum hq)
      safe _ hlater j hj leader hrole rfl
  · exact (term_layers_aux run safe same ((run.state j).servers leader).currentTerm).1
      k owner index hc j hj leader hrole le_rfl hlater

/-- Concrete local committed-prefix origin, now with all auxiliary obligations discharged. -/
theorem commit_index_content (run : Execution C) (k : ℕ) (hk : k ≤ run.length)
    (node index : ℕ) (hp : 0 < index)
    (hi : index ≤ ((run.state k).servers node).commitIndex) :
    HistoricalCommitPrefix run k node index := by
  apply commit_index_content_aux run (fun j hj => execution_election_safety run j hj)
    ((run.state k).servers node).currentTerm ?_ k hk node index hp hi le_rfl
  intro a owner bound hc b hb leader hrole _hupper hlater
  exact raft_reconfig_leader_completeness run a owner bound hc b hb leader hrole hlater

/-- Historical fixation refers to a real earlier commit on the same trace, not
simultaneous presence in today's replicas. Positions use zero-based list indices. -/
def HistoricallyCommitted (run : Execution C) (time position : ℕ) (entry : LogEntry) : Prop :=
  ∃ a owner bound, a < time ∧ CommitEvent run a owner bound ∧ position < bound ∧
    ((run.state a).servers owner).log[position]? = some entry

/-- Every entry below a local commitIndex has the contents of an actual earlier commit. -/
theorem commit_index_soundness (run : Execution C) (time : ℕ) (ht : time ≤ run.length)
    (node position : ℕ) (hpos : position < ((run.state time).servers node).commitIndex) :
    ∃ entry, ((run.state time).servers node).log[position]? = some entry ∧
      HistoricallyCommitted run time position entry := by
  obtain ⟨a, owner, bound, ha, hc, hb, hprefix, _term⟩ :=
    commit_index_content run time ht node (position + 1) (by omega) (by omega)
  have histLen : position < ((run.state a).servers owner).log.length := by
    have := hc.withinLog; omega
  let entry := ((run.state a).servers owner).log[position]
  have histGet : ((run.state a).servers owner).log[position]? = some entry :=
    List.getElem?_eq_getElem histLen
  refine ⟨entry, ?_, a, owner, bound, ha, hc, by omega, histGet⟩
  obtain ⟨suffix, hlog⟩ := hprefix
  rw [← hlog, List.getElem?_append_left (by simp; omega),
    List.getElem?_take_of_lt (by omega)]
  exact histGet

/-- The creation barrier is now unconditional, including inherited commitIndex values. -/
theorem new_entry_has_joint_barrier (run : Execution C)
    (distinct : C.initial ≠ C.finalConfig)
    (k : ℕ) (hk : k ≤ run.length) (node : NodeId) (entry : LogEntry)
    (he : entry ∈ ((run.state k).servers node).log)
    (hnew : entry.payload = .config C.finalConfig) : JointBarrier run entry.term := by
  exact (term_layers_aux run (fun i hi => execution_election_safety run i hi)
    distinct entry.term).2 k hk node entry he hnew le_rfl

/-- If joint survives and the active configuration is stable-new, a final
configuration entry really occurs in the suffix, even when old = new. -/
theorem final_entry_after_joint {log : List LogEntry} {default : Config}
    {e : LogEntry} (he : e ∈ log) (hp : e.payload = .config C.jointConfig)
    (ha : active_config log default = C.finalConfig) :
    ∃ entry ∈ log, entry.payload = .config C.finalConfig := by
  obtain ⟨pre, post, hsplit⟩ := List.mem_iff_append.mp he
  have activePost : active_config post C.jointConfig = C.finalConfig := by
    rw [hsplit, active_config_append] at ha
    simpa only [active_config, List.foldl_cons, hp] using ha
  rcases active_config_origin post C.jointConfig with hd | ⟨entry, hmem, hcfg⟩
  · have impossible := hd.symm.trans activePost
    cases impossible
  · refine ⟨entry, ?_, hcfg.trans (congrArg EntryPayload.config activePost)⟩
    rw [hsplit]; simp [hmem]

/-- Chronological barrier: the joint commit is strictly before the given time. -/
def JointBarrierBefore (run : Execution C) (time termBound : ℕ) : Prop :=
  ∃ a owner index, a < time ∧ CommitEvent run a owner index ∧
    active ((run.state a).servers owner) = C.jointConfig ∧
    (∃ e ∈ (((run.state a).servers owner).log.take index),
      e.payload = .config C.jointConfig) ∧
    ((run.state a).servers owner).currentTerm ≤ termBound

/-- Any locally committed joint entry has an actual earlier joint-quorum commit.
Recursion through an inherited final-config commit decreases execution time. -/
theorem committed_joint_has_prior_barrier (run : Execution C) (time : ℕ)
    (ht : time ≤ run.length) (node : NodeId)
    (jointLocal : ∃ e ∈ (((run.state time).servers node).log.take
      ((run.state time).servers node).commitIndex), e.payload = .config C.jointConfig) :
    JointBarrierBefore run time ((run.state time).servers node).currentTerm := by
  induction time using Nat.strong_induction_on generalizing node with
  | h time ih =>
    obtain ⟨e, he, hp⟩ := jointLocal
    have ciPos : 0 < ((run.state time).servers node).commitIndex := by
      by_contra h
      have hz : ((run.state time).servers node).commitIndex = 0 := by omega
      simp [hz] at he
    obtain ⟨a, committer, bound, ha, hc, hbound, hpre, hterm⟩ := commit_index_content run time ht
      node ((run.state time).servers node).commitIndex ciPos le_rfl
    have localEq : (((run.state a).servers committer).log.take
        ((run.state time).servers node).commitIndex) =
        ((run.state time).servers node).log.take ((run.state time).servers node).commitIndex := by
      have len := hbound.trans hc.withinLog
      have localLen := hpre.length_le
      simp only [List.length_take, Nat.min_eq_left len] at localLen
      have eqLen := List.IsPrefix.eq_of_length
        (hpre.take ((run.state time).servers node).commitIndex)
        (by simp [len, localLen])
      simpa only [List.take_take, Nat.min_self] using eqLen
    rw [← localEq] at he
    have histMem := List.mem_of_mem_take he
    have histPrefix : e ∈ ((run.state a).servers committer).log.take bound := by
      have small : (((run.state a).servers committer).log.take
          ((run.state time).servers node).commitIndex).IsPrefix
          (((run.state a).servers committer).log.take bound) := by
        simpa only [List.take_take, Nat.min_eq_left hbound] using
          List.take_prefix ((run.state time).servers node).commitIndex
            (((run.state a).servers committer).log.take bound)
      exact small.mem he
    by_cases joint : active ((run.state a).servers committer) = C.jointConfig
    · exact ⟨a, committer, bound, ha, hc, joint, ⟨e, histPrefix, hp⟩, hterm⟩
    have final : active ((run.state a).servers committer) = C.finalConfig := by
      rcases active_config_reachable (run.reachable a (by omega)) committer with old | hj | hf
      · by_cases same : C.initial = C.finalConfig
        · exact old.trans same
        · exact False.elim (config_entry_excludes_initial run a (by omega) committer e histMem
            C.jointConfig hp same old)
      · exact False.elim (joint hj)
      · exact hf
    obtain ⟨entry, hentry, hpnew⟩ := final_entry_after_joint histMem hp final
    obtain ⟨b, hb, leader, cmd, role, guard, entryEq, _next⟩ :=
      trace_generated run a (by omega) committer entry hentry
    have cmdEq : cmd = .config C.finalConfig := by simpa [entryEq] using hpnew
    subst cmd
    rcases guard with ⟨_, impossible, _⟩ | ⟨_, _, localJoint⟩
    · cases impossible
    obtain ⟨c, owner, index, hcb, commit, activeJoint, jointEntry, tc⟩ :=
      ih b (by omega) (by omega) leader localJoint
    have entryBound := reachable_log_bound (run.reachable a (by omega)) committer entry hentry
    have entryTerm : entry.term = ((run.state b).servers leader).currentTerm := by simp [entryEq]
    exact ⟨c, owner, index, by omega, commit, activeJoint, jointEntry, by omega⟩

/-- Exact creation rule with a derived historical witness; the commit is strictly
before creation and its prefix contains joint. This also covers identical memberships. -/
theorem joint_committed_before_new_created (run : Execution C) (time : ℕ)
    (ht : time ≤ run.length) (node : NodeId)
    (guard : mayAppend ((run.state time).servers node) (.config C.finalConfig)) :
    JointBarrierBefore run time ((run.state time).servers node).currentTerm := by
  rcases guard with ⟨_, impossible, _⟩ | ⟨_, _, localJoint⟩
  · cases impossible
  · exact committed_joint_has_prior_barrier run time ht node localJoint

/-- Actual replicas at a commit's quorum, discharged from the global induction.
The replica times are historical; acknowledgments may have been delayed. -/
theorem commit_origin_implies_quorum_replication (run : Execution C)
    (k owner index : ℕ) (hc : CommitEvent run k owner index)
    (node : NodeId) (hnode : node ∈ replicationQuorum (run.state k) owner index) :
    ∃ a, a ≤ k ∧
      ((run.state a).servers node).currentTerm = ((run.state k).servers owner).currentTerm ∧
      (((run.state k).servers owner).log.take index).IsPrefix
        ((run.state a).servers node).log :=
  commit_quorum_replica hc (fun j hj => execution_election_safety run j
    (hj.trans (Nat.le_of_lt hc.within))) node hnode

/-- Local commit indices stay within their actual logs, including partial batches. -/
theorem commit_index_within_log (run : Execution C) (time : ℕ) (ht : time ≤ run.length)
    (node : NodeId) : ((run.state time).servers node).commitIndex ≤
      ((run.state time).servers node).log.length := by
  by_cases pos : 0 < ((run.state time).servers node).commitIndex
  · obtain ⟨a, owner, bound, _ha, hc, hbound, hpre, _term⟩ :=
      commit_index_content run time ht node _ pos le_rfl
    have len := hpre.length_le
    simpa only [List.length_take, Nat.min_eq_left (hbound.trans hc.withinLog)] using len
  · omega

/-- A quorum-backed candidate already contains every earlier-term committed
prefix. Extend the trace by its enabled election and apply proved completeness;
no assumption about the extended trace's safety is required. -/
theorem committed_prefix_preserved_at_election (run : Execution C)
    (k owner index : ℕ) (hc : CommitEvent run k owner index) (candidate : NodeId)
    (hrole : ((run.state run.length).servers candidate).role = .candidate)
    (hq : has_quorum (eligibleVotes (run.state run.length) candidate)
      (active ((run.state run.length).servers candidate)))
    (ht : ((run.state k).servers owner).currentTerm <
      ((run.state run.length).servers candidate).currentTerm) :
    (((run.state k).servers owner).log.take index).IsPrefix
      ((run.state run.length).servers candidate).log := by
  let extended := run.extend (becomeLeader (run.state run.length) candidate) (.elect hrole hq)
  have old : ∀ i, i ≤ run.length → extended.state i = run.state i := by
    intro i hi; simp [extended, Execution.extend, hi]
  have last : extended.state extended.length = becomeLeader (run.state run.length) candidate := by
    simp [extended, Execution.extend]
  have commit : CommitEvent extended k owner index := by
    have hk := Nat.le_of_lt hc.within
    refine ⟨by dsimp [extended, Execution.extend]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [old k hk] using hc.leaderRole
    · simpa only [old k hk] using hc.withinLog
    · simpa only [old k hk] using hc.currentTerm
    · simpa only [old k hk] using hc.quorum
    · rw [old k hk, old (k + 1) (by have := hc.within; omega)]; exact hc.next
  have transfer := raft_reconfig_leader_completeness extended k owner index commit
    extended.length le_rfl candidate (by rw [last]; simp [becomeLeader, setServer])
    (by rw [last, old k (Nat.le_of_lt hc.within)]
        simpa only [becomeLeader, setServer, Function.update_self] using ht)
  simpa only [last, old k (Nat.le_of_lt hc.within), becomeLeader, setServer,
    Function.update_self] using transfer

/-- The completed suite exports reachable-state safety and same-execution
historical provenance. Auxiliary safety premises do not enter this interface. -/
structure DistributedRaftJointConsensusReconfigSuite : Prop where
  election_safety : ∀ (C : Transition) (s : GlobalState C), Reachable s → ElectionHistorySafe s
  log_matching : ∀ (C : Transition) (s : GlobalState C), Reachable s → GlobalLogMatching s
  leader_completeness : ∀ (C : Transition) (run : Execution C) k owner index,
    CommitEvent run k owner index → ∀ j, j ≤ run.length → ∀ leader,
    ((run.state j).servers leader).role = .leader →
    ((run.state k).servers owner).currentTerm < ((run.state j).servers leader).currentTerm →
    (((run.state k).servers owner).log.take index).IsPrefix ((run.state j).servers leader).log
  commit_contents : ∀ (C : Transition) (run : Execution C) time, time ≤ run.length →
    ∀ node position, position < ((run.state time).servers node).commitIndex →
    ∃ entry, ((run.state time).servers node).log[position]? = some entry ∧
      HistoricallyCommitted run time position entry
  joint_before_new : ∀ (C : Transition) (run : Execution C) time, time ≤ run.length →
    ∀ node, mayAppend ((run.state time).servers node) (.config C.finalConfig) →
    JointBarrierBefore run time ((run.state time).servers node).currentTerm
  rollback : ∀ (pre suffix : List LogEntry) cfg,
    active_config ((pre ++ suffix).take pre.length) cfg = active_config pre cfg
  old_joint_intersection : ∀ (Q₁ Q₂ A B : Finset NodeId),
    is_stable_quorum Q₁ A → is_joint_quorum Q₂ A B → (Q₁ ∩ Q₂).Nonempty
  joint_new_intersection : ∀ (Q₁ Q₂ A B : Finset NodeId),
    is_joint_quorum Q₁ A B → is_stable_quorum Q₂ B → (Q₁ ∩ Q₂).Nonempty
  joint_joint_intersection : ∀ (Q₁ Q₂ A B : Finset NodeId),
    is_joint_quorum Q₁ A B → is_joint_quorum Q₂ A B →
    (Q₁ ∩ Q₂ ∩ A).Nonempty ∧ (Q₁ ∩ Q₂ ∩ B).Nonempty
  disjoint_handover : Reachable Examples.s₁₄
  rollback_execution : Reachable RollbackExample.r₁₇

theorem distributed_raft_joint_consensus_master_suite :
    DistributedRaftJointConsensusReconfigSuite where
  election_safety := fun _ _ hr => raft_reconfig_election_safety hr
  log_matching := fun _ _ hr => raft_reconfig_log_matching hr
  leader_completeness := fun _ => raft_reconfig_leader_completeness
  commit_contents := fun _ => commit_index_soundness
  joint_before_new := fun _ => joint_committed_before_new_created
  rollback := raft_reconfig_rollback_on_truncate
  old_joint_intersection := fun _ _ _ _ => quorum_intersection_stable_joint
  joint_new_intersection := fun _ _ _ _ => quorum_intersection_joint_new
  joint_joint_intersection := fun _ _ _ _ => quorum_intersection_joint_joint
  disjoint_handover := Examples.reach₁₄
  rollback_execution := RollbackExample.reach₁₇

end DistributedRaftJointConsensusReconfig
