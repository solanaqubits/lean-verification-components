/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Verification.DistributedTwoPhaseCommit
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype

/-!
# Two-participant operational 2PC with timeout observations

One transaction, fixed honest participants, a fail-stop coordinator, and an
asynchronous packet list. Delivery consumes an actual packet; timeout is an
observation, not evidence of failure. No recovery, fairness, physical clock or
peer termination protocol is assumed. Finite control lemmas are kernel checked;
network queues and execution lengths are unbounded.
-/

namespace DistributedTwoPhaseCommitTimeout

open DistributedTwoPhaseCommit (Decision)

instance : Fintype Decision := ⟨{.commit, .abort}, by intro d; cases d <;> simp⟩

inductive ParticipantState where
  | init | prepared | committed | aborted
  deriving DecidableEq, Repr

instance : Fintype ParticipantState :=
  ⟨{.init, .prepared, .committed, .aborted}, by intro s; cases s <;> simp⟩

/-- `false` is P1 and `true` is P2. -/
abbrev Participant := Bool

structure Core where
  left : ParticipantState
  right : ParticipantState
  yesLeft : Bool
  yesRight : Bool
  decision : Option Decision
  running : Bool
  deriving DecidableEq, Repr, Fintype

def localState (c : Core) (p : Participant) : ParticipantState :=
  if p then c.right else c.left

def votedYes (c : Core) (p : Participant) : Bool :=
  if p then c.yesRight else c.yesLeft

def setLocal (c : Core) (p : Participant) (v : ParticipantState) : Core :=
  if p then { c with right := v } else { c with left := v }

def recordYes (c : Core) (p : Participant) : Core :=
  if p then { c with yesRight := true } else { c with yesLeft := true }

inductive Packet where
  | yes (p : Participant)
  | no (p : Participant)
  | decision (p : Participant) (d : Decision)
  deriving DecidableEq, Repr, Fintype

inductive Event where
  | prepare (p : Participant)
  | preVoteAbort (p : Participant)
  | receiveYes (p : Participant)
  | receiveNo (p : Participant)
  | chooseCommit
  | chooseAbort
  | sendDecision (p : Participant) (d : Decision)
  | receiveDecision (p : Participant) (d : Decision)
  | timeout (p : Participant)
  | crash
  | drop (m : Packet)
  deriving DecidableEq, Repr, Fintype

def incoming : Event → Option Packet
  | .receiveYes p => some (.yes p)
  | .receiveNo p => some (.no p)
  | .receiveDecision p d => some (.decision p d)
  | .drop m => some m
  | _ => none

def outgoing : Event → List Packet
  | .prepare p => [.yes p]
  | .preVoteAbort p => [.no p]
  | .sendDecision p d => [.decision p d]
  | _ => []

/-- Guards consult only the acting process's state. Packet presence is checked by Step. -/
def coreNext (c : Core) : Event → Option Core
  | .prepare p => if localState c p = .init then some (setLocal c p .prepared) else none
  | .preVoteAbort p => if localState c p = .init then some (setLocal c p .aborted) else none
  | .receiveYes p => if c.running ∧ c.decision = none then some (recordYes c p) else none
  | .receiveNo _ => if c.running ∧ c.decision = none then
      some { c with decision := some .abort } else none
  | .chooseCommit => if c.running ∧ c.decision = none ∧ c.yesLeft ∧ c.yesRight then
      some { c with decision := some .commit } else none
  | .chooseAbort => if c.running ∧ c.decision = none then
      some { c with decision := some .abort } else none
  | .sendDecision _ d => if c.running ∧ c.decision = some d then some c else none
  | .receiveDecision p .commit =>
      if localState c p = .prepared ∨ localState c p = .committed then
        some (setLocal c p .committed) else none
  | .receiveDecision p .abort =>
      if localState c p ≠ .committed then some (setLocal c p .aborted) else none
  | .timeout _ => some c
  | .crash => if c.running then some { c with running := false } else none
  | .drop _ => some c

structure Network where
  core : Core
  packets : List Packet
  deriving DecidableEq, Repr

def initial : Network :=
  ⟨⟨.init, .init, false, false, none, true⟩, []⟩

def inputAvailable (s : Network) (e : Event) : Prop :=
  ∀ m ∈ (incoming e).toList, m ∈ s.packets

instance (s : Network) (e : Event) : Decidable (inputAvailable s e) :=
  inferInstanceAs (Decidable (∀ m ∈ (incoming e).toList, m ∈ s.packets))

def remaining (packets : List Packet) (e : Event) : List Packet :=
  match incoming e with
  | none => packets
  | some m => packets.erase m

/-- A transition consumes a queued packet and appends only the rule's output. -/
inductive Step : Network → Event → Network → Prop where
  | execute {s : Network} {e : Event} {c : Core}
      (enabled : coreNext s.core e = some c) (available : inputAvailable s e) :
      Step s e ⟨c, remaining s.packets e ++ outgoing e⟩

inductive Execution : Network → List Event → Network → Prop where
  | nil (s : Network) : Execution s [] s
  | cons {s t u : Network} {e : Event} {es : List Event}
      (head : Step s e t) (tail : Execution t es u) : Execution s (e :: es) u

def Reachable (s : Network) : Prop := ∃ es, Execution initial es s

def CoreInvariant (c : Core) : Prop :=
  (∀ p, localState c p = .committed → c.decision = some .commit) ∧
  (∀ p, localState c p = .aborted → c.decision ≠ some .commit) ∧
  (∀ p, votedYes c p = true → localState c p ≠ .init ∧
    (localState c p = .aborted → c.decision = some .abort)) ∧
  (c.decision = some .commit → c.yesLeft = true ∧ c.yesRight = true)

def PacketValid (c : Core) : Packet → Prop
  | .yes p => localState c p ≠ .init ∧
      (localState c p = .aborted → c.decision = some .abort)
  | .no p => localState c p = .aborted ∧ c.decision ≠ some .commit
  | .decision _ d => c.decision = some d

def Invariant (s : Network) : Prop :=
  CoreInvariant s.core ∧ ∀ m ∈ s.packets, PacketValid s.core m

instance (c : Core) : Decidable (CoreInvariant c) := by unfold CoreInvariant; infer_instance
instance (c : Core) (m : Packet) : Decidable (PacketValid c m) := by
  cases m <;> unfold PacketValid <;> infer_instance

def SafeUpdate (c : Core) (e : Event) : Prop :=
  match coreNext c e with
  | none => True
  | some c' => CoreInvariant c' ∧
      (∀ m, PacketValid c m → PacketValid c' m) ∧
      (∀ m ∈ outgoing e, PacketValid c' m)

instance (c : Core) (e : Event) : Decidable (SafeUpdate c e) := by
  unfold SafeUpdate
  split <;> infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction checks all finite control states and events, not a bounded trace search.
/-- A finite control check, not an enumeration of networks or executions. -/
theorem core_transition_sound (c : Core) (e : Event) :
    CoreInvariant c → (∀ m ∈ (incoming e).toList, PacketValid c m) → SafeUpdate c e := by
  revert c e
  decide


theorem initial_invariant : Invariant initial := by
  constructor
  · decide
  · simp [initial]

theorem step_preserves_invariant {s t : Network} {e : Event}
    (h : Step s e t) (hs : Invariant s) : Invariant t := by
  cases h with
  | execute enabled available =>
    have hinput : ∀ m ∈ (incoming e).toList, PacketValid s.core m :=
      fun m hm => hs.2 m (available m hm)
    have hctrl := core_transition_sound s.core e hs.1 hinput
    simp only [SafeUpdate, enabled] at hctrl
    refine ⟨hctrl.1, ?_⟩
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · apply hctrl.2.1 m (hs.2 m ?_)
      unfold remaining at hm
      split at hm
      · exact hm
      · exact List.mem_of_mem_erase hm
    · exact hctrl.2.2 m hm

theorem execution_preserves_invariant {s t : Network} {es : List Event}
    (h : Execution s es t) (hs : Invariant s) : Invariant t := by
  induction h with
  | nil => exact hs
  | cons hstep _ ih => exact ih (step_preserves_invariant hstep hs)

theorem reachable_invariant {s : Network} (h : Reachable s) : Invariant s := by
  obtain ⟨es, he⟩ := h
  exact execution_preserves_invariant he initial_invariant

def Agreement (s : Network) : Prop :=
  ∀ p q, ¬ (localState s.core p = .committed ∧ localState s.core q = .aborted)

theorem reachable_agreement {s : Network} (h : Reachable s) : Agreement s := by
  intro p q hpq
  have hi := (reachable_invariant h).1
  exact hi.2.1 q hpq.2 (hi.1 p hpq.1)

/-- Terminal participants, chosen decisions and a stopped coordinator stay so. -/
def StableUpdate (c : Core) (e : Event) : Prop :=
  match coreNext c e with
  | none => True
  | some c' =>
      (∀ p, localState c p = .committed ∨ localState c p = .aborted →
        localState c' p = localState c p) ∧
      (∀ d, c.decision = some d → c'.decision = some d) ∧
      (c.running = false → c'.running = false)

instance (c : Core) (e : Event) : Decidable (StableUpdate c e) := by
  unfold StableUpdate
  split <;> infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction checks all finite control states and events, not a bounded trace search.
theorem core_transition_stable (c : Core) (e : Event) : StableUpdate c e := by
  revert c e
  decide

theorem terminal_state_preserved {s t : Network} {e : Event} (h : Step s e t)
    (p : Participant) (hp : localState s.core p = .committed ∨
      localState s.core p = .aborted) : localState t.core p = localState s.core p := by
  cases h with
  | execute enabled _ =>
    have hc := core_transition_stable s.core e
    simp only [StableUpdate, enabled] at hc
    exact hc.1 p hp

theorem decision_preserved {s t : Network} {e : Event} (h : Step s e t)
    (d : Decision) (hd : s.core.decision = some d) : t.core.decision = some d := by
  cases h with
  | execute enabled _ =>
    have hc := core_transition_stable s.core e
    simp only [StableUpdate, enabled] at hc
    exact hc.2.1 d hd

theorem aborted_preserved_execution {s t : Network} {es : List Event}
    (h : Execution s es t) (p : Participant) (hp : localState s.core p = .aborted) :
    localState t.core p = .aborted := by
  induction h with
  | nil => exact hp
  | cons hstep _ ih =>
    apply ih
    exact (terminal_state_preserved hstep p (Or.inr hp)).trans hp

theorem Execution.append {s t u : Network} {es fs : List Event}
    (h : Execution s es t) (h' : Execution t fs u) : Execution s (es ++ fs) u := by
  induction h with
  | nil => exact h'
  | cons step _ ih => exact .cons step (ih h')

theorem Reachable.after {s t : Network} {es : List Event}
    (h : Reachable s) (he : Execution s es t) : Reachable t := by
  obtain ⟨fs, hf⟩ := h
  exact ⟨fs ++ es, hf.append he⟩

theorem Reachable.step {s t : Network} {e : Event} (h : Reachable s)
    (he : Step s e t) : Reachable t := h.after (.cons he (.nil t))

/-- Pre-vote timeout makes abort permanent; every continuation excludes global commit. -/
theorem pre_vote_timeout_abort_safe {s : Network} (hs : Reachable s)
    (p : Participant) (hp : localState s.core p = .init) :
    ∃ t, Step s (.preVoteAbort p) t ∧ Agreement t ∧
      ∀ es u, Execution t es u →
        localState u.core p = .aborted ∧ u.core.decision ≠ some .commit := by
  let t : Network := ⟨setLocal s.core p .aborted, s.packets ++ [.no p]⟩
  have ht : Step s (.preVoteAbort p) t := by
    apply Step.execute
    · simp [coreNext, hp]
    · simp [inputAvailable, incoming]
  have hab : localState t.core p = .aborted := by
    cases p <;> simp [t, localState, setLocal]
  refine ⟨t, ht, reachable_agreement (hs.step ht), ?_⟩
  intro es u hu
  have hp' := aborted_preserved_execution hu p hab
  exact ⟨hp', (reachable_invariant ((hs.step ht).after hu)).1.2.1 p hp'⟩

def BothPrepared (c : Core) : Prop := c.left = .prepared ∧ c.right = .prepared

instance (c : Core) : Decidable (BothPrepared c) :=
  inferInstanceAs (Decidable (c.left = .prepared ∧ c.right = .prepared))

def IsDecision : Packet → Prop
  | .decision _ _ => True
  | _ => False

instance (m : Packet) : Decidable (IsDecision m) := by
  cases m <;> unfold IsDecision <;> infer_instance

def NoDecision (packets : List Packet) : Prop := ∀ m ∈ packets, ¬ IsDecision m

instance (packets : List Packet) : Decidable (NoDecision packets) :=
  inferInstanceAs (Decidable (∀ m ∈ packets, ¬ IsDecision m))

/-- Local closure fact used only when the coordinator is stopped and both are prepared. -/
def BlockedUpdate (c : Core) (e : Event) : Prop :=
  BothPrepared c → c.running = false →
    (∀ m ∈ (incoming e).toList, ¬ IsDecision m) →
      match coreNext c e with
      | none => True
      | some c' => BothPrepared c' ∧ c'.running = false ∧ NoDecision (outgoing e)

instance (c : Core) (e : Event) : Decidable (BlockedUpdate c e) := by
  unfold BlockedUpdate BothPrepared NoDecision
  split <;> infer_instance

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- Kernel reduction checks all finite control states and events, not a bounded trace search.
theorem core_blocked_closed (c : Core) (e : Event) : BlockedUpdate c e := by
  revert c e
  decide

theorem blocked_step_closed {s t : Network} {e : Event} (h : Step s e t)
    (hp : BothPrepared s.core) (hr : s.core.running = false) (hn : NoDecision s.packets) :
    BothPrepared t.core ∧ t.core.running = false ∧ NoDecision t.packets := by
  cases h with
  | execute enabled available =>
    have hc := core_blocked_closed s.core e hp hr (fun m hm => hn m (available m hm))
    simp only [enabled] at hc
    refine ⟨hc.1, hc.2.1, ?_⟩
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · apply hn m
      unfold remaining at hm
      split at hm
      · exact hm
      · exact List.mem_of_mem_erase hm
    · exact hc.2.2 m hm

theorem blocked_execution_closed {s t : Network} {es : List Event}
    (h : Execution s es t) (hp : BothPrepared s.core) (hr : s.core.running = false)
    (hn : NoDecision s.packets) :
    BothPrepared t.core ∧ t.core.running = false ∧ NoDecision t.packets := by
  induction h with
  | nil => exact ⟨hp, hr, hn⟩
  | cons hs _ ih =>
    obtain ⟨hp', hr', hn'⟩ := blocked_step_closed hs hp hr hn
    exact ih hp' hr' hn'

def HasTerminal (s : Network) : Prop :=
  ∃ p, localState s.core p = .committed ∨ localState s.core p = .aborted

/-- Blocking means no finite continuation reaches a terminal participant. -/
def Blocked (s : Network) : Prop :=
  ∀ es t, Execution s es t → ¬ HasTerminal t

theorem both_prepared_not_terminal {s : Network} (h : BothPrepared s.core) :
    ¬ HasTerminal s := by
  rintro ⟨p, hp⟩
  cases p <;> simp_all [localState, BothPrepared]

/-- A queued decision enables delivery even after coordinator failure; no fairness claim. -/
theorem in_flight_decision_delivery {s : Network} (hp : BothPrepared s.core)
    (p : Participant) (d : Decision) (hm : Packet.decision p d ∈ s.packets) :
    ∃ t, Step s (.receiveDecision p d) t ∧ HasTerminal t := by
  have hlocal : localState s.core p = .prepared := by
    cases p <;> simp_all [BothPrepared, localState]
  let st := match d with | .commit => ParticipantState.committed | .abort => .aborted
  let t : Network := ⟨setLocal s.core p st, s.packets.erase (.decision p d)⟩
  have ht : Step s (.receiveDecision p d) t := by
    have hc : coreNext s.core (.receiveDecision p d) = some (setLocal s.core p st) := by
      cases d <;> simp [coreNext, hlocal, st]
    simpa [remaining, incoming, outgoing, t] using
      (Step.execute hc (by simpa [inputAvailable, incoming] using hm))
  refine ⟨t, ht, p, ?_⟩
  cases d <;> cases p <;> simp [t, st, localState, setLocal]

/-- Exact relative characterization for this fail-stop, two-participant model. -/
theorem blocking_condition_characterization {s : Network}
    (hp : BothPrepared s.core) (hr : s.core.running = false) :
    Blocked s ↔ NoDecision s.packets := by
  constructor
  · intro hb m hm hd
    cases m with
    | yes p => exact hd
    | no p => exact hd
    | decision p d =>
      obtain ⟨t, ht, hterminal⟩ := in_flight_decision_delivery hp p d hm
      exact hb _ t (.cons ht (.nil t)) hterminal
  · intro hn es t he
    exact both_prepared_not_terminal (blocked_execution_closed he hp hr hn).1


/-- Executable interpreter used to certify concrete traces against the same Step. -/
def runEvent (s : Network) (e : Event) : Option Network :=
  if inputAvailable s e then
    (coreNext s.core e).map fun c => ⟨c, remaining s.packets e ++ outgoing e⟩
  else none

def run (s : Network) : List Event → Option Network
  | [] => some s
  | e :: es => (runEvent s e).bind fun t => run t es

theorem runEvent_sound {s t : Network} {e : Event} (h : runEvent s e = some t) :
    Step s e t := by
  unfold runEvent at h
  split at h
  next hav =>
    cases hc : coreNext s.core e with
    | none => simp [hc] at h
    | some c =>
      simp only [hc, Option.map_some, Option.some.injEq] at h
      subst t
      exact Step.execute hc hav
  next => simp at h

theorem run_sound {s t : Network} {es : List Event} (h : run s es = some t) :
    Execution s es t := by
  induction es generalizing s with
  | nil => simp only [run, Option.some.injEq] at h; subst t; exact .nil s
  | cons e es ih =>
    cases he : runEvent s e with
    | none => simp [run, he] at h
    | some u =>
      simp only [run, he, Option.bind_some] at h
      exact .cons (runEvent_sound he) (ih h)

inductive Observation where
  | sentYes | timeoutAbort | received (d : Decision) | timeout
  deriving DecidableEq, Repr

def observe (p : Participant) : Event → Option Observation
  | .prepare q => if q = p then some .sentYes else none
  | .preVoteAbort q => if q = p then some .timeoutAbort else none
  | .receiveDecision q d => if q = p then some (.received d) else none
  | .timeout q => if q = p then some .timeout else none
  | _ => none

/-- Complete local event projection; remote actions and crashes are not observed. -/
def Obs (p : Participant) (history : List Event) : List Observation :=
  history.filterMap (observe p)

abbrev LocalView := ParticipantState × List Observation

def view (p : Participant) (history : List Event) (s : Network) : LocalView :=
  (localState s.core p, Obs p history)

namespace Examples

/-- P2 has committed before the coordinator stops; P1 sees only its vote and timeout. -/
def commitHistory : List Event :=
  [.prepare false, .prepare true, .receiveYes false, .receiveYes true,
   .chooseCommit, .sendDecision true .commit, .receiveDecision true .commit,
   .crash, .timeout false]

def commitEnd : Network :=
  ⟨⟨.prepared, .committed, true, true, some .commit, false⟩, []⟩

def abortHistory : List Event :=
  [.prepare false, .preVoteAbort true, .receiveNo true, .crash, .timeout false]

def abortEnd : Network :=
  ⟨⟨.prepared, .aborted, false, false, some .abort, false⟩, [.yes false]⟩

theorem commit_execution : Execution initial commitHistory commitEnd :=
  run_sound (by decide)

theorem abort_execution : Execution initial abortHistory abortEnd :=
  run_sound (by decide)

theorem commit_reachable : Reachable commitEnd := ⟨commitHistory, commit_execution⟩
theorem abort_reachable : Reachable abortEnd := ⟨abortHistory, abort_execution⟩

def uncertainView : LocalView := (.prepared, [.sentYes, .timeout])

theorem commit_view : view false commitHistory commitEnd = uncertainView := by decide
theorem abort_view : view false abortHistory abortEnd = uncertainView := by decide

def blockedHistory : List Event := [.prepare false, .prepare true, .crash, .timeout false]

def blockedEnd : Network :=
  ⟨⟨.prepared, .prepared, false, false, none, false⟩, [.yes false, .yes true]⟩

theorem blocked_execution : Execution initial blockedHistory blockedEnd := run_sound (by decide)

theorem blocked_reachable : Reachable blockedEnd := ⟨blockedHistory, blocked_execution⟩

theorem blocked_end_blocked : Blocked blockedEnd :=
  (blocking_condition_characterization (by decide) (by rfl)).2 (by decide)

def inFlightHistory : List Event :=
  [.prepare false, .prepare true, .receiveYes false, .receiveYes true,
   .chooseCommit, .sendDecision false .commit, .crash]

def inFlightEnd : Network :=
  ⟨⟨.prepared, .prepared, true, true, some .commit, false⟩, [.decision false .commit]⟩

theorem in_flight_execution : Execution initial inFlightHistory inFlightEnd := run_sound (by decide)

theorem in_flight_reachable : Reachable inFlightEnd := ⟨inFlightHistory, in_flight_execution⟩

theorem in_flight_not_blocked : ¬ Blocked inFlightEnd := by
  intro h
  have hn := (blocking_condition_characterization (by decide) (by rfl)).1 h
  exact hn (.decision false .commit) (by simp [inFlightEnd]) trivial

end Examples

/-- Opposite terminal peers occur in reachable histories with exactly the same local view. -/
theorem prepared_indistinguishable_histories :
    ∃ ha hc sa sc,
      Execution initial ha sa ∧ Execution initial hc sc ∧
      view false ha sa = (.prepared, [.sentYes, .timeout]) ∧
      view false hc sc = (.prepared, [.sentYes, .timeout]) ∧
      sa.core.decision = some .abort ∧ sc.core.decision = some .commit ∧
      localState sa.core true = .aborted ∧ localState sc.core true = .committed := by
  exact ⟨Examples.abortHistory, Examples.commitHistory, Examples.abortEnd, Examples.commitEnd,
    Examples.abort_execution, Examples.commit_execution, Examples.abort_view,
    Examples.commit_view, rfl, rfl, rfl, rfl⟩

/-- Counterfactual override, deliberately not a constructor of the safe protocol Step. -/
def unsafeDecision (s : Network) (p : Participant) (d : Decision) : Network :=
  { s with core := setLocal s.core p (match d with | .commit => .committed | .abort => .aborted) }

theorem unilateral_commit_breaks_agreement :
    ¬ Agreement (unsafeDecision Examples.abortEnd false .commit) := by
  intro h
  exact h false true ⟨rfl, rfl⟩

theorem unilateral_abort_breaks_agreement :
    ¬ Agreement (unsafeDecision Examples.commitEnd false .abort) := by
  intro h
  exact h true false ⟨rfl, rfl⟩

/-- No deterministic policy deciding on this view is safe in both possible histories.
A policy which waits is not refuted: its codomain would include an undecided case. -/
theorem prepared_autonomous_decision_unsafe (policy : LocalView → Decision) :
    ¬ Agreement (unsafeDecision Examples.abortEnd false
      (policy (view false Examples.abortHistory Examples.abortEnd))) ∨
    ¬ Agreement (unsafeDecision Examples.commitEnd false
      (policy (view false Examples.commitHistory Examples.commitEnd))) := by
  rw [Examples.abort_view, Examples.commit_view]
  cases h : policy Examples.uncertainView with
  | commit => exact Or.inl unilateral_commit_breaks_agreement
  | abort => exact Or.inr unilateral_abort_breaks_agreement

/-- A selected decision is not undone by coordinator timeout/abort. -/
theorem chosen_decision_not_reversed {s t : Network} {e : Event}
    (h : Step s e t) (d : Decision) (hd : s.core.decision = some d) :
    t.core.decision = some d := decision_preserved h d hd

/-- The executable table is reused for two supplied, collected yes votes. -/
theorem commit_table_compatibility :
    DistributedTwoPhaseCommit.coordinatorDecision .yes .yes = .commit := rfl

structure DistributedTwoPhaseCommitTimeoutSuite : Prop where
  agreement : ∀ s, Reachable s → Agreement s
  pre_vote_safe : ∀ s, Reachable s → ∀ p, localState s.core p = .init →
    ∃ t, Step s (.preVoteAbort p) t ∧ Agreement t ∧
      ∀ es u, Execution t es u →
        localState u.core p = .aborted ∧ u.core.decision ≠ some .commit
  indistinguishable :
    ∃ ha hc sa sc, Execution initial ha sa ∧ Execution initial hc sc ∧
      view false ha sa = (.prepared, [.sentYes, .timeout]) ∧
      view false hc sc = (.prepared, [.sentYes, .timeout]) ∧
      sa.core.decision = some .abort ∧ sc.core.decision = some .commit ∧
      localState sa.core true = .aborted ∧ localState sc.core true = .committed
  no_autonomous_decision : ∀ policy : LocalView → Decision,
    ¬ Agreement (unsafeDecision Examples.abortEnd false
      (policy (view false Examples.abortHistory Examples.abortEnd))) ∨
    ¬ Agreement (unsafeDecision Examples.commitEnd false
      (policy (view false Examples.commitHistory Examples.commitEnd)))
  in_flight_delivery : ∀ s, BothPrepared s.core → ∀ p d,
    Packet.decision p d ∈ s.packets → ∃ t, Step s (.receiveDecision p d) t ∧ HasTerminal t
  blocking : ∀ s, BothPrepared s.core → s.core.running = false →
    (Blocked s ↔ NoDecision s.packets)
  reachable_blocking : Reachable Examples.blockedEnd ∧ Blocked Examples.blockedEnd
  reachable_escape : Reachable Examples.inFlightEnd ∧ ¬ Blocked Examples.inFlightEnd
  decision_stable : ∀ s t e, Step s e t → ∀ d,
    s.core.decision = some d → t.core.decision = some d

theorem distributed_two_phase_commit_timeout_master_suite :
    DistributedTwoPhaseCommitTimeoutSuite := {
  agreement := fun _ h => reachable_agreement h
  pre_vote_safe := fun _ h p hp => pre_vote_timeout_abort_safe h p hp
  indistinguishable := prepared_indistinguishable_histories
  no_autonomous_decision := prepared_autonomous_decision_unsafe
  in_flight_delivery := fun _ h p d hm => in_flight_decision_delivery h p d hm
  blocking := fun _ h hr => blocking_condition_characterization h hr
  reachable_blocking := ⟨Examples.blocked_reachable, Examples.blocked_end_blocked⟩
  reachable_escape := ⟨Examples.in_flight_reachable, Examples.in_flight_not_blocked⟩
  decision_stable := fun _ _ _ h d hd => decision_preserved h d hd
}

end DistributedTwoPhaseCommitTimeout
