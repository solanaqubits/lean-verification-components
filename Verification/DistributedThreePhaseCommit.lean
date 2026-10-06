/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedThreePhaseCommitCertificate

/-!
# Two-participant 3PC safety and conditional completion

The finite certificate is checked by the Lean kernel. Its closure gives safety
for unbounded finite executions. A rank argument distinguishes existence of
completion from eventual completion under explicit weak fairness, after a stable
accurate fenced view. Election, fencing and failure detection are environment
contracts; partitions, false suspicions and crash recovery are outside this model.
-/
namespace DistributedThreePhaseCommit

instance (s : Core) : Decidable (Certified s) :=
  inferInstanceAs (Decidable (certifiedBool s = true))

private theorem certified_checks {s : Core} (h : Certified s) :
    localCheck s = true ∧ (List.range 16).all (transitionCheck s) = true := by
  have hc : certificate.contains (encode s) = true ∧ decode (encode s) = s := by
    simpa [Certified, certifiedBool] using h
  have ha := CodeTree.all_sound certificate_checked hc.1
  simpa [stateCheck, hc.2] using ha

private theorem checked_transition {s t : Core} {e : Nat} (hs : Certified s)
    (he : e < 16) (ht : coreStep s e = some t) :
    Certified t ∧ terminalStable s t ∧
      (operational e → Stable s → Stable t ∧ rank t ≤ rank s ∧
        (rank t = rank s → t = s)) := by
  have h := List.all_eq_true.mp (certified_checks hs).2 e (List.mem_range.mpr he)
  have raw : Certified t ∧ (terminalStable s t ∧ Persistent s t ∧ PacketEvidence s t e) ∧
      (operational e → Stable s → Stable t ∧ rank t ≤ rank s ∧
        (rank t = rank s → t = s)) := by
    simp only [transitionCheck, ht, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  exact ⟨raw.1, raw.2.1.1, raw.2.2⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Locate the initial state in the kernel-checked finite certificate.
theorem initial_certified : Certified initial := by decide

theorem step_preserves_certificate {s t : Core} {e : Nat}
    (h : Step s e t) (hs : Certified s) : Certified t := by
  cases h with
  | execute he ht => exact (checked_transition hs he ht).1

theorem execution_preserves_certificate {s t : Core} {es : List Nat}
    (h : Execution s es t) (hs : Certified s) : Certified t := by
  induction h with
  | nil => exact hs
  | cons h _ ih => exact ih (step_preserves_certificate h hs)

theorem reachable_certified {s : Core} (h : Reachable s) : Certified s := by
  obtain ⟨es, h⟩ := h
  exact execution_preserves_certificate h initial_certified

private theorem local_facts {s : Core} (h : Certified s) :
    Agreement s ∧
    ((s.left = 2 ∨ s.left = 3 ∨ s.right = 2 ∨ s.right = 3) → s.yes = 3) ∧
    ((s.leftSlot = 3 ∨ s.leftSlot = 4 → s.leftBody = s.left) ∧
      (s.rightSlot = 3 ∨ s.rightSlot = 4 → s.rightBody = s.right)) ∧
    (s.phase = 4 → (member s false → s.left = 2 ∨ s.left = 3) ∧
      (member s true → s.right = 2 ∨ s.right = 3)) := by
  have hl := (certified_checks h).1
  simp only [localCheck, Bool.and_eq_true, decide_eq_true_eq] at hl
  exact ⟨hl.1.1.1.1, hl.1.1.1.2, hl.1.1.2, hl.1.2⟩

/-- Terminal decisions of stopped participants remain part of agreement. -/
theorem reachable_agreement {s : Core} (h : Reachable s) : Agreement s :=
  (local_facts (reachable_certified h)).1

/-- Votes from both participants, not a majority or only the surviving participant. -/
theorem commit_requires_yes {s : Core} (h : Reachable s)
    (hc : s.left = 3 ∨ s.right = 3) : s.yes = 3 := by
  apply (local_facts (reachable_certified h)).2.1
  rcases hc with hc | hc
  · exact Or.inr (Or.inl hc)
  · exact Or.inr (Or.inr (Or.inr hc))

/-- Consumed replies have exactly the state captured by their sender in this phase. -/
theorem precommit_ack_provenance {s : Core} (h : Reachable s) :
    (s.leftSlot = 3 ∨ s.leftSlot = 4 → s.leftBody = s.left) ∧
    (s.rightSlot = 3 ∨ s.rightSlot = 4 → s.rightBody = s.right) :=
  (local_facts (reachable_certified h)).2.2.1

/-- Every member of the committing view crossed PreCommit, even if it later stopped. -/
theorem normal_commit_barrier {s : Core} (h : Reachable s) (hp : s.phase = 4) :
    (member s false → s.left = 2 ∨ s.left = 3) ∧
    (member s true → s.right = 2 ∨ s.right = 3) :=
  (local_facts (reachable_certified h)).2.2.2 hp

theorem terminal_decision_stability {s t : Core} {e : Nat}
    (hs : Reachable s) (h : Step s e t) : terminalStable s t := by
  cases h with
  | execute he ht => exact (checked_transition (reachable_certified hs) he ht).2.1

theorem Execution.append {s t u : Core} {xs ys : List Nat}
    (h : Execution s xs t) (k : Execution t ys u) : Execution s (xs ++ ys) u := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h (ih k)

theorem Reachable.after {s t : Core} {es : List Nat}
    (hs : Reachable s) (h : Execution s es t) : Reachable t := by
  obtain ⟨xs, hx⟩ := hs
  exact ⟨xs ++ es, hx.append h⟩

theorem termination_protocol_preserves_agreement {s t : Core} {es : List Nat}
    (hs : Reachable s) (h : Execution s es t) : Agreement t :=
  reachable_agreement (hs.after h)

private theorem progress_exists {s : Core} (hs : Certified s)
    (hstable : Stable s) (hnot : ¬AllTerminal s) :
    ∃ e t, e ≤ 10 ∧ coreStep s e = some t ∧ t ≠ s := by
  have hl := (certified_checks hs).1
  simp only [localCheck, Bool.and_eq_true] at hl
  have hp := hl.2
  simp only [if_pos (show Stable s ∧ ¬AllTerminal s from ⟨hstable, hnot⟩)] at hp
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hp
  have hmem := List.mem_of_find?_eq_some he
  have hfound := List.find?_some he
  have hbound : e ≤ 10 := by
    have hlt := List.mem_range.mp hmem
    omega
  cases ht : coreStep s e with
  | none => simp [ht] at hfound
  | some t =>
    refine ⟨e, t, hbound, ht, ?_⟩
    simpa [ht] using hfound

/-- Existence of a finite completion once an accurate stable view is installed.
This does not assume a fair scheduler and does not assert that every scheduler finishes. -/
theorem completion_path_exists {s : Core} (hs : Reachable s) (hstable : Stable s) :
    ∃ es t, Execution s es t ∧ AllTerminal t := by
  suffices aux : ∀ n s, rank s = n → Certified s → Stable s →
      ∃ es t, Execution s es t ∧ AllTerminal t from
    aux (rank s) s rfl (reachable_certified hs) hstable
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hr hc hst
    by_cases hd : AllTerminal s
    · exact ⟨[], s, .nil s, hd⟩
    obtain ⟨e, t, he, ht, hne⟩ := progress_exists hc hst hd
    have facts := checked_transition hc (by omega) ht
    have prog := facts.2.2 (Or.inl he) hst
    have hlt : rank t < n := by
      have hn : rank t ≠ rank s := fun h => hne (prog.2.2 h)
      omega
    obtain ⟨es, u, hu, hd⟩ := ih (rank t) hlt t rfl facts.1 prog.1
    exact ⟨e :: es, u, .cons (.execute (by omega) ht) hu, hd⟩

/-- Infinite executions include real protocol actions and idle ticks. -/
structure Run where
  states : Nat → Core
  events : Nat → Nat
  valid : ∀ n, Step (states n) (events n) (states (n + 1))

/-- Concrete action justice, not an assumption of successful completion. -/
def WeaklyFair (r : Run) : Prop :=
  ∀ n e, e ≤ 10 →
    (∀ m, n ≤ m → ∃ t, coreStep (r.states m) e = some t ∧ t ≠ r.states m) →
    ∃ m, n ≤ m ∧ r.events m = e

/-- Explicit stable suffix: no new crash or view installation, a live owner and
exact nonempty membership. The installation/detection service is an external contract. -/
structure ProgressAssumptions (r : Run) where
  stableFrom : Nat
  reached : Reachable (r.states stableFrom)
  stable : Stable (r.states stableFrom)
  noFurtherFailure : ∀ n, stableFrom ≤ n → operational (r.events n)
  fair : WeaklyFair r


/-- Every weakly fair execution completes its survivors after the stable suffix.
There is no numerical wall-clock bound and no demand to finish stopped processes. -/
theorem completion_under_progress_assumptions (r : Run) (h : ProgressAssumptions r) :
    ∃ n, h.stableFrom ≤ n ∧ AllTerminal (r.states n) := by
  classical
  have inv : ∀ n, h.stableFrom ≤ n → Certified (r.states n) ∧ Stable (r.states n) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => exact ⟨reachable_certified h.reached, h.stable⟩
    | succ n hn ih =>
      obtain ⟨he, ht⟩ := r.valid n
      have hc := checked_transition ih.1 he ht
      exact ⟨hc.1, (hc.2.2 (h.noFurtherFailure n hn) ih.2).1⟩
  let P : Nat → Prop := fun v => ∃ n, h.stableFrom ≤ n ∧ rank (r.states n) = v
  have hex : ∃ v, P v := ⟨rank (r.states h.stableFrom), h.stableFrom, le_rfl, rfl⟩
  obtain ⟨n, hn, hmin⟩ := Nat.find_spec hex
  have minimal : ∀ m, h.stableFrom ≤ m → rank (r.states n) ≤ rank (r.states m) := by
    intro m hm
    rw [hmin]
    exact Nat.find_min' hex ⟨m, hm, rfl⟩
  have constant : ∀ m, n ≤ m → r.states m = r.states n := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => rfl
    | succ m hm ih =>
      obtain ⟨he, ht⟩ := r.valid m
      have hc := (checked_transition (inv m (by omega)).1 he ht).2.2
        (h.noFurtherFailure m (by omega)) (inv m (by omega)).2
      have eqrank : rank (r.states (m + 1)) = rank (r.states m) := by
        apply le_antisymm hc.2.1
        rw [ih]
        exact minimal (m + 1) (by omega)
      exact (hc.2.2 eqrank).trans ih
  refine ⟨n, hn, ?_⟩
  by_contra hd
  obtain ⟨e, t, he, ht, hne⟩ := progress_exists (inv n hn).1 (inv n hn).2 hd
  have enabled : ∀ m, n ≤ m → ∃ u,
      coreStep (r.states m) e = some u ∧ u ≠ r.states m := by
    intro m hm
    rw [constant m hm]
    exact ⟨t, ht, hne⟩
  obtain ⟨m, hm, hme⟩ := h.fair n e he enabled
  obtain ⟨_, actual⟩ := r.valid m
  rw [hme, constant m hm, constant (m + 1) (by omega), ht] at actual
  exact hne (Option.some.inj actual)


/-- The named local states corresponding to the compact certificate representation. -/
inductive ParticipantState where
  | init | prepared | preCommit | committed | aborted
  deriving DecidableEq, Repr

def participantState (s : Core) (p : Bool) : ParticipantState :=
  match localState s p with
  | 0 => .init
  | 1 => .prepared
  | 2 => .preCommit
  | 3 => .committed
  | _ => .aborted

/-- Admission checks the complete current envelope, including epoch and sender. -/
def deliverPacket (s : Core) (p : Bool) (m : Packet) : Option Core :=
  if m.epoch ≠ s.epoch then none
  else if m = request s p then coreStep s (if p then 4 else 2)
  else if m = response s p then coreStep s (if p then 9 else 8)
  else none

theorem stale_epoch_rejected (s : Core) (p : Bool) (m : Packet)
    (h : m.epoch ≠ s.epoch) : deliverPacket s p m = none := by
  simp [deliverPacket, h]

private theorem persistent_and_packets {s t : Core} {e : Nat}
    (hs : Certified s) (he : e < 16) (ht : coreStep s e = some t) :
    Persistent s t ∧ PacketEvidence s t e := by
  have h := List.all_eq_true.mp (certified_checks hs).2 e (List.mem_range.mpr he)
  have raw : Certified t ∧ (terminalStable s t ∧ Persistent s t ∧ PacketEvidence s t e) ∧
      (operational e → Stable s → Stable t ∧ rank t ≤ rank s ∧
        (rank t = rank s → t = s)) := by
    simp only [transitionCheck, ht, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  exact raw.2.1.2

theorem votes_and_crashes_are_permanent {s t : Core} {e : Nat}
    (hs : Reachable s) (h : Step s e t) : Persistent s t := by
  cases h with
  | execute he ht => exact (persistent_and_packets (reachable_certified hs) he ht).1

theorem receives_consume_authentic_packets {s t : Core} {e : Nat}
    (hs : Reachable s) (h : Step s e t) : PacketEvidence s t e := by
  cases h with
  | execute he ht => exact (persistent_and_packets (reachable_certified hs) he ht).2

/-- The environment installs one owner value; no second owner may send within the epoch. -/
def AuthorizedSender (s : Core) (process epoch : Nat) : Prop :=
  process = s.owner ∧ epoch = s.epoch ∧ running s

theorem unique_epoch_coordinator {s : Core} {p q epoch : Nat}
    (hp : AuthorizedSender s p epoch) (hq : AuthorizedSender s q epoch) : p = q :=
  hp.1.trans hq.1.symm

/-- Deterministic replay fails on a disabled event; it never silently fabricates a step. -/
def runEvents : Core → List Nat → Option Core
  | s, [] => some s
  | s, e :: es => if e < 16 then (coreStep s e).bind (fun t => runEvents t es) else none

theorem runEvents_sound {s t : Core} {es : List Nat}
    (h : runEvents s es = some t) : Execution s es t := by
  induction es generalizing s with
  | nil => simp only [runEvents, Option.some.injEq] at h; subst t; exact .nil s
  | cons e es ih =>
    simp only [runEvents] at h
    split at h
    · next he =>
      cases ht : coreStep s e with
      | none => simp [ht] at h
      | some u =>
        simp only [ht, Option.bind_some] at h
        exact .cons (.execute he ht) (ih h)
    · simp at h

/-- A scheduler can withhold every message forever by taking ticks. -/
def idleRun (s : Core) : Run where
  states := fun _ => s
  events := fun _ => 15
  valid := fun _ => .execute (by decide) (by simp [coreStep])

theorem unfair_execution_need_not_complete :
    Reachable ((idleRun initial).states 0) ∧
    ∀ n, ¬AllTerminal ((idleRun initial).states n) := by
  refine ⟨⟨[], .nil initial⟩, ?_⟩
  intro n
  change ¬AllTerminal initial
  decide

/-- The original decision type is reused; the extra states describe protocol phases. -/
def finalDecision (s : Core) : Option DistributedTwoPhaseCommit.Decision :=
  if s.phase = 4 then some .commit else if s.phase = 5 then some .abort else none

/-- Votes are explicit input events, using the existing 2PC vote type. -/
def voteEvent (p : Bool) (v : DistributedTwoPhaseCommit.Vote) : Nat :=
  (if p then 4 else 2) + (if v = .no then 1 else 0)

/-- A reachable partial PreCommit exposes the unsafe unilateral timeout shortcut. -/
theorem naive_timeout_counterexample : ∃ s, Reachable s ∧ s.left = 2 ∧ s.right = 1 ∧
    ¬Agreement { s with left := 3, right := 4 } := by
  let s : Core := ⟨2, 1, 3, 7, 3, 0, 0, 2, 2, 0, 0, 0⟩
  refine ⟨s, ?_, by decide, by decide, by decide⟩
  refine ⟨[0, 1, 2, 4, 6, 7, 8, 9, 10, 0, 2], runEvents_sound ?_⟩
  decide


/-- Availability of the external accurate-view installation; no decision is read here. -/
def viewRepairCheck (n : Nat) : Bool :=
  let s := decode n
  if s.live / 2 % 4 = 0 ∨ Stable s then true
  else match coreStep s 14 with
    | none => false
    | some t => decide (Stable t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
-- Check view installation for every member of the finite invariant certificate.
theorem view_repair_checked : certificate.all viewRepairCheck = true := by decide

/-- A live survivor admits a finite completion, including accurate view installation.
The service step is explicit, not an assumption that a decision already exists. -/
theorem completion_path_after_detection {s : Core} (hs : Reachable s)
    (hleft : s.live / 2 % 4 ≠ 0) : ∃ es t, Execution s es t ∧ AllTerminal t := by
  by_cases hstable : Stable s
  · exact completion_path_exists hs hstable
  have hc : certificate.contains (encode s) = true ∧ decode (encode s) = s := by
    simpa [Certified, certifiedBool] using reachable_certified hs
  have hv := CodeTree.all_sound view_repair_checked hc.1
  simp only [viewRepairCheck, hc.2, if_neg (by tauto : ¬(s.live / 2 % 4 = 0 ∨ Stable s))] at hv
  cases ht : coreStep s 14 with
  | none => simp [ht] at hv
  | some t =>
    have hst : Stable t := by simpa [ht] using hv
    have step : Step s 14 t := .execute (by decide) ht
    have reached : Reachable t := hs.after (.cons step (.nil t))
    obtain ⟨es, u, path, hd⟩ := completion_path_exists reached hst
    exact ⟨14 :: es, u, .cons step path, hd⟩

structure DistributedThreePhaseCommitSuite : Prop where
  agreement : ∀ s, Reachable s → Agreement s
  terminal_stability : ∀ s t e, Reachable s → Step s e t → terminalStable s t
  yes_provenance : ∀ s, Reachable s → (s.left = 3 ∨ s.right = 3) → s.yes = 3
  completion_path : ∀ s, Reachable s → Stable s →
    ∃ es t, Execution s es t ∧ AllTerminal t
  survivor_completion : ∀ s, Reachable s → s.live / 2 % 4 ≠ 0 →
    ∃ es t, Execution s es t ∧ AllTerminal t
  packet_provenance : ∀ s t e, Reachable s → Step s e t → PacketEvidence s t e
  fair_completion : ∀ r, ProgressAssumptions r → ∃ n, AllTerminal (r.states n)

theorem distributed_three_phase_commit_master_suite : DistributedThreePhaseCommitSuite where
  agreement := fun _ => reachable_agreement
  terminal_stability := fun _ _ _ => terminal_decision_stability
  yes_provenance := fun _ => commit_requires_yes
  completion_path := fun _ => completion_path_exists
  survivor_completion := fun _ => completion_path_after_detection
  packet_provenance := fun _ _ _ => receives_consume_authentic_packets
  fair_completion := fun r h => by
    obtain ⟨n, _, hn⟩ := completion_under_progress_assumptions r h
    exact ⟨n, hn⟩


end DistributedThreePhaseCommit
