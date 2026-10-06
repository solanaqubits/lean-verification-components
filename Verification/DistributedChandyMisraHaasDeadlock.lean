/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

/-!
# Static-epoch AND wait-graph probe detection

An operational edge-chasing specialization inspired by CMH. The graph is fixed
throughout an execution; arbitrary dynamic changes require a separate argument.
Probe flooding has no duplicate suppression. A cycle here is a nonempty closed
walk. No physical resource manager, OR-model, failure or runtime is verified.
-/
namespace DistributedChandyMisraHaasDeadlock

abbrev ProcessId (n : Nat) := Fin n

structure WFG (n : Nat) where
  edges : Finset (ProcessId n × ProcessId n)
  deriving DecidableEq

def WFG.waitsFor (g : WFG n) (p q : ProcessId n) : Prop := (p, q) ∈ g.edges
instance (g : WFG n) (p q : ProcessId n) : Decidable (g.waitsFor p q) :=
  inferInstanceAs (Decidable ((p, q) ∈ g.edges))
def Blocked (g : WFG n) (p : ProcessId n) : Prop := ∃ q, g.waitsFor p q

inductive WaitPath (g : WFG n) : Nat → ProcessId n → ProcessId n → Prop where
  | nil (p) : WaitPath g 0 p p
  | cons {k p q r} : g.waitsFor p q → WaitPath g k q r → WaitPath g (k + 1) p r

def WaitCycle (g : WFG n) (i : ProcessId n) : Prop := ∃ k, WaitPath g (k + 1) i i
def Acyclic (g : WFG n) : Prop := ∀ i, ¬WaitCycle g i

theorem WaitPath.append {g : WFG n} {k l p q r}
    (h : WaitPath g k p q) (j : WaitPath g l q r) : WaitPath g (k + l) p r := by
  induction h with
  | nil => simpa using j
  | cons e _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WaitPath.cons e (ih j)

theorem WaitCycle.blocked {g : WFG n} {i} (h : WaitCycle g i) : Blocked g i := by
  obtain ⟨k, h⟩ := h
  cases h with
  | cons e _ => exact ⟨_, e⟩

structure Probe (n : Nat) where
  initiator : ProcessId n
  sender : ProcessId n
  receiver : ProcessId n
  deriving DecidableEq, Repr

def outgoing (g : WFG n) (i p : ProcessId n) : List (Probe n) :=
  ((List.finRange n).filter (fun q => decide (g.waitsFor p q))).map (fun q => ⟨i, p, q⟩)

theorem mem_outgoing {g : WFG n} {i p} {m : Probe n} :
    m ∈ outgoing g i p ↔ m.initiator = i ∧ m.sender = p ∧ g.waitsFor p m.receiver := by
  simp only [outgoing, List.mem_map, List.mem_filter, List.mem_finRange,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨q, hq, rfl⟩; exact ⟨rfl, rfl, hq⟩
  · rintro ⟨hi, hp, he⟩
    refine ⟨m.receiver, he, ?_⟩
    cases m; simp_all

structure State (n : Nat) where
  queue : List (Probe n)
  sent : List (Probe n)
  detected : Finset (ProcessId n)
  deriving DecidableEq

def initial : State n := ⟨[], [], ∅⟩
def enqueue (s : State n) (ms : List (Probe n)) : State n :=
  { s with queue := s.queue ++ ms, sent := s.sent ++ ms }

inductive Event (n : Nat) where
  | initiate (i : ProcessId n)
  | deliver (m : Probe n)
  | idle
  deriving DecidableEq

/-- Receives select a real queue occurrence; no path or safety predicate is a guard.
Fanout is an atomic local enqueue, not atomic network delivery. -/
inductive Step (g : WFG n) : State n → Event n → State n → Prop where
  | initiate (s i) (hb : Blocked g i) :
      Step g s (.initiate i) (enqueue s (outgoing g i i))
  | forward (s m before after) (hq : s.queue = before ++ m :: after)
      (hne : m.receiver ≠ m.initiator) (hb : Blocked g m.receiver) :
      Step g s (.deliver m)
        (enqueue { s with queue := before ++ after } (outgoing g m.initiator m.receiver))
  | detect (s m before after) (hq : s.queue = before ++ m :: after)
      (heq : m.receiver = m.initiator) (hb : Blocked g m.receiver) :
      Step g s (.deliver m)
        { s with queue := before ++ after, detected := insert m.initiator s.detected }
  | absorb (s m before after) (hq : s.queue = before ++ m :: after)
      (ha : ¬Blocked g m.receiver) :
      Step g s (.deliver m) { s with queue := before ++ after }
  | idle (s) : Step g s .idle s

inductive Execution (g : WFG n) : State n → State n → Prop where
  | nil (s) : Execution g s s
  | cons {s t u e} : Step g s e t → Execution g t u → Execution g s u

def Reachable (g : WFG n) (s : State n) : Prop := Execution g initial s

def ProbeValid (g : WFG n) (m : Probe n) : Prop :=
  ∃ k, WaitPath g k m.initiator m.sender ∧ g.waitsFor m.sender m.receiver

def Invariant (g : WFG n) (s : State n) : Prop :=
  (∀ m ∈ s.queue, ProbeValid g m) ∧ (∀ m ∈ s.sent, ProbeValid g m) ∧
  (∀ i ∈ s.detected, WaitCycle g i)

private theorem outgoing_valid {g : WFG n} {i p k} (h : WaitPath g k i p) :
    ∀ m ∈ outgoing g i p, ProbeValid g m := by
  intro m hm
  obtain ⟨hi, hp, he⟩ := mem_outgoing.mp hm
  exact ⟨k, hi.symm ▸ hp.symm ▸ h, hp.symm ▸ he⟩

private theorem remove_valid {g : WFG n} {s : State n} {m before after}
    (h : ∀ m ∈ s.queue, ProbeValid g m) (hq : s.queue = before ++ m :: after) :
    ∀ x ∈ before ++ after, ProbeValid g x := by
  intro x hx
  apply h x
  rw [hq]
  simpa only [List.mem_append, List.mem_cons] using
    (show x ∈ before ∨ x = m ∨ x ∈ after from
      (List.mem_append.mp hx).elim Or.inl (fun h => Or.inr (Or.inr h)))

theorem step_preserves_invariant {g : WFG n} {s t : State n} {e}
    (h : Step g s e t) (hs : Invariant g s) : Invariant g t := by
  rcases hs with ⟨hq, hh, hd⟩
  cases h with
  | initiate i hb =>
    have ho := outgoing_valid (WaitPath.nil (g := g) i)
    exact ⟨fun m hm => (List.mem_append.mp hm).elim (hq m) (ho m),
      fun m hm => (List.mem_append.mp hm).elim (hh m) (ho m), hd⟩
  | forward m before after eq ne hb =>
    have hm : m ∈ s.queue := by simp [eq]
    obtain ⟨k, hp, he⟩ := hq m hm
    have ho := outgoing_valid (hp.append (.cons he (.nil _)))
    exact ⟨fun x hx => (List.mem_append.mp hx).elim
        (remove_valid hq eq x) (ho x),
      fun x hx => (List.mem_append.mp hx).elim (hh x) (ho x), hd⟩
  | detect m before after eq heq hb =>
    refine ⟨remove_valid hq eq, hh, ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have hm : m ∈ s.queue := by simp [eq]
      obtain ⟨k, hp, he⟩ := hq m hm
      exact ⟨k, heq ▸ hp.append (.cons he (.nil _))⟩
    · exact hd i hi
  | absorb m before after eq ha => exact ⟨remove_valid hq eq, hh, hd⟩
  | idle => exact ⟨hq, hh, hd⟩

theorem execution_preserves_invariant {g : WFG n} {s t}
    (h : Execution g s t) (hs : Invariant g s) : Invariant g t := by
  induction h with
  | nil => exact hs
  | cons h _ ih => exact ih (step_preserves_invariant h hs)

theorem reachable_invariant {g : WFG n} {s} (h : Reachable g s) : Invariant g s :=
  execution_preserves_invariant h (by simp [Invariant, initial])

/-- Sent probes have an actual edge in this fixed graph. -/
theorem probe_transmission_validity {g : WFG n} {s m}
    (h : Reachable g s) (hm : m ∈ s.sent) : g.waitsFor m.sender m.receiver := by
  obtain ⟨_, _, he⟩ := (reachable_invariant h).2.1 m hm
  exact he

theorem probe_path_reconstruction {g : WFG n} {s m}
    (h : Reachable g s) (hm : m ∈ s.queue ∨ m ∈ s.sent) :
    ∃ k, WaitPath g k m.initiator m.sender ∧ g.waitsFor m.sender m.receiver :=
  hm.elim ((reachable_invariant h).1 m) ((reachable_invariant h).2.1 m)

/-- Soundness is about the graph of the current fixed detection epoch. -/
theorem cycle_detection_soundness {g : WFG n} {s i}
    (h : Reachable g s) (hi : i ∈ s.detected) : WaitCycle g i :=
  (reachable_invariant h).2.2 i hi

theorem phantom_deadlock_absence {g : WFG n} (ha : Acyclic g) {s}
    (h : Reachable g s) : s.detected = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  exact ha i (cycle_detection_soundness h hi)

theorem no_probe_without_path {g : WFG n} {s m}
    (h : Reachable g s) (hn : ¬∃ k, WaitPath g k m.initiator m.sender) :
    m ∉ s.queue ∧ m ∉ s.sent := by
  constructor <;> intro hm
  · obtain ⟨k, hp, _⟩ := probe_path_reconstruction h (Or.inl hm); exact hn ⟨k, hp⟩
  · obtain ⟨k, hp, _⟩ := probe_path_reconstruction h (Or.inr hm); exact hn ⟨k, hp⟩

theorem Execution.trans {g : WFG n} {s t u}
    (h : Execution g s t) (k : Execution g t u) : Execution g s u := by
  induction h with
  | nil => exact k
  | cons h _ ih => exact .cons h (ih k)

theorem initiation_enqueues {g : WFG n} {s t i}
    (h : Step g s (.initiate i) t) {q} (he : g.waitsFor i q) :
    (⟨i, i, q⟩ : Probe n) ∈ t.queue := by
  cases h
  simp [enqueue, mem_outgoing, he]

theorem delivery_effect {g : WFG n} {s t m}
    (h : Step g s (.deliver m) t) (hb : Blocked g m.receiver) :
    (m.receiver = m.initiator → m.initiator ∈ t.detected) ∧
    (m.receiver ≠ m.initiator → ∀ q, g.waitsFor m.receiver q →
      (⟨m.initiator, m.receiver, q⟩ : Probe n) ∈ t.queue) := by
  cases h <;> simp_all [enqueue, mem_outgoing]

theorem detected_monotone {g : WFG n} {s t e} (h : Step g s e t) :
    s.detected ⊆ t.detected := by
  cases h <;> simp [enqueue]

/-- A queued probe can be delivered without a path or cycle check. -/
theorem blocked_delivery_exists {g : WFG n} {s m}
    (hm : m ∈ s.queue) (hb : Blocked g m.receiver) :
    ∃ t, Step g s (.deliver m) t := by
  obtain ⟨before, after, hq⟩ := List.mem_iff_append.mp hm
  by_cases he : m.receiver = m.initiator
  · exact ⟨_, .detect s m before after hq he hb⟩
  · exact ⟨_, .forward s m before after hq he hb⟩

private theorem follow_path {g : WFG n} {k q i} (hp : WaitPath g k q i)
    (hi : Blocked g i) : ∀ (s : State n) (p : ProcessId n),
    (⟨i, p, q⟩ : Probe n) ∈ s.queue → ∃ t, Execution g s t ∧ i ∈ t.detected := by
  induction hp with
  | nil =>
    intro s p hm
    obtain ⟨t, ht⟩ := blocked_delivery_exists hm hi
    exact ⟨t, .cons ht (.nil t), (delivery_effect ht hi).1 rfl⟩
  | @cons k q r i edge tail ih =>
    intro s p hm
    have hb : Blocked g q := ⟨r, edge⟩
    obtain ⟨t, ht⟩ := blocked_delivery_exists hm hb
    by_cases he : q = i
    · exact ⟨t, .cons ht (.nil t), (delivery_effect ht hb).1 he⟩
    · have hnext := (delivery_effect ht hb).2 he r edge
      obtain ⟨u, hu, hd⟩ := ih hi t q hnext
      exact ⟨u, .cons ht hu, hd⟩

/-- Existence alone makes no guarantee about an arbitrary scheduler. -/
theorem cycle_detection_path_exists {g : WFG n} {i} (hc : WaitCycle g i)
    (s : State n) : ∃ t, Execution g s t ∧ i ∈ t.detected := by
  have hb := hc.blocked
  obtain ⟨k, hp⟩ := hc
  cases hp with
  | @cons k i q _ he hp =>
    let t := enqueue s (outgoing g i i)
    have hs : Step g s (.initiate i) t := .initiate s i hb
    obtain ⟨u, hu, hd⟩ := follow_path hp hb t i (initiation_enqueues hs he)
    exact ⟨u, .cons hs hu, hd⟩

structure Run (g : WFG n) where
  states : Nat → State n
  events : Nat → Event n
  valid : ∀ t, Step g (states t) (events t) (states (t + 1))

/-- Every pending probe payload is eventually served. This is a scheduling/delivery
assumption, not an assumption of a detected cycle or a wall-clock bound. -/
def DeliveryFair (r : Run g) : Prop := ∀ t m, m ∈ (r.states t).queue →
  ∃ u, t ≤ u ∧ r.events u = .deliver m

private theorem fair_follow_path {g : WFG n} (r : Run g) (hf : DeliveryFair r)
    {k q i} (hp : WaitPath g k q i) (hi : Blocked g i) :
    ∀ t p, (⟨i, p, q⟩ : Probe n) ∈ (r.states t).queue →
      ∃ u, t ≤ u ∧ i ∈ (r.states u).detected := by
  induction hp with
  | nil =>
    intro t p hm
    obtain ⟨u, hu, he⟩ := hf t _ hm
    have hs := r.valid u
    rw [he] at hs
    exact ⟨u + 1, by omega, (delivery_effect hs hi).1 rfl⟩
  | @cons k q v i edge tail ih =>
    intro t p hm
    obtain ⟨u, hu, he⟩ := hf t _ hm
    have hs := r.valid u
    rw [he] at hs
    have hb : Blocked g q := ⟨v, edge⟩
    by_cases eq : q = i
    · exact ⟨u + 1, by omega, (delivery_effect hs hb).1 eq⟩
    · obtain ⟨z, hz, hd⟩ := ih hi (u + 1) q ((delivery_effect hs hb).2 eq v edge)
      exact ⟨z, by omega, hd⟩

/-- Completeness for an initiated cycle under explicit delivery fairness, with a
fixed WFG. An upstream process is not asserted to belong to the cycle. -/
theorem cycle_eventually_detected {g : WFG n} (r : Run g) (hf : DeliveryFair r)
    {i t} (hc : WaitCycle g i) (hi : r.events t = .initiate i) :
    ∃ u, t ≤ u ∧ i ∈ (r.states u).detected := by
  have hb := hc.blocked
  obtain ⟨k, hp⟩ := hc
  cases hp with
  | @cons k i q _ he hp =>
    have hs := r.valid t
    rw [hi] at hs
    obtain ⟨u, hu, hd⟩ := fair_follow_path r hf hp hb (t + 1) i (initiation_enqueues hs he)
    exact ⟨u, by omega, hd⟩

/-- Strictly increasing vertex ranks exclude every nonempty closed walk. -/
theorem acyclic_of_rank {g : WFG n} (rank : ProcessId n → Nat)
    (he : ∀ p q, g.waitsFor p q → rank p < rank q) : Acyclic g := by
  have bound : ∀ {k p q}, WaitPath g k p q → rank p + k ≤ rank q := by
    intro k p q h
    induction h with
    | nil => omega
    | cons edge _ ih => have := he _ _ edge; omega
  intro i hc
  obtain ⟨k, hp⟩ := hc
  have := bound hp
  omega

/-- Diagnostic extension only: graph changes retain old probes. This deliberately
lacks a resource-manager protocol or an epoch-reset contract. -/
inductive DynamicTrace : WFG n → State n → List (WFG n) → WFG n → State n → Prop where
  | nil (g s) : DynamicTrace g s [g] g s
  | protocol {g s t es h u e} : Step g s e t → DynamicTrace g t es h u →
      DynamicTrace g s (g :: es) h u
  | change {g h s es k t} : DynamicTrace h s es k t → DynamicTrace g s (g :: es) k t

namespace Counterexample

def g0 : WFG 3 := ⟨{(0, 1)}⟩
def g1 : WFG 3 := ⟨{(0, 1), (1, 2)}⟩
def g2 : WFG 3 := ⟨{(0, 1), (2, 0)}⟩
def s1 : State 3 := enqueue initial (outgoing g0 0 0)
def s2 : State 3 := enqueue { s1 with queue := [] } (outgoing g1 0 1)
def s3 : State 3 := enqueue { s2 with queue := [] } (outgoing g2 0 2)
def s4 : State 3 := { s3 with queue := [], detected := {0} }

theorem graphs_acyclic : Acyclic g0 ∧ Acyclic g1 ∧ Acyclic g2 := by
  refine ⟨acyclic_of_rank Fin.val ?_, acyclic_of_rank Fin.val ?_,
    acyclic_of_rank (fun p => (p.val + 1) % 3) ?_⟩ <;> decide

theorem trace : DynamicTrace g0 initial [g0, g0, g1, g1, g2, g2, g2] g2 s4 := by
  have h1 : Step g0 initial (.initiate 0) s1 := .initiate _ _ ⟨1, by decide⟩
  have h2 : Step g1 s1 (.deliver ⟨0, 0, 1⟩) s2 :=
    .forward _ _ [] [] (by decide) (by decide) ⟨2, by decide⟩
  have h3 : Step g2 s2 (.deliver ⟨0, 1, 2⟩) s3 :=
    .forward _ _ [] [] (by decide) (by decide) ⟨0, by decide⟩
  have h4 : Step g2 s3 (.deliver ⟨0, 2, 0⟩) s4 :=
    .detect _ _ [] [] (by decide) rfl ⟨1, by decide⟩
  exact .protocol h1 (.change (.protocol h2 (.change (.protocol h3 (.protocol h4 (.nil _ _))))))

end Counterexample

/-- All instantaneous graphs are acyclic, yet old probes form a temporal cycle.
This refutes send-time edge checks as a sufficient dynamic soundness condition. -/
theorem dynamic_send_checks_insufficient :
    ∃ (gs : List (WFG 3)) (last : WFG 3) (s : State 3),
      DynamicTrace Counterexample.g0 initial gs last s ∧
      (∀ g ∈ gs, Acyclic g) ∧ Acyclic last ∧ (0 : Fin 3) ∈ s.detected := by
  refine ⟨_, _, _, Counterexample.trace, ?_, Counterexample.graphs_acyclic.2.2, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact Counterexample.graphs_acyclic.1
          | exact Counterexample.graphs_acyclic.2.1
          | exact Counterexample.graphs_acyclic.2.2

/-- An explicit boundary for quasi-static use: a graph replacement starts a fresh
isolated detector, discarding pending probes and reports. No reset implementation. -/
inductive EpochReachable : WFG n → State n → Prop where
  | initial (g : WFG n) : EpochReachable g initial
  | step {g : WFG n} {s t : State n} {e : Event n} :
      EpochReachable g s → Step g s e t → EpochReachable g t
  | reset {g : WFG n} {s : State n} (h : EpochReachable g s) (next : WFG n) :
      EpochReachable next initial

theorem epoch_reachable_static {g : WFG n} {s} (h : EpochReachable g s) : Reachable g s := by
  induction h with
  | initial => exact .nil _
  | step _ hs ih => exact ih.trans (.cons hs (.nil _))
  | reset => exact .nil _

theorem reset_epoch_soundness {g : WFG n} {s i} (h : EpochReachable g s)
    (hi : i ∈ s.detected) : WaitCycle g i :=
  cycle_detection_soundness (epoch_reachable_static h) hi

def idleRun (g : WFG n) (s : State n) : Run g where
  states := fun _ => s
  events := fun _ => .idle
  valid := fun _ => .idle s

def twoCycle : WFG 2 := ⟨{(0, 1), (1, 0)}⟩
def waiting : State 2 := enqueue initial (outgoing twoCycle 0 0)

theorem two_cycle : WaitCycle twoCycle 0 :=
  ⟨1, .cons (q := (1 : Fin 2)) (by decide) (.cons (by decide) (.nil _))⟩

/-- Reliable storage without eventual scheduling does not imply detection. -/
theorem unfair_execution_counterexample :
    WaitCycle twoCycle 0 ∧ Reachable twoCycle waiting ∧
    (∀ t, (0 : Fin 2) ∉ ((idleRun twoCycle waiting).states t).detected) ∧
    ¬DeliveryFair (idleRun twoCycle waiting) := by
  refine ⟨two_cycle, .cons (.initiate _ _ ⟨1, by decide⟩) (.nil _), ?_, ?_⟩
  · intro t; simp [idleRun, waiting, enqueue, initial]
  · intro hf
    have hm : (⟨0, 0, 1⟩ : Probe 2) ∈ waiting.queue := by decide
    obtain ⟨u, _, hu⟩ := hf 0 _ hm
    cases hu

structure DistributedChandyMisraHaasSuite : Prop where
  path_provenance : ∀ n (g : WFG n) s m, Reachable g s → m ∈ s.queue ∨ m ∈ s.sent →
    ProbeValid g m
  soundness : ∀ n (g : WFG n) s i, Reachable g s → i ∈ s.detected → WaitCycle g i
  acyclic_safety : ∀ n (g : WFG n) s, Acyclic g → Reachable g s → s.detected = ∅
  detection_path : ∀ n (g : WFG n) i s, WaitCycle g i →
    ∃ t, Execution g s t ∧ i ∈ t.detected
  fair_detection : ∀ n (g : WFG n) (r : Run g) i t, DeliveryFair r →
    WaitCycle g i → r.events t = .initiate i → ∃ u, t ≤ u ∧ i ∈ (r.states u).detected
  fresh_epoch_safety : ∀ n (g : WFG n) s i, EpochReachable g s →
    i ∈ s.detected → WaitCycle g i

theorem distributed_chandy_misra_haas_master_suite : DistributedChandyMisraHaasSuite where
  path_provenance := fun _ _ _ _ => probe_path_reconstruction
  soundness := fun _ _ _ _ => cycle_detection_soundness
  acyclic_safety := fun _ _ _ ha hr => phantom_deadlock_absence ha hr
  detection_path := fun _ _ _ s hc => cycle_detection_path_exists hc s
  fair_detection := fun _ _ r _ _ hf hc he => cycle_eventually_detected r hf hc he
  fresh_epoch_safety := fun _ _ _ _ => reset_epoch_soundness

end DistributedChandyMisraHaasDeadlock
