/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedLamportClocks
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Max

/-! A fixed-membership, crash-free asynchronous Ricart–Agrawala model.
Request fanout is one local enqueue; delivery and reply sending are separate.
Finite sets represent unordered, uniquely identified messages and receipt history.
Historical replies never count for a fresh request. No fairness is needed for safety. -/
namespace DistributedRicartAgrawalaMutex

abbrev NodeId (n : ℕ) := Fin n

inductive NodeState where
  | released
  | wanted (ts : ℕ)
  | held (ts : ℕ)
  deriving DecidableEq, Repr

structure Request (n : ℕ) where
  ts : ℕ
  owner : NodeId n
  deriving DecidableEq, Repr

def RequestPriority (t₁ : ℕ) (i : NodeId n) (t₂ : ℕ) (j : NodeId n) : Prop :=
  t₁ < t₂ ∨ (t₁ = t₂ ∧ i.val < j.val)

def Earlier (r q : Request n) : Prop := RequestPriority r.ts r.owner q.ts q.owner

instance (r q : Request n) : Decidable (Earlier r q) :=
  inferInstanceAs (Decidable (_ < _ ∨ (_ = _ ∧ _ < _)))

theorem priority_irreflexive (r : Request n) : ¬ Earlier r r := by
  simp [Earlier, RequestPriority]

theorem priority_transitive {a b c : Request n} (h : Earlier a b) (k : Earlier b c) :
    Earlier a c := by
  unfold Earlier RequestPriority at *
  omega

theorem priority_asymmetric {a b : Request n} (h : Earlier a b) : ¬ Earlier b a := by
  intro k
  exact priority_irreflexive a (priority_transitive h k)

theorem priority_trichotomy {r q : Request n} (hne : r.owner ≠ q.owner) :
    Earlier r q ∨ Earlier q r := by
  have hv : r.owner.val ≠ q.owner.val := fun h => hne (Fin.ext h)
  unfold Earlier RequestPriority
  omega

def Request.rank (r : Request n) : ℕ := n * r.ts + r.owner.val

theorem priority_rank {r q : Request n} (h : Earlier r q) : r.rank < q.rank := by
  rcases h with h | ⟨h, hi⟩
  · have hm := Nat.mul_le_mul_left n (show r.ts + 1 ≤ q.ts by omega)
    simp only [Nat.mul_add, Nat.mul_one] at hm
    have := r.owner.isLt
    unfold Request.rank
    omega
  · change r.ts = q.ts at h
    unfold Request.rank
    rw [h]
    omega

structure State (n : ℕ) where
  mode : NodeId n → NodeState
  clock : NodeId n → ℕ
  requests : Finset (Request n)
  seen : Finset (Request n × NodeId n)
  replied : Finset (Request n × NodeId n)
  delivered : Finset (Request n × NodeId n)

/-- Each pair is a uniquely identified REQUEST from r.owner to j or REPLY back.
The histories encode the pending queues as set differences, without a FIFO order. -/
def pendingRequests (s : State n) (r : Request n) (j : NodeId n) : Prop :=
  r ∈ s.requests ∧ j ≠ r.owner ∧ (r, j) ∉ s.seen

def pendingReplies (s : State n) : Finset (Request n × NodeId n) := s.replied \ s.delivered

def Active (s : State n) (i : NodeId n) (t : ℕ) : Prop :=
  s.mode i = .wanted t ∨ s.mode i = .held t

def ReplyCondition (s : State n) (r : Request n) (j : NodeId n) : Prop :=
  s.mode j = .released ∨ ∃ t, s.mode j = .wanted t ∧ Earlier r ⟨t, j⟩

def Deferred (s : State n) (r : Request n) (j : NodeId n) : Prop :=
  (r, j) ∈ s.seen ∧ (r, j) ∉ s.replied ∧ ¬ ReplyCondition s r j

def initial : State n := ⟨fun _ => .released, fun _ => 0, ∅, ∅, ∅, ∅⟩

inductive Event (n : ℕ) where
  | request (i : NodeId n)
  | receive (r : Request n) (j : NodeId n)
  | reply (r : Request n) (j : NodeId n)
  | deliver (r : Request n) (j : NodeId n)
  | enter (i : NodeId n) (t : ℕ)
  | leave (i : NodeId n) (t : ℕ)
  | idle
  deriving DecidableEq, Repr

def Enabled (s : State n) : Event n → Prop
  | .request i => s.mode i = .released
  | .receive r j => pendingRequests s r j
  | .reply r j => (r, j) ∈ s.seen ∧ (r, j) ∉ s.replied ∧ ReplyCondition s r j
  | .deliver r j => (r, j) ∈ s.replied ∧ (r, j) ∉ s.delivered
  | .enter i t => s.mode i = .wanted t ∧ ∀ j, j ≠ i → (⟨t, i⟩, j) ∈ s.delivered
  | .leave i t => s.mode i = .held t
  | .idle => True

instance (s : State n) (r : Request n) (j : NodeId n) : Decidable (ReplyCondition s r j) :=
  match hm : s.mode j with
  | .released => isTrue (Or.inl hm)
  | .held t => isFalse (by
      rintro (hz | ⟨u, hu, _⟩)
      · rw [hm] at hz; cases hz
      · rw [hm] at hu; cases hu)
  | .wanted t =>
    if hp : Earlier r ⟨t, j⟩ then isTrue (Or.inr ⟨t, hm, hp⟩)
    else isFalse (by
      rintro (hz | ⟨u, hu, hlt⟩)
      · rw [hm] at hz; cases hz
      · have ht := NodeState.wanted.inj (hm.symm.trans hu)
        subst u; exact hp hlt)

instance (s : State n) (r : Request n) (j : NodeId n) : Decidable (Deferred s r j) :=
  inferInstanceAs (Decidable ((r, j) ∈ s.seen ∧ (r, j) ∉ s.replied ∧ ¬ ReplyCondition s r j))

instance (s : State n) (e : Event n) : Decidable (Enabled s e) := by
  cases e <;> simp only [Enabled, pendingRequests] <;> infer_instance

/-- Receiving a REQUEST advances the local clock; a new request uses a strict tick.
Replies are separated from receipt so delayed local scheduling is explicit. -/
def next (s : State n) : Event n → State n
  | .request i =>
    { s with
      mode := Function.update s.mode i (.wanted (s.clock i + 1))
      clock := Function.update s.clock i (s.clock i + 1)
      requests := insert ⟨s.clock i + 1, i⟩ s.requests }
  | .receive r j =>
    { s with
      seen := insert (r, j) s.seen
      clock := Function.update s.clock j (max (s.clock j) r.ts + 1) }
  | .reply r j => { s with replied := insert (r, j) s.replied }
  | .deliver r j => { s with delivered := insert (r, j) s.delivered }
  | .enter i t => { s with mode := Function.update s.mode i (.held t) }
  | .leave i _ => { s with mode := Function.update s.mode i .released }
  | .idle => s

def Step (s : State n) (e : Event n) (u : State n) : Prop :=
  Enabled s e ∧ u = next s e

inductive Execution : State n → State n → Prop where
  | refl (s) : Execution s s
  | tail {s u v e} : Execution s u → Step u e v → Execution s v

def Reachable (s : State n) : Prop := Execution initial s

structure Invariant (s : State n) : Prop where
  active_clock : ∀ i t, Active s i t → t ≤ s.clock i
  active_request : ∀ i t, Active s i t → ⟨t, i⟩ ∈ s.requests
  seen_origin : ∀ r j, (r, j) ∈ s.seen → r ∈ s.requests ∧ j ≠ r.owner
  seen_clock : ∀ r j, (r, j) ∈ s.seen → r.ts < s.clock j
  reply_origin : ∀ r j, (r, j) ∈ s.replied → (r, j) ∈ s.seen
  delivered_origin : ∀ r j, (r, j) ∈ s.delivered → (r, j) ∈ s.replied
  permission_order : ∀ r j, (r, j) ∈ s.replied → ∀ t, Active s j t → Earlier r ⟨t, j⟩
  held_barrier : ∀ i t, s.mode i = .held t → ∀ j, j ≠ i → (⟨t, i⟩, j) ∈ s.delivered

private theorem initial_invariant : Invariant (initial : State n) := by
  constructor <;> simp [initial, Active]

theorem step_preserves_invariant {s : State n} (h : Invariant s) {e}
    (he : Enabled s e) : Invariant (next s e) := by
  rcases h with ⟨hc, hr, ho, hs, hp, hd, hx, hb⟩
  cases e with
  | request a =>
    constructor
    · intro i t ha
      by_cases hi : i = a
      · subst i; simp only [Active, next, Function.update_self,
        NodeState.wanted.injEq, reduceCtorEq, or_false] at ha; subst t; simp [next]
      · simpa [next, hi] using hc i t (by simpa [Active, next, hi] using ha)
    · intro i t ha
      by_cases hi : i = a
      · subst i; simp only [Active, next, Function.update_self,
        NodeState.wanted.injEq, reduceCtorEq, or_false] at ha; subst t; simp [next]
      · exact Finset.mem_insert_of_mem (hr i t (by simpa [Active, next, hi] using ha))
    · intro r j hm; exact ⟨Finset.mem_insert_of_mem (ho r j hm).1, (ho r j hm).2⟩
    · intro r j hm
      by_cases hj : j = a
      · subst j; have := hs r a hm; simp [next]; omega
      · simpa [next, hj] using hs r j hm
    · exact hp
    · exact hd
    · intro r j hm t ha
      by_cases hj : j = a
      · subst j; simp only [Active, next, Function.update_self,
        NodeState.wanted.injEq, reduceCtorEq, or_false] at ha; subst t
        have ht := hs r a (hp r a hm)
        exact Or.inl (show r.ts < s.clock a + 1 by omega)
      · exact hx r j hm t (by simpa [Active, next, hj] using ha)
    · intro i t hi j hj
      by_cases ha : i = a
      · subst i; simp only [next, Function.update_self, reduceCtorEq] at hi
      · exact hb i t (by simpa [next, ha] using hi) j hj
  | receive r a =>
    constructor
    · intro i t ha
      by_cases hi : i = a
      · subst i; have := hc a t ha; simp [next]; omega
      · simpa [next, hi] using hc i t ha
    · exact hr
    · intro q j hm
      rcases Finset.mem_insert.mp hm with eq | hm
      · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; exact ⟨he.1, he.2.1⟩
      · exact ho q j hm
    · intro q j hm
      rcases Finset.mem_insert.mp hm with eq | hm
      · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; simp [next]; omega
      · by_cases hj : j = a
        · subst j; have := hs q a hm; simp [next]; omega
        · simpa [next, hj] using hs q j hm
    · intro q j hm; exact Finset.mem_insert_of_mem (hp q j hm)
    · exact hd
    · exact hx
    · exact hb
  | reply r a =>
    refine ⟨hc, hr, ho, hs, ?_, ?_, ?_, hb⟩
    · intro q j hm
      rcases Finset.mem_insert.mp hm with eq | hm
      · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; exact he.1
      · exact hp q j hm
    · intro q j hm; exact Finset.mem_insert_of_mem (hd q j hm)
    · intro q j hm t ha
      rcases Finset.mem_insert.mp hm with eq | hm
      · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩
        rcases he.2.2 with hz | ⟨u, hu, hlt⟩
        · simp [Active, next, hz] at ha
        · rcases ha with ht | ht
          · have eq := NodeState.wanted.inj (hu.symm.trans ht)
            simpa [eq] using hlt
          · change s.mode j = .held t at ht
            rw [hu] at ht
            cases ht
      · exact hx q j hm t ha
  | deliver r a =>
    refine ⟨hc, hr, ho, hs, hp, ?_, hx, ?_⟩
    · intro q j hm
      rcases Finset.mem_insert.mp hm with eq | hm
      · rcases Prod.mk.inj eq with ⟨rfl, rfl⟩; exact he.1
      · exact hd q j hm
    · intro i t hi j hj; exact Finset.mem_insert_of_mem (hb i t hi j hj)
  | enter a u =>
    have lift : ∀ i t, Active (next s (.enter a u)) i t → Active s i t := by
      intro i t ha
      by_cases hi : i = a
      · subst i; simp only [Active, next, Function.update_self,
        reduceCtorEq, NodeState.held.injEq, false_or] at ha; subst t; exact Or.inl he.1
      · simpa [Active, next, hi] using ha
    refine ⟨fun i t ha => hc i t (lift i t ha), fun i t ha => hr i t (lift i t ha),
      ho, hs, hp, hd, fun r j hm t ha => hx r j hm t (lift j t ha), ?_⟩
    intro i t hi j hj
    by_cases ha : i = a
    · subst i; simp only [next, Function.update_self, NodeState.held.injEq] at hi
      subst t; exact he.2 j hj
    · exact hb i t (by simpa [next, ha] using hi) j hj
  | leave a u =>
    have lift : ∀ i t, Active (next s (.leave a u)) i t → Active s i t := by
      intro i t ha
      by_cases hi : i = a
      · subst i; simp only [Active, next, Function.update_self,
        reduceCtorEq, or_self] at ha
      · simpa [Active, next, hi] using ha
    refine ⟨fun i t ha => hc i t (lift i t ha), fun i t ha => hr i t (lift i t ha),
      ho, hs, hp, hd, fun r j hm t ha => hx r j hm t (lift j t ha), ?_⟩
    intro i t hi j hj
    by_cases ha : i = a
    · subst i; simp only [next, Function.update_self, reduceCtorEq] at hi
    · exact hb i t (by simpa [next, ha] using hi) j hj
  | idle => exact ⟨hc, hr, ho, hs, hp, hd, hx, hb⟩

theorem reachable_invariant {s : State n} (h : Reachable s) : Invariant s := by
  induction h with
  | refl => exact initial_invariant
  | tail _ h ih => rcases h with ⟨he, rfl⟩; exact step_preserves_invariant ih he

theorem mutual_exclusion_safety {s : State n} (h : Reachable s) {i j t u}
    (hne : i ≠ j) (hi : s.mode i = .held t) (hj : s.mode j = .held u) : False := by
  have hs := reachable_invariant h
  have hji := hs.permission_order _ j
    (hs.delivered_origin _ j (hs.held_barrier i t hi j (Ne.symm hne))) u (Or.inr hj)
  have hij := hs.permission_order _ i
    (hs.delivered_origin _ i (hs.held_barrier j u hj i hne)) t (Or.inr hi)
  exact priority_asymmetric hji hij

/-- This concerns a new send while the local request remains active; it does not
retroactively forbid an earlier reply sent before this local request was created. -/
theorem reply_deferral_invariant {s : State n} {i t r}
    (ha : Active s i t) (hp : Earlier ⟨t, i⟩ r) : ¬ Enabled s (.reply r i) := by
  intro h
  rcases h.2.2 with hz | ⟨u, hu, hlt⟩
  · simp [Active, hz] at ha
  · rcases ha with ha | ha
    · have ht := NodeState.wanted.inj (ha.symm.trans hu)
      subst u; exact priority_asymmetric hp hlt
    · simp [ha] at hu

/-- The mode of an existing request can change from Wanted only by entering Held. -/
theorem wanted_next {s : State n} {e i t} (he : Enabled s e)
    (hw : s.mode i = .wanted t) : Active (next s e) i t := by
  cases e with
  | request a =>
    by_cases hi : i = a
    · subst i; simp [Enabled, hw] at he
    · simp [Active, next, hi, hw]
  | enter a u =>
    by_cases hi : i = a
    · subst i
      have ht := NodeState.wanted.inj (hw.symm.trans he.1)
      subst u; simp [Active, next]
    · simp [Active, next, hi, hw]
  | leave a u =>
    by_cases hi : i = a
    · subst i; simp [Enabled, hw] at he
    · simp [Active, next, hi, hw]
  | receive => exact Or.inl hw
  | reply => exact Or.inl hw
  | deliver => exact Or.inl hw
  | idle => exact Or.inl hw

theorem histories_grow (s : State n) (e : Event n) :
    s.requests ⊆ (next s e).requests ∧ s.seen ⊆ (next s e).seen ∧
    s.replied ⊆ (next s e).replied ∧ s.delivered ⊆ (next s e).delivered := by
  cases e <;> simp [next, Finset.subset_insert]

/-- Once a responder has no earlier active request, receipt of r prevents it
from creating a new request earlier than r. This fact does not assume progress. -/
def LaterOnly (s : State n) (r : Request n) (j : NodeId n) : Prop :=
  ∀ t, Active s j t → Earlier r ⟨t, j⟩

theorem later_only_next {s : State n} {r j e} (hs : Invariant s)
    (hm : (r, j) ∈ s.seen) (hl : LaterOnly s r j) (he : Enabled s e) :
    LaterOnly (next s e) r j := by
  intro t ha
  cases e with
  | request a =>
    by_cases hj : j = a
    · subst j; simp only [Active, next, Function.update_self, NodeState.wanted.injEq,
        reduceCtorEq, or_false] at ha; subst t
      have ht := hs.seen_clock r a hm
      exact Or.inl (show r.ts < s.clock a + 1 by omega)
    · exact hl t (by simpa [Active, next, hj] using ha)
  | enter a u =>
    by_cases hj : j = a
    · subst j; simp only [Active, next, Function.update_self, reduceCtorEq,
        NodeState.held.injEq, false_or] at ha; subst t; exact hl u (Or.inl he.1)
    · exact hl t (by simpa [Active, next, hj] using ha)
  | leave a u =>
    by_cases hj : j = a
    · subst j; simp only [Active, next, Function.update_self, reduceCtorEq, or_self] at ha
    · exact hl t (by simpa [Active, next, hj] using ha)
  | receive => exact hl t ha
  | reply => exact hl t ha
  | deliver => exact hl t ha
  | idle => exact hl t ha

structure Run (n : ℕ) where
  state : ℕ → State n
  event : ℕ → Event n
  start : state 0 = initial
  valid : ∀ k, Step (state k) (event k) (state (k + 1))

theorem Run.reachable (ρ : Run n) (k : ℕ) : Reachable (ρ.state k) := by
  induction k with
  | zero => rw [ρ.start]; exact .refl _
  | succ k ih => exact .tail ih (ρ.valid k)

theorem Run.invariant (ρ : Run n) (k : ℕ) : Invariant (ρ.state k) :=
  reachable_invariant (ρ.reachable k)

theorem Run.grow (ρ : Run n) {k l : ℕ} (h : k ≤ l) :
    (ρ.state k).requests ⊆ (ρ.state l).requests ∧
    (ρ.state k).seen ⊆ (ρ.state l).seen ∧
    (ρ.state k).replied ⊆ (ρ.state l).replied ∧
    (ρ.state k).delivered ⊆ (ρ.state l).delivered := by
  induction l, h using Nat.le_induction with
  | base => exact ⟨fun _ h => h, fun _ h => h, fun _ h => h, fun _ h => h⟩
  | succ l _ ih =>
    have hg := histories_grow (ρ.state l) (ρ.event l)
    rw [← (ρ.valid l).2] at hg
    exact ⟨ih.1.trans hg.1, ih.2.1.trans hg.2.1,
      ih.2.2.1.trans hg.2.2.1, ih.2.2.2.trans hg.2.2.2⟩

theorem Run.later_only (ρ : Run n) {k l r j} (hkl : k ≤ l)
    (hm : (r, j) ∈ (ρ.state k).seen) (hl : LaterOnly (ρ.state k) r j) :
    LaterOnly (ρ.state l) r j := by
  induction l, hkl using Nat.le_induction with
  | base => exact hl
  | succ l hkl ih =>
    rw [(ρ.valid l).2]
    exact later_only_next (ρ.invariant l) ((ρ.grow hkl).2.1 hm) ih (ρ.valid l).1

/-- Reliability means eventual receipt of each addressed REQUEST and each sent REPLY.
Storage alone is insufficient. There is no delay bound or FIFO requirement.
Network loss and duplication are excluded. -/
def ReliableDelivery (ρ : Run n) : Prop :=
  (∀ k r j, r ∈ (ρ.state k).requests → j ≠ r.owner →
    ∃ l, k ≤ l ∧ (r, j) ∈ (ρ.state l).seen) ∧
  (∀ k r j, (r, j) ∈ (ρ.state k).replied →
    ∃ l, k ≤ l ∧ (r, j) ∈ (ρ.state l).delivered)

def LocalService : Event n → Prop
  | .reply _ _ | .enter _ _ => True
  | _ => False

/-- Weak action fairness for continuously enabled reply sends and CS entry.
Client request generation is optional; finite CS residence is a separate contract. -/
def WeakFairness (ρ : Run n) : Prop :=
  ∀ e, LocalService e → ∀ k, (∀ l, k ≤ l → Enabled (ρ.state l) e) →
    ∃ l, k ≤ l ∧ ρ.event l = e

def FiniteCS (ρ : Run n) : Prop :=
  ∀ k i t, (ρ.state k).mode i = .held t →
    ∃ l, k ≤ l ∧ (ρ.state l).mode i = .released

private theorem service_eventually (ρ : Run n) (hf : WeakFairness ρ)
    (e : Event n) (he : LocalService e) (k : ℕ) (P : ℕ → Prop)
    (ready : ∀ l, k ≤ l → ¬ P l → Enabled (ρ.state l) e)
    (effect : ∀ l, ρ.event l = e → P (l + 1)) : ∃ l, k ≤ l ∧ P l := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨l, hkl, hel⟩ := hf e he k (fun l hl => ready l hl (hn l hl))
  exact hn (l + 1) (by omega) (effect l hel)

private theorem later_reply_condition {s : State n} (hs : Invariant s)
    {r : Request n} {j : NodeId n} (hne : j ≠ r.owner)
    (hw : s.mode r.owner = .wanted r.ts) (hl : LaterOnly s r j) : ReplyCondition s r j := by
  cases hm : s.mode j with
  | released => exact Or.inl hm
  | wanted t => exact Or.inr ⟨t, hm, hl t (Or.inl hm)⟩
  | held t =>
    have hrep := hs.delivered_origin _ r.owner
      (hs.held_barrier j t hm r.owner (Ne.symm hne))
    have hp := hs.permission_order _ r.owner hrep r.ts (Or.inl hw)
    exact False.elim (priority_asymmetric (hl t (Or.inr hm)) hp)

/-- Every individual request eventually enters, even with later client requests.
The proof descends on n*timestamp+nodeId, not on an assumed completion predicate. -/
theorem request_eventually_enters (ρ : Run n) (hd : ReliableDelivery ρ)
    (hf : WeakFairness ρ) (hc : FiniteCS ρ) (r : Request n) (k : ℕ)
    (hw : (ρ.state k).mode r.owner = .wanted r.ts) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode r.owner = .held r.ts := by
  classical
  have main : ∀ d (r : Request n), r.rank = d → ∀ k,
      (ρ.state k).mode r.owner = .wanted r.ts →
      ∃ l, k ≤ l ∧ (ρ.state l).mode r.owner = .held r.ts := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro r hrank k hw
      by_contra hn
      push Not at hn
      have waiting : ∀ l, k ≤ l → (ρ.state l).mode r.owner = .wanted r.ts := by
        intro l hkl
        induction l, hkl using Nat.le_induction with
        | base => exact hw
        | succ l hkl ihl =>
          have ha := wanted_next (ρ.valid l).1 ihl
          rw [← (ρ.valid l).2] at ha
          exact ha.resolve_right (hn (l + 1) (by omega))
      have each : ∀ j, j ≠ r.owner → ∃ l, k ≤ l ∧ (r, j) ∈ (ρ.state l).delivered := by
        intro j hne
        obtain ⟨a, hka, hseen⟩ := hd.1 k r j
          ((ρ.invariant k).active_request _ _ (Or.inl hw)) hne
        have eventually_later : ∃ b, a ≤ b ∧ LaterOnly (ρ.state b) r j := by
          cases hm : (ρ.state a).mode j with
          | released => exact ⟨a, le_refl _, by simp [LaterOnly, Active, hm]⟩
          | held t =>
            obtain ⟨b, hab, hb⟩ := hc a j t hm
            exact ⟨b, hab, by simp [LaterOnly, Active, hb]⟩
          | wanted t =>
            rcases priority_trichotomy (show r.owner ≠ (⟨t, j⟩ : Request n).owner
              from Ne.symm hne) with hlt | hlt
            · exact ⟨a, le_refl _, by simpa [LaterOnly, Active, hm] using hlt⟩
            · have hsmall := priority_rank hlt
              rw [hrank] at hsmall
              obtain ⟨b, hab, hb⟩ := ih _ hsmall ⟨t, j⟩ rfl a hm
              obtain ⟨c, hbc, hreleased⟩ := hc b j t hb
              exact ⟨c, hab.trans hbc, by simp [LaterOnly, Active, hreleased]⟩
        obtain ⟨b, hab, hlater⟩ := eventually_later
        obtain ⟨c, hbc, hsent⟩ := service_eventually ρ hf (.reply r j) trivial b
          (fun l => (r, j) ∈ (ρ.state l).replied)
          (by
            intro l hbl hnot
            have hal := hab.trans hbl
            exact ⟨(ρ.grow hal).2.1 hseen, hnot,
              later_reply_condition (ρ.invariant l) hne
                (waiting l (hka.trans hal))
                (ρ.later_only hbl ((ρ.grow hab).2.1 hseen) hlater)⟩)
          (by
            intro l he
            rw [(ρ.valid l).2, he]
            exact Finset.mem_insert_self _ _)
        obtain ⟨l, hcl, hl⟩ := hd.2 c r j hsent
        exact ⟨l, hka.trans (hab.trans (hbc.trans hcl)), hl⟩
      have all_times : ∀ j, ∃ l, k ≤ l ∧ (j ≠ r.owner → (r, j) ∈ (ρ.state l).delivered) := by
        intro j
        by_cases hj : j = r.owner
        · exact ⟨k, le_refl _, fun h => False.elim (h hj)⟩
        · obtain ⟨l, hkl, hl⟩ := each j hj
          exact ⟨l, hkl, fun _ => hl⟩
      choose times ht using all_times
      let b := max k (Finset.univ.sup times)
      have hkb : k ≤ b := le_max_left _ _
      have barriers : ∀ l, b ≤ l → ∀ j, j ≠ r.owner → (r, j) ∈ (ρ.state l).delivered := by
        intro l hbl j hj
        have hjb : times j ≤ b := (Finset.le_sup (Finset.mem_univ j)).trans (le_max_right _ _)
        exact (ρ.grow (hjb.trans hbl)).2.2.2 ((ht j).2 hj)
      obtain ⟨l, hbl, hl⟩ := service_eventually ρ hf (.enter r.owner r.ts) trivial b
        (fun l => (ρ.state l).mode r.owner = .held r.ts)
        (fun l hbl _ => ⟨waiting l (hkb.trans hbl), by simpa using barriers l hbl⟩)
        (by intro l he; rw [(ρ.valid l).2, he]; simp [next])
      exact hn l (hkb.trans hbl) hl
  exact main r.rank r rfl k hw

def MinimalWanted (s : State n) (r : Request n) : Prop :=
  s.mode r.owner = .wanted r.ts ∧
    ∀ j t, s.mode j = .wanted t → ¬ Earlier ⟨t, j⟩ r

theorem deadlock_freedom_minimal_request (ρ : Run n) (hd : ReliableDelivery ρ)
    (hf : WeakFairness ρ) (hc : FiniteCS ρ) {r k}
    (hm : MinimalWanted (ρ.state k) r) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode r.owner = .held r.ts :=
  request_eventually_enters ρ hd hf hc r k hm.1

theorem clock_monotone_step (s : State n) (e : Event n) (i : NodeId n) :
    s.clock i ≤ (next s e).clock i := by
  cases e <;> simp [next, Function.update_apply]
  all_goals split_ifs <;> simp_all <;> omega

theorem historical_request_clock {s : State n} (h : Reachable s) :
    ∀ r ∈ s.requests, r.ts ≤ s.clock r.owner := by
  induction h with
  | refl => simp [initial]
  | @tail u v e _ h ih =>
    rcases h with ⟨_, rfl⟩
    intro r hr
    cases e with
    | request i =>
      rcases Finset.mem_insert.mp hr with rfl | hr
      · simp [next]
      · exact (ih r hr).trans (clock_monotone_step u (.request i) r.owner)
    | receive q j => exact (ih r hr).trans (clock_monotone_step u (.receive q j) r.owner)
    | reply => exact ih r hr
    | deliver => exact ih r hr
    | enter => exact ih r hr
    | leave => exact ih r hr
    | idle => exact ih r hr

theorem fresh_request_unique {s : State n} (h : Reachable s) (i : NodeId n) :
    (⟨s.clock i + 1, i⟩ : Request n) ∉ s.requests := by
  intro hm
  have hb := historical_request_clock h _ hm
  change s.clock i + 1 ≤ s.clock i at hb
  omega

theorem no_stale_reply_for_fresh_request {s : State n} (h : Reachable s) (i j : NodeId n) :
    (⟨s.clock i + 1, i⟩, j) ∉ s.delivered := by
  intro hm
  have hs := reachable_invariant h
  exact fresh_request_unique h i
    (hs.seen_origin _ _ (hs.reply_origin _ _ (hs.delivered_origin _ _ hm))).1

theorem reply_deferral_until_release {s : State n} (h : Reachable s) {i t r}
    (ha : Active s i t) (hp : Earlier ⟨t, i⟩ r) : (r, i) ∉ s.replied := by
  intro hm
  exact priority_asymmetric hp ((reachable_invariant h).permission_order r i hm t ha)

def runTrace (s : State n) : List (Event n) → State n
  | [] => s
  | e :: es => runTrace (next s e) es

def ValidTrace (s : State n) : List (Event n) → Prop
  | [] => True
  | e :: es => Enabled s e ∧ ValidTrace (next s e) es

instance (s : State n) (es : List (Event n)) : Decidable (ValidTrace s es) := by
  induction es generalizing s with
  | nil => exact isTrue trivial
  | cons e es ih => exact instDecidableAnd

theorem valid_trace_execution {s : State n} {es} (h : ValidTrace s es) :
    ∀ u, Execution u s → Execution u (runTrace s es) := by
  induction es generalizing s with
  | nil => intro u hu; exact hu
  | cons e es ih =>
    intro u hu
    exact ih h.2 u (.tail hu ⟨h.1, rfl⟩)

theorem valid_trace_reachable {es : List (Event n)} (h : ValidTrace initial es) :
    Reachable (runTrace initial es) := valid_trace_execution h initial (.refl _)

/-- A real request followed forever by idle steps. Storage is not delivery. -/
def withheldRun : Run 2 where
  state k := if k = 0 then initial else next initial (.request 0)
  event k := if k = 0 then .request 0 else .idle
  start := rfl
  valid k := by
    cases k <;> simp [Step, Enabled, next, initial]

theorem delivery_contract_necessary :
    (withheldRun.state 1).mode 0 = .wanted 1 ∧
    (∀ k t, (withheldRun.state k).mode 0 ≠ .held t) ∧ ¬ ReliableDelivery withheldRun := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k t; cases k <;> simp [withheldRun, next, initial]
  · intro hd
    obtain ⟨l, _, hl⟩ := hd.1 1 ⟨1, 0⟩ 1 (by simp [withheldRun, next, initial]) (by decide)
    cases l <;> simp [withheldRun, next, initial] at hl

/-- An existential deadlock-freedom consequence of individual request progress. -/
theorem deadlock_freedom (ρ : Run n) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ)
    (hc : FiniteCS ρ) {k} (hw : ∃ i t, (ρ.state k).mode i = .wanted t) :
    ∃ l, k ≤ l ∧ ∃ i t, (ρ.state l).mode i = .held t := by
  obtain ⟨i, t, ht⟩ := hw
  obtain ⟨l, hkl, hl⟩ := request_eventually_enters ρ hd hf hc ⟨t, i⟩ k ht
  exact ⟨l, hkl, i, t, hl⟩

structure DistributedRicartAgrawalaSuite : Prop where
  priority : ∀ n (a b c : Request n), Earlier a b → Earlier b c → Earlier a c
  safety : ∀ n (s : State n), Reachable s → ∀ i j t u, i ≠ j →
    s.mode i = .held t → s.mode j = .held u → False
  deferral : ∀ n (s : State n), Reachable s → ∀ i t r, Active s i t →
    Earlier ⟨t, i⟩ r → (r, i) ∉ s.replied
  freshness : ∀ n (s : State n), Reachable s → ∀ i j,
    (⟨s.clock i + 1, i⟩, j) ∉ s.delivered
  progress : ∀ n (ρ : Run n), ReliableDelivery ρ → WeakFairness ρ → FiniteCS ρ →
    ∀ (r : Request n) (k : ℕ), (ρ.state k).mode r.owner = .wanted r.ts →
      ∃ l, k ≤ l ∧ (ρ.state l).mode r.owner = .held r.ts

theorem distributed_ricart_agrawala_master_suite : DistributedRicartAgrawalaSuite where
  priority := fun _ _ _ _ => priority_transitive
  safety := fun _ _ h _ _ _ _ => mutual_exclusion_safety h
  deferral := fun _ _ h _ _ _ => reply_deferral_until_release h
  freshness := fun _ _ h => no_stale_reply_for_fresh_request h
  progress := fun _ => request_eventually_enters

theorem request_clock_is_lamport_tick (s : State n) (i : NodeId n) :
    (next s (.request i)).clock i = DistributedLamportClocks.localTick (s.clock i) := by
  simp [next, DistributedLamportClocks.localTick]

theorem receive_clock_is_lamport_update (s : State n) (r : Request n) (j : NodeId n) :
    (next s (.receive r j)).clock j =
      DistributedLamportClocks.receiveMsg (s.clock j) r.ts := by
  simp [next, DistributedLamportClocks.receiveMsg]

/-- Distinct responding peers for the current invocation, derived from tagged receipts. -/
def repliesReceived (s : State n) (i : NodeId n) : Finset (NodeId n) :=
  match s.mode i with
  | .released => ∅
  | .wanted t | .held t => Finset.univ.filter (fun j => (⟨t, i⟩, j) ∈ s.delivered)

theorem entry_barrier_iff (s : State n) (i : NodeId n) (t : ℕ) :
    Enabled s (.enter i t) ↔ s.mode i = .wanted t ∧
      ∀ j, j ≠ i → j ∈ repliesReceived s i := by
  constructor
  · rintro ⟨hw, hb⟩
    exact ⟨hw, fun j hj => by simpa [repliesReceived, hw] using hb j hj⟩
  · rintro ⟨hw, hb⟩
    exact ⟨hw, fun j hj => by simpa [repliesReceived, hw] using hb j hj⟩

end DistributedRicartAgrawalaMutex
