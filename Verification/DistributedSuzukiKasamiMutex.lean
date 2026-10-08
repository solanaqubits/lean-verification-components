/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.List.FinRange

/-! Fixed-membership, crash-free Suzuki–Kasami with unbounded counters.
The global payload is a semantic coordinate, accessible only to its holder.
Ownership and transit are separate locations; conservation is proved, not a Step guard.
Request fanout is one local enqueue. Receipt, token send/delivery and CS actions
are separate. An idle holder reserves its queued handoff before new local entry. -/
namespace DistributedSuzukiKasamiMutex

abbrev NodeId (n : ℕ) := Fin n
inductive Mode where
  | idle | requesting | inCS
  deriving DecidableEq, Repr

structure Token (n : ℕ) where
  ln : NodeId n → ℕ
  queue : List (NodeId n)

structure Request (n : ℕ) where
  sender : NodeId n
  sn : ℕ
  dest : NodeId n
  deriving DecidableEq, Repr

structure State (n : ℕ) where
  mode : NodeId n → Mode
  rn : NodeId n → NodeId n → ℕ
  owners : Finset (NodeId n)
  flight : Option (NodeId n)
  token : Token n
  sent : Finset (Request n)
  received : Finset (Request n)

def localToken (s : State n) (i : NodeId n) : Option (Token n) :=
  if i ∈ s.owners then some s.token else none

def tokenCount (s : State n) : ℕ := s.owners.card + s.flight.toList.length

def initial (owner : NodeId n) : State n :=
  ⟨fun _ => .idle, fun _ _ => 0, {owner}, none, ⟨fun _ => 0, []⟩, ∅, ∅⟩

def appendPending (q : List (NodeId n)) (rn ln : NodeId n → ℕ) : List (NodeId n) :=
  q ++ (List.finRange n).filter (fun j => decide (j ∉ q ∧ rn j = ln j + 1))

inductive Event (n : ℕ) where
  | request (i : NodeId n)
  | receive (r : Request n)
  | send (i j : NodeId n)
  | deliver (j : NodeId n)
  | enter (i : NodeId n)
  | leave (i : NodeId n)
  | idle
  deriving DecidableEq, Repr

def Enabled (s : State n) : Event n → Prop
  | .request i => s.mode i = .idle ∧ (i ∈ s.owners → s.token.queue = [])
  | .receive r => r ∈ s.sent ∧ r ∉ s.received
  | .send i j => i ∈ s.owners ∧ s.mode i = .idle ∧ s.token.queue.head? = some j
  | .deliver j => s.flight = some j
  | .enter i => s.mode i = .requesting ∧ i ∈ s.owners
  | .leave i => s.mode i = .inCS
  | .idle => True

instance (s : State n) (e : Event n) : Decidable (Enabled s e) := by
  cases e <;> simp only [Enabled] <;> infer_instance

def next (s : State n) : Event n → State n
  | .request i =>
    if i ∈ s.owners then { s with mode := Function.update s.mode i .requesting }
    else { s with mode := Function.update s.mode i .requesting
                  rn := Function.update s.rn i (Function.update (s.rn i) i (s.rn i i + 1))
                  sent := s.sent ∪ (Finset.univ.erase i).image
                    (fun j => ⟨i, s.rn i i + 1, j⟩) }
  | .receive r =>
    let row := Function.update (s.rn r.dest) r.sender (max (s.rn r.dest r.sender) r.sn)
    { s with rn := Function.update s.rn r.dest row
             received := insert r s.received
             token := if r.dest ∈ s.owners ∧ s.mode r.dest = .idle then
               ⟨s.token.ln, appendPending s.token.queue row s.token.ln⟩ else s.token }
  | .send i j =>
    { s with owners := s.owners.erase i
             flight := some j
             token := ⟨s.token.ln, s.token.queue.tail⟩ }
  | .deliver j => { s with owners := insert j s.owners, flight := none }
  | .enter i => { s with mode := Function.update s.mode i .inCS }
  | .leave i =>
    let ln := Function.update s.token.ln i (s.rn i i)
    { s with mode := Function.update s.mode i .idle
             token := ⟨ln, appendPending s.token.queue (s.rn i) ln⟩ }
  | .idle => s

def Step (s : State n) (e : Event n) (t : State n) : Prop := Enabled s e ∧ t = next s e
inductive Execution : State n → State n → Prop where
  | refl (s) : Execution s s
  | tail {s t u e} : Execution s t → Step t e u → Execution s u

def Reachable (owner : NodeId n) (s : State n) : Prop := Execution (initial owner) s

structure Safety (s : State n) : Prop where
  conserved : tokenCount s = 1
  cs_owner : ∀ i, s.mode i = .inCS → i ∈ s.owners

theorem owner_singleton {s : State n} (h : tokenCount s = 1) {i} (hi : i ∈ s.owners) :
    s.owners = {i} ∧ s.flight = none := by
  have hp := Finset.card_pos.mpr ⟨i, hi⟩
  cases hf : s.flight with
  | none =>
    have hc : s.owners.card = 1 := by simpa [tokenCount, hf] using h
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
    have hij : i = j := by simpa [hj] using hi
    exact ⟨by simpa [hij] using hj, rfl⟩
  | some j =>
    have hc : s.owners.card = 0 := by simpa [tokenCount, hf] using h
    omega

theorem flight_empty_owners {s : State n} (h : tokenCount s = 1) {j}
    (hf : s.flight = some j) : s.owners = ∅ := by
  have hc : s.owners.card = 0 := by simpa [tokenCount, hf] using h
  exact Finset.card_eq_zero.mp hc

theorem safety_initial (i : NodeId n) : Safety (initial i) := by
  constructor
  · simp [tokenCount, initial]
  · simp [initial]

theorem safety_step {s : State n} (h : Safety s) {e} (he : Enabled s e) :
    Safety (next s e) := by
  cases e with
  | request a =>
    simp only [next]
    split <;> constructor
    all_goals first
      | exact h.conserved
      | intro i hi; by_cases ha : i = a
        · subst i; simp at hi
        · exact h.cs_owner i (by simpa [ha] using hi)
  | receive r => exact ⟨h.conserved, h.cs_owner⟩
  | send i j =>
    obtain ⟨hi, hm, _⟩ := he
    obtain ⟨ho, _⟩ := owner_singleton h.conserved hi
    constructor
    · simp [tokenCount, next, ho]
    · intro k hk
      have hki : k = i := by simpa [ho] using h.cs_owner k hk
      subst k
      change s.mode i = .inCS at hk
      rw [hm] at hk
      cases hk
  | deliver j =>
    have ho := flight_empty_owners h.conserved he
    constructor
    · simp [tokenCount, next, ho]
    · intro i hi; exact Finset.mem_insert_of_mem (h.cs_owner i hi)
  | enter a =>
    constructor
    · exact h.conserved
    · intro i hi
      by_cases ha : i = a
      · subst i; exact he.2
      · exact h.cs_owner i (by simpa [next, ha] using hi)
  | leave a =>
    constructor
    · exact h.conserved
    · intro i hi
      by_cases ha : i = a
      · subst i; simp [next] at hi
      · exact h.cs_owner i (by simpa [next, ha] using hi)
  | idle => exact h

theorem reachable_safety {owner : NodeId n} {s : State n} (h : Reachable owner s) : Safety s := by
  induction h with
  | refl => exact safety_initial _
  | tail _ hs ih => rcases hs with ⟨he, rfl⟩; exact safety_step ih he

theorem token_uniqueness_invariant {owner : NodeId n} {s : State n}
    (h : Reachable owner s) : tokenCount s = 1 := (reachable_safety h).conserved

theorem mutual_exclusion_safety {owner : NodeId n} {s : State n}
    (h : Reachable owner s) {i j} (hne : i ≠ j)
    (hi : s.mode i = .inCS) (hj : s.mode j = .inCS) : False := by
  have hs := reachable_safety h
  have ho := (owner_singleton hs.conserved (hs.cs_owner i hi)).1
  exact hne (Finset.mem_singleton.mp (ho ▸ hs.cs_owner j hj)).symm


theorem appendPending_mem (q : List (NodeId n)) (rn ln : NodeId n → ℕ) (j : NodeId n) :
    j ∈ appendPending q rn ln ↔ j ∈ q ∨ rn j = ln j + 1 := by
  simp only [appendPending, List.mem_append, List.mem_filter, List.mem_finRange,
    decide_eq_true_eq, true_and]
  tauto

theorem appendPending_nodup {q : List (NodeId n)} (h : q.Nodup) (rn ln : NodeId n → ℕ) :
    (appendPending q rn ln).Nodup := by
  apply List.Nodup.append h ((List.nodup_finRange n).filter _)
  intro j hj hk
  have hx := (List.mem_filter.mp hk).2
  simp only [decide_eq_true_eq] at hx
  exact hx.1 hj

theorem queue_nodup_step {s : State n} (h : s.token.queue.Nodup) (e : Event n) :
    (next s e).token.queue.Nodup := by
  cases e with
  | request i => simp only [next]; split <;> exact h
  | receive r =>
    simp only [next]
    split
    · exact appendPending_nodup h _ _
    · exact h
  | send i j => exact h.tail
  | deliver => exact h
  | enter => exact h
  | leave i => exact appendPending_nodup h _ _
  | idle => exact h

theorem queue_nodup_preservation {owner : NodeId n} {s : State n}
    (h : Reachable owner s) : s.token.queue.Nodup := by
  induction h with
  | refl => exact List.nodup_nil
  | tail _ hs ih => rcases hs with ⟨_, rfl⟩; exact queue_nodup_step ih _

theorem rn_monotone_step (s : State n) (e : Event n) (i j : NodeId n) :
    s.rn i j ≤ (next s e).rn i j := by
  cases e with
  | request a =>
    by_cases ho : a ∈ s.owners
    · simp [next, ho]
    · by_cases hi : i = a <;> by_cases hj : j = a <;> simp [next, ho, hi, hj]
  | receive r =>
    by_cases hi : i = r.dest <;> by_cases hj : j = r.sender <;>
      simp [next, hi, hj]
  | send => exact le_refl _
  | deliver => exact le_refl _
  | enter => exact le_refl _
  | leave => exact le_refl _
  | idle => exact le_refl _


structure Counters (s : State n) : Prop where
  rn_bound : ∀ i j, s.rn i j ≤ s.rn j j
  ln_bound : ∀ j, s.token.ln j ≤ s.rn j j
  gap_bound : ∀ j, s.rn j j ≤ s.token.ln j + 1
  idle_eq : ∀ j, s.mode j = .idle → s.rn j j = s.token.ln j
  sent_bound : ∀ r ∈ s.sent, r.sender ≠ r.dest ∧ r.sn ≤ s.rn r.sender r.sender

theorem counters_initial (i : NodeId n) : Counters (initial i) := by
  constructor <;> simp [initial]

theorem self_receive {s : State n} {r : Request n} (hne : r.sender ≠ r.dest) (i : NodeId n) :
    (next s (.receive r)).rn i i = s.rn i i := by
  by_cases hi : i = r.dest
  · subst i
    simp [next, Ne.symm hne]
  · simp [next, hi]

theorem ln_receive (s : State n) (r : Request n) :
    (next s (.receive r)).token.ln = s.token.ln := by
  simp only [next]
  split <;> rfl

theorem counters_step {s : State n} (h : Counters s) {e} (he : Enabled s e) :
    Counters (next s e) := by
  cases e with
  | request a =>
    by_cases ho : a ∈ s.owners
    · simp only [next, if_pos ho]
      refine ⟨h.rn_bound, h.ln_bound, h.gap_bound, ?_, h.sent_bound⟩
      intro j hj
      by_cases ha : j = a
      · subst j; simp at hj
      · exact h.idle_eq j (by simpa [ha] using hj)
    · have hi := h.idle_eq a he.1
      simp only [next, if_neg ho]
      constructor
      · intro i j
        by_cases ha : i = a <;> by_cases hb : j = a
        · subst i; subst j; exact le_refl _
        · subst i; simpa [hb] using h.rn_bound a j
        · subst j; simpa [ha] using (h.rn_bound i a).trans (Nat.le_succ _)
        · simpa [ha, hb] using h.rn_bound i j
      · intro j; by_cases ha : j = a
        · subst j; simpa using (h.ln_bound a).trans (Nat.le_succ _)
        · simpa [ha] using h.ln_bound j
      · intro j; by_cases ha : j = a
        · subst j; simpa using Nat.succ_le_succ hi.le
        · simpa [ha] using h.gap_bound j
      · intro j hj; by_cases ha : j = a
        · subst j; simp at hj
        · simpa [ha] using h.idle_eq j (by simpa [ha] using hj)
      · intro r hr
        rcases Finset.mem_union.mp hr with hr | hr
        · have hb := h.sent_bound r hr
          exact ⟨hb.1, by
            simpa [next, ho] using hb.2.trans (rn_monotone_step s (.request a) r.sender r.sender)⟩
        · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
          exact ⟨Ne.symm (Finset.mem_erase.mp hj).1, by simp⟩
  | receive r =>
    have hr := h.sent_bound r he.1
    constructor
    · intro i j
      rw [self_receive hr.1]
      by_cases hi : i = r.dest <;> by_cases hj : j = r.sender
      · subst i; subst j; simpa [next] using max_le (h.rn_bound r.dest r.sender) hr.2
      · subst i; simpa [next, hj] using h.rn_bound r.dest j
      · simpa [next, hi] using h.rn_bound i j
      · simpa [next, hi] using h.rn_bound i j
    · intro j; rw [ln_receive, self_receive hr.1]; exact h.ln_bound j
    · intro j; rw [ln_receive, self_receive hr.1]; exact h.gap_bound j
    · intro j hj; rw [ln_receive, self_receive hr.1]; exact h.idle_eq j hj
    · intro q hq; rw [self_receive hr.1]; exact h.sent_bound q hq
  | send => exact ⟨h.rn_bound, h.ln_bound, h.gap_bound, h.idle_eq, h.sent_bound⟩
  | deliver => exact ⟨h.rn_bound, h.ln_bound, h.gap_bound, h.idle_eq, h.sent_bound⟩
  | enter a =>
    refine ⟨h.rn_bound, h.ln_bound, h.gap_bound, ?_, h.sent_bound⟩
    intro j hj
    by_cases ha : j = a
    · subst j; simp [next] at hj
    · exact h.idle_eq j (by simpa [next, ha] using hj)
  | leave a =>
    refine ⟨h.rn_bound, ?_, ?_, ?_, h.sent_bound⟩
    · intro j; by_cases ha : j = a
      · subst j; simp [next]
      · simpa [next, ha] using h.ln_bound j
    · intro j; by_cases ha : j = a
      · subst j; simp [next]
      · simpa [next, ha] using h.gap_bound j
    · intro j hj; by_cases ha : j = a
      · subst j; simp [next]
      · simpa [next, ha] using h.idle_eq j (by simpa [next, ha] using hj)
  | idle => exact h

theorem reachable_counters {owner : NodeId n} {s : State n}
    (h : Reachable owner s) : Counters s := by
  induction h with
  | refl => exact counters_initial _
  | tail _ hs ih => rcases hs with ⟨he, rfl⟩; exact counters_step ih he

theorem ln_monotone_step {s : State n} (h : Counters s) (e : Event n) (j : NodeId n) :
    s.token.ln j ≤ (next s e).token.ln j := by
  cases e with
  | request i => simp only [next]; split <;> exact le_refl _
  | receive r => rw [ln_receive]
  | send => exact le_refl _
  | deliver => exact le_refl _
  | enter => exact le_refl _
  | leave i =>
    by_cases hi : j = i
    · subst j; simpa [next] using h.ln_bound i
    · simp [next, hi]
  | idle => exact le_refl _


def Pending (s : State n) (j : NodeId n) : Prop :=
  s.mode j = .requesting ∧ j ∉ s.owners

structure Routing (s : State n) : Prop where
  foreign : ∀ j, Pending s j → s.rn j j = s.token.ln j + 1 ∧
    ∀ i, i ≠ j → (⟨j, s.rn j j, i⟩ : Request n) ∈ s.sent
  queued : ∀ j ∈ s.token.queue, Pending s j ∧ s.flight ≠ some j
  transit : ∀ j, s.flight = some j → s.mode j = .requesting

theorem routing_initial (i : NodeId n) : Routing (initial i) := by
  constructor <;> simp [initial, Pending]

theorem outstanding_pending {s : State n} (hs : Safety s) (hc : Counters s)
    {i j : NodeId n} (hi : i ∈ s.owners) (hm : s.mode i = .idle)
    (hr : s.rn i j = s.token.ln j + 1) : Pending s j := by
  have hb := hc.rn_bound i j
  have noidle : s.mode j ≠ .idle := by
    intro hj
    have he := hc.idle_eq j hj
    omega
  have hji : j ≠ i := by
    intro he; subst j
    have he := hc.idle_eq i hm
    omega
  have hno : j ∉ s.owners := by
    rw [(owner_singleton hs.conserved hi).1]
    simpa using hji
  refine ⟨?_, hno⟩
  cases hj : s.mode j with
  | idle => exact False.elim (noidle hj)
  | requesting => rfl
  | inCS => exact False.elim (hno (hs.cs_owner j hj))

theorem sent_monotone (s : State n) (e : Event n) : s.sent ⊆ (next s e).sent := by
  cases e with
  | request i => simp only [next]; split <;> simp
  | receive => exact Finset.Subset.refl _
  | send => exact Finset.Subset.refl _
  | deliver => exact Finset.Subset.refl _
  | enter => exact Finset.Subset.refl _
  | leave => exact Finset.Subset.refl _
  | idle => exact Finset.Subset.refl _

theorem self_unchanged_request {s : State n} {i j : NodeId n} (h : j ≠ i) :
    (next s (.request i)).rn j j = s.rn j j := by
  simp only [next]
  split <;> simp [h]

theorem routing_foreign_step {s : State n} (hs : Safety s) (hc : Counters s)
    (hr : Routing s) {e} (he : Enabled s e) :
    ∀ j, Pending (next s e) j → (next s e).rn j j = (next s e).token.ln j + 1 ∧
      ∀ i, i ≠ j → (⟨j, (next s e).rn j j, i⟩ : Request n) ∈ (next s e).sent := by
  intro j hj
  cases e with
  | request a =>
    by_cases ha : j = a
    · subst j
      by_cases ho : a ∈ s.owners
      · exact False.elim (hj.2 (by simp [next, ho]))
      · have hidle := hc.idle_eq a he.1
        simp only [next, if_neg ho, Function.update_self]
        refine ⟨congrArg Nat.succ hidle, ?_⟩
        intro i hi
        apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨i, by simpa using hi, rfl⟩
    · have old : Pending s j := by
        unfold Pending at *
        by_cases ho : a ∈ s.owners <;> simpa [next, ho, ha] using hj
      have hf := hr.foreign j old
      refine ⟨?_, ?_⟩
      · by_cases ho : a ∈ s.owners <;> simpa [next, ho, ha] using hf.1
      · intro i hi
        rw [self_unchanged_request ha]
        exact sent_monotone s (.request a) (hf.2 i hi)
  | receive r =>
    have hne := (hc.sent_bound r he.1).1
    rw [self_receive hne, ln_receive]
    exact hr.foreign j hj
  | send a b =>
    have hold : Pending s j := by
      refine ⟨hj.1, ?_⟩
      intro ho
      have hja : j = a := by
        simpa [(owner_singleton hs.conserved he.1).1] using ho
      subst j
      have hm := he.2.1
      have hx := hj.1
      change s.mode a = .requesting at hx
      rw [hm] at hx; cases hx
    exact hr.foreign j hold
  | deliver a =>
    have hold : Pending s j := ⟨hj.1, fun h => hj.2 (Finset.mem_insert_of_mem h)⟩
    exact hr.foreign j hold
  | enter a =>
    by_cases ha : j = a
    · subst j; have hm := hj.1; simp [next] at hm
    · exact hr.foreign j ⟨by simpa [next, ha] using hj.1, hj.2⟩
  | leave a =>
    by_cases ha : j = a
    · subst j; have hm := hj.1; simp [next] at hm
    · simpa [next, ha] using hr.foreign j ⟨by simpa [next, ha] using hj.1, hj.2⟩
  | idle => exact hr.foreign j hj


theorem routing_step {s : State n} (hs : Safety s) (hc : Counters s)
    (hr : Routing s) (hq : s.token.queue.Nodup) {e} (he : Enabled s e) : Routing (next s e) := by
  refine ⟨routing_foreign_step hs hc hr he, ?_, ?_⟩
  · intro j hj
    cases e with
    | request a =>
      have old : j ∈ s.token.queue := by
        by_cases ho : a ∈ s.owners <;> simpa [next, ho] using hj
      obtain ⟨⟨hm, hn⟩, hf⟩ := hr.queued j old
      have ha : j ≠ a := by intro ha; subst j; rw [he.1] at hm; cases hm
      by_cases ho : a ∈ s.owners <;>
        simpa [Pending, next, ho, ha] using And.intro (And.intro hm hn) hf
    | receive r =>
      by_cases ho : r.dest ∈ s.owners ∧ s.mode r.dest = .idle
      · have hj' : j ∈ appendPending s.token.queue
            (Function.update (s.rn r.dest) r.sender
              (max (s.rn r.dest r.sender) r.sn)) s.token.ln := by
          simpa [next, ho] using hj
        rcases (appendPending_mem _ _ _ _).mp hj' with hold | hnew
        · simpa [Pending, next] using hr.queued j hold
        · have hs' := safety_step hs he
          have hc' := counters_step hc he
          have hp := outstanding_pending hs' hc' (i := r.dest) (j := j) ho.1 ho.2
          have hp' : Pending (next s (.receive r)) j := hp (by simpa [next, ho] using hnew)
          exact ⟨hp', by simp [next, (owner_singleton hs.conserved ho.1).2]⟩
      · simpa [Pending, next, ho] using hr.queued j (by simpa [next, ho] using hj)
    | send a b =>
      have ht : j ∈ s.token.queue.tail := hj
      have hold := hr.queued j (List.mem_of_mem_tail ht)
      have hne : j ≠ b := by
        cases hlist : s.token.queue with
        | nil => simp [hlist] at ht
        | cons x xs =>
          have hb : x = b := by simpa [hlist] using he.2.2
          subst x
          have hnot := (List.nodup_cons.mp (hlist ▸ hq)).1
          intro h; subst j; exact hnot (by simpa [hlist] using ht)
      exact ⟨⟨hold.1.1, fun h => hold.1.2 (Finset.mem_of_mem_erase h)⟩,
        by simpa [next] using hne.symm⟩
    | deliver a =>
      have hold := hr.queued j hj
      have hne : j ≠ a := by intro h; subst j; exact hold.2 he
      exact ⟨⟨hold.1.1, by simpa [next, hne] using hold.1.2⟩, by simp [next]⟩
    | enter a =>
      have hold := hr.queued j hj
      have ha : j ≠ a := by intro h; subst j; exact hold.1.2 he.2
      exact ⟨⟨by simpa [next, ha] using hold.1.1, hold.1.2⟩, hold.2⟩
    | leave a =>
      have haown := hs.cs_owner a he
      have hs' := safety_step hs he
      have hc' := counters_step hc he
      change j ∈ appendPending s.token.queue (s.rn a)
        (Function.update s.token.ln a (s.rn a a)) at hj
      rcases (appendPending_mem _ _ _ _).mp hj with hold | hnew
      · obtain ⟨⟨hm, hn⟩, hf⟩ := hr.queued j hold
        have ha : j ≠ a := by intro ha; subst j; exact hn haown
        exact ⟨⟨by simpa [next, ha] using hm, hn⟩, hf⟩
      · refine ⟨outstanding_pending hs' hc' haown (by simp [next]) hnew, ?_⟩
        simp [next, (owner_singleton hs.conserved haown).2]
    | idle => exact hr.queued j hj
  · intro j hj
    cases e with
    | request a =>
      have hold : s.flight = some j := by
        by_cases ho : a ∈ s.owners <;> simpa [next, ho] using hj
      have hm := hr.transit j hold
      have ha : j ≠ a := by intro ha; subst j; rw [he.1] at hm; cases hm
      by_cases ho : a ∈ s.owners <;> simpa [next, ho, ha] using hm
    | receive => exact hr.transit j hj
    | send a b =>
      have hb : b = j := Option.some.inj hj
      subst b
      exact (hr.queued j (List.mem_of_head? he.2.2)).1.1
    | deliver => simp [next] at hj
    | enter a =>
      have hf : s.flight = none := (owner_singleton hs.conserved he.2).2
      simp [next, hf] at hj
    | leave a =>
      have hf : s.flight = none := (owner_singleton hs.conserved (hs.cs_owner a he)).2
      simp [next, hf] at hj
    | idle => exact hr.transit j hj

theorem reachable_routing {owner : NodeId n} {s : State n}
    (h : Reachable owner s) : Routing s := by
  induction h with
  | refl => exact routing_initial _
  | @tail t u e ht hs ih =>
    rcases hs with ⟨he, rfl⟩
    exact routing_step (reachable_safety ht) (reachable_counters ht) ih
      (queue_nodup_preservation ht) he


def Ready (s : State n) : Prop := ∀ i, i ∈ s.owners → s.mode i = .idle →
  ∀ j, s.rn i j = s.token.ln j + 1 → j ∈ s.token.queue

theorem ready_step {s : State n} (hs : Safety s) (_hc : Counters s)
    (hr : Routing s) (h : Ready s) {e} (he : Enabled s e) : Ready (next s e) := by
  intro i hi hm j hj
  cases e with
  | request a =>
    have hia : i ≠ a := by
      intro ha; subst i
      by_cases ho : a ∈ s.owners <;> simp [next, ho] at hm
    by_cases ho : a ∈ s.owners
    · simp only [next, if_pos ho] at *
      exact h i hi (by simpa [hia] using hm) j hj
    · simp only [next, if_neg ho] at *
      exact h i hi (by simpa [hia] using hm) j (by simpa [hia] using hj)
  | receive r =>
    by_cases hid : i = r.dest
    · subst i
      have ho : r.dest ∈ s.owners ∧ s.mode r.dest = .idle := ⟨hi, hm⟩
      simp only [next, if_pos ho]
      apply (appendPending_mem _ _ _ _).2
      right
      simpa [next, ho] using hj
    · rw [ln_receive] at hj
      have hold : j ∈ s.token.queue := h i hi hm j (by simpa [next, hid] using hj)
      simp only [next]
      split
      · exact (appendPending_mem _ _ _ _).2 (Or.inl hold)
      · exact hold
  | send a b =>
    have ho := (owner_singleton hs.conserved he.1).1
    simp [next, ho] at hi
  | deliver a =>
    have ho := flight_empty_owners hs.conserved he
    have hia : i = a := by simpa [next, ho] using hi
    subst i
    have hreq := hr.transit a he
    change s.mode a = .idle at hm
    rw [hreq] at hm
    cases hm
  | enter a =>
    have hia : i ≠ a := by intro ha; subst i; simp [next] at hm
    exact h i hi (by simpa [next, hia] using hm) j hj
  | leave a =>
    have haown := hs.cs_owner a he
    have hia : i = a := by simpa [next, (owner_singleton hs.conserved haown).1] using hi
    subst i
    exact (appendPending_mem _ _ _ _).2 (Or.inr hj)
  | idle => exact h i hi hm j hj

theorem reachable_ready {owner : NodeId n} {s : State n} (h : Reachable owner s) : Ready s := by
  induction h with
  | refl => simp [Ready, initial]
  | @tail t u e ht hs ih =>
    rcases hs with ⟨he, rfl⟩
    exact ready_step (reachable_safety ht) (reachable_counters ht) (reachable_routing ht) ih he

structure Run (n : ℕ) where
  owner : NodeId n
  state : ℕ → State n
  event : ℕ → Event n
  start : state 0 = initial owner
  valid : ∀ k, Step (state k) (event k) (state (k + 1))

theorem Run.reachable (ρ : Run n) (k : ℕ) : Reachable ρ.owner (ρ.state k) := by
  induction k with
  | zero => rw [ρ.start]; exact .refl _
  | succ k ih => exact .tail ih (ρ.valid k)

def LocalService : Event n → Prop
  | .send _ _ | .enter _ => True
  | _ => False

/-- Every continuously enabled local service action is eventually scheduled.
This does not force a client to create another request. -/
def WeakFairness (ρ : Run n) : Prop := ∀ e, LocalService e → ∀ k,
  (∀ l, k ≤ l → Enabled (ρ.state l) e) → ∃ l, k ≤ l ∧ ρ.event l = e

/-- Eventual receipt, not merely absence of a message-loss transition. -/
def ReliableDelivery (ρ : Run n) : Prop :=
  (∀ k r, r ∈ (ρ.state k).sent → ∃ l, k ≤ l ∧ r ∈ (ρ.state l).received) ∧
  (∀ k j, (ρ.state k).flight = some j → ∃ l, k ≤ l ∧ ρ.event l = .deliver j)

def FiniteCS (ρ : Run n) : Prop := ∀ k i, (ρ.state k).mode i = .inCS →
  ∃ l, k ≤ l ∧ ρ.event l = .leave i

theorem Run.rn_mono (ρ : Run n) {k l} (h : k ≤ l) (i j : NodeId n) :
    (ρ.state k).rn i j ≤ (ρ.state l).rn i j := by
  induction l, h using Nat.le_induction with
  | base => exact le_refl _
  | succ l h ih => rw [(ρ.valid l).2]; exact ih.trans (rn_monotone_step _ _ _ _)

theorem Run.ln_mono (ρ : Run n) {k l} (h : k ≤ l) (j : NodeId n) :
    (ρ.state k).token.ln j ≤ (ρ.state l).token.ln j := by
  induction l, h using Nat.le_induction with
  | base => exact le_refl _
  | succ l h ih =>
    rw [(ρ.valid l).2]
    exact ih.trans (ln_monotone_step (reachable_counters (ρ.reachable l)) _ _)

theorem received_bound {owner : NodeId n} {s : State n} (h : Reachable owner s) :
    ∀ r ∈ s.received, r.sn ≤ s.rn r.dest r.sender := by
  induction h with
  | refl => simp [initial]
  | @tail t u e ht hs ih =>
    rcases hs with ⟨he, rfl⟩
    intro r hr
    cases e with
    | receive q =>
      rcases Finset.mem_insert.mp hr with hq | hr
      · subst q; simp [next]
      · exact (ih r hr).trans (rn_monotone_step t (.receive q) _ _)
    | request a =>
      have hold : r ∈ t.received := by
        by_cases ho : a ∈ t.owners <;> simpa [next, ho] using hr
      exact (ih r hold).trans (rn_monotone_step t (.request a) _ _)
    | send => exact ih r hr
    | deliver => exact ih r hr
    | enter => exact ih r hr
    | leave => exact ih r hr
    | idle => exact ih r hr


theorem fair_persistent_action (ρ : Run n) (hf : WeakFairness ρ) (e : Event n)
    (he : LocalService e) (k : ℕ) (hk : Enabled (ρ.state k) e)
    (hp : ∀ l, k ≤ l → Enabled (ρ.state l) e → ρ.event l ≠ e → Enabled (ρ.state (l + 1)) e) :
    ∃ l, k ≤ l ∧ ρ.event l = e := by
  by_contra hn
  push Not at hn
  have hall : ∀ l, k ≤ l → Enabled (ρ.state l) e := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact hk
    | succ l hkl ih => exact hp l hkl ih (hn l hkl)
  exact hn _ (hf e he k hall).choose_spec.1 (hf e he k hall).choose_spec.2

theorem enter_persistent {s : State n} {i} (h : Enabled s (.enter i))
    {e} (he : Enabled s e) (hne : e ≠ .enter i) : Enabled (next s e) (.enter i) := by
  change s.mode i = .requesting ∧ i ∈ s.owners at h
  cases e with
  | request a =>
    have hia : i ≠ a := by intro ha; subst i; rw [he.1] at h; cases h.1
    by_cases ho : a ∈ s.owners <;> simpa [Enabled, next, ho, hia] using h
  | receive => exact h
  | send a b =>
    have hia : i ≠ a := by intro ha; subst i; rw [he.2.1] at h; cases h.1
    exact ⟨h.1, by simpa [next, hia] using h.2⟩
  | deliver => exact ⟨h.1, Finset.mem_insert_of_mem h.2⟩
  | enter a =>
    have hia : i ≠ a := by intro ha; subst i; exact hne rfl
    exact ⟨by simpa [next, hia] using h.1, h.2⟩
  | leave a =>
    have hia : i ≠ a := by intro ha; subst i; rw [he] at h; cases h.1
    exact ⟨by simpa [next, hia] using h.1, h.2⟩
  | idle => exact h

theorem holder_enters (ρ : Run n) (hf : WeakFairness ρ) {k i}
    (hk : Enabled (ρ.state k) (.enter i)) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode i = .inCS := by
  obtain ⟨l, hkl, hl⟩ := fair_persistent_action ρ hf (.enter i) trivial k hk (by
    intro l _ he hne
    rw [(ρ.valid l).2]
    exact enter_persistent he (ρ.valid l).1 hne)
  exact ⟨l + 1, by omega, by rw [(ρ.valid l).2, hl]; simp [next]⟩

theorem appendPending_head {q : List (NodeId n)} {j} (h : q.head? = some j) (rn ln) :
    (appendPending q rn ln).head? = some j := by
  cases q with
  | nil => simp at h
  | cons a q => simpa [appendPending] using h

theorem send_persistent {s : State n} (hs : Safety s) {i j}
    (h : Enabled s (.send i j)) {e} (he : Enabled s e) (hne : e ≠ .send i j) :
    Enabled (next s e) (.send i j) := by
  change i ∈ s.owners ∧ s.mode i = .idle ∧ s.token.queue.head? = some j at h
  cases e with
  | request a =>
    have hia : i ≠ a := by
      intro ha; subst i
      have hq := he.2 h.1
      rw [hq] at h
      cases h.2.2
    by_cases ho : a ∈ s.owners <;> simpa [Enabled, next, ho, hia] using h
  | receive r =>
    refine ⟨h.1, h.2.1, ?_⟩
    simp only [next]
    split
    · exact appendPending_head h.2.2 _ _
    · exact h.2.2
  | send a b =>
    have ha : a = i := by simpa [(owner_singleton hs.conserved h.1).1] using he.1
    have hb : b = j := Option.some.inj (he.2.2.symm.trans h.2.2)
    subst a; subst b
    exact False.elim (hne rfl)
  | deliver a =>
    have hz := (owner_singleton hs.conserved h.1).2
    rw [show s.flight = some a from he] at hz
    cases hz
  | enter a =>
    have ha : a = i := by simpa [(owner_singleton hs.conserved h.1).1] using he.2
    subst a
    change s.mode i = .requesting ∧ i ∈ s.owners at he
    rw [h.2.1] at he
    cases he.1
  | leave a =>
    have ha : a = i := by
      simpa [(owner_singleton hs.conserved h.1).1] using hs.cs_owner a he
    subst a
    change s.mode i = .inCS at he
    rw [h.2.1] at he
    cases he
  | idle => exact h

theorem idle_holder_sends (ρ : Run n) (hf : WeakFairness ρ) {k i j}
    (hk : Enabled (ρ.state k) (.send i j)) :
    ∃ l, k ≤ l ∧ ρ.event l = .send i j :=
  fair_persistent_action ρ hf (.send i j) trivial k hk (by
    intro l _ he hne
    rw [(ρ.valid l).2]
    exact send_persistent (reachable_safety (ρ.reachable l)) he (ρ.valid l).1 hne)

/-- Under progress contracts the token eventually reaches an idle holder. -/
theorem eventually_idle_holder (ρ : Run n) (hd : ReliableDelivery ρ) (hf : WeakFairness ρ)
    (hc : FiniteCS ρ) (k : ℕ) :
    ∃ l, k ≤ l ∧ ∃ i, i ∈ (ρ.state l).owners ∧ (ρ.state l).mode i = .idle := by
  have holder : ∃ a, k ≤ a ∧ ∃ i, i ∈ (ρ.state a).owners := by
    have hs := reachable_safety (ρ.reachable k)
    cases ht : (ρ.state k).flight with
    | none =>
      have hp : 0 < (ρ.state k).owners.card := by
        have h := hs.conserved
        simp [tokenCount, ht] at h
        omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
      exact ⟨k, le_refl _, i, hi⟩
    | some j =>
      obtain ⟨l, hkl, hl⟩ := hd.2 k j ht
      exact ⟨l + 1, by omega, j, by rw [(ρ.valid l).2, hl]; simp [next]⟩
  obtain ⟨a, hka, i, hi⟩ := holder
  have finish : ∀ b, a ≤ b → (ρ.state b).mode i = .inCS →
      ∃ l, k ≤ l ∧ ∃ j, j ∈ (ρ.state l).owners ∧ (ρ.state l).mode j = .idle := by
    intro b hab hb
    obtain ⟨c, hbc, hc'⟩ := hc b i hb
    have hi' := (reachable_safety (ρ.reachable c)).cs_owner i (by
      have he := (ρ.valid c).1; rw [hc'] at he; exact he)
    exact ⟨c + 1, by omega, i, by simpa [(ρ.valid c).2, hc', next] using hi',
      by rw [(ρ.valid c).2, hc']; simp [next]⟩
  cases hm : (ρ.state a).mode i with
  | idle => exact ⟨a, hka, i, hi, hm⟩
  | inCS => exact finish a (le_refl _) hm
  | requesting =>
    obtain ⟨b, hab, hb⟩ := holder_enters ρ hf ⟨hm, hi⟩
    exact finish b hab hb


def IsSend : Event n → Prop
  | .send _ _ => True
  | _ => False

theorem appendPending_idx {q : List (NodeId n)} {j} (h : j ∈ q) (rn ln) :
    (appendPending q rn ln).idxOf j = q.idxOf j := List.idxOf_append_of_mem h

theorem queue_movement {s : State n} {j} (hj : j ∈ s.token.queue) {e}
    (he : Enabled s e) (hf : (next s e).flight ≠ some j) :
    j ∈ (next s e).token.queue ∧
    (next s e).token.queue.idxOf j ≤ s.token.queue.idxOf j ∧
    (IsSend e → (next s e).token.queue.idxOf j < s.token.queue.idxOf j) := by
  have append (rn ln) : j ∈ appendPending s.token.queue rn ln ∧
      (appendPending s.token.queue rn ln).idxOf j ≤ s.token.queue.idxOf j :=
    ⟨(appendPending_mem _ _ _ _).2 (Or.inl hj), (appendPending_idx hj _ _).le⟩
  cases e with
  | request a =>
    by_cases ho : a ∈ s.owners <;> simp [next, ho, hj, IsSend]
  | receive r =>
    simp only [next]
    split
    · exact ⟨(append _ _).1, (append _ _).2, False.elim⟩
    · exact ⟨hj, le_refl _, False.elim⟩
  | send a b =>
    have hbj : b ≠ j := by simpa [next] using hf
    have hlist : s.token.queue = b :: s.token.queue.tail :=
      List.eq_cons_of_mem_head? he.2.2
    have hm : j ∈ s.token.queue.tail := by
      rw [hlist] at hj
      exact (List.mem_cons.mp hj).resolve_left (Ne.symm hbj)
    have hx : s.token.queue.idxOf j = s.token.queue.tail.idxOf j + 1 := by
      conv_lhs => rw [hlist]
      exact List.idxOf_cons_ne _ hbj
    exact ⟨hm, by change s.token.queue.tail.idxOf j ≤ s.token.queue.idxOf j; omega,
      fun _ => by change s.token.queue.tail.idxOf j < s.token.queue.idxOf j; omega⟩
  | deliver => exact ⟨hj, le_refl _, False.elim⟩
  | enter => exact ⟨hj, le_refl _, False.elim⟩
  | leave a => exact ⟨(append _ _).1, (append _ _).2, False.elim⟩
  | idle => exact ⟨hj, le_refl _, False.elim⟩

theorem queued_eventually_token (ρ : Run n) (hd : ReliableDelivery ρ) (hw : WeakFairness ρ)
    (hc : FiniteCS ρ) {k j} (hj : j ∈ (ρ.state k).token.queue) :
    ∃ l, k ≤ l ∧ j ∈ (ρ.state l).owners := by
  classical
  by_contra hn
  push Not at hn
  have noflight : ∀ l, k ≤ l → (ρ.state l).flight ≠ some j := by
    intro l hkl hflight
    obtain ⟨b, hlb, hb⟩ := hd.2 l j hflight
    apply hn (b + 1) (by omega)
    rw [(ρ.valid b).2, hb]
    simp [next]
  have grow : ∀ a, k ≤ a → j ∈ (ρ.state a).token.queue → ∀ b, a ≤ b →
      j ∈ (ρ.state b).token.queue ∧
      (ρ.state b).token.queue.idxOf j ≤ (ρ.state a).token.queue.idxOf j := by
    intro a hka ha b hab
    induction b, hab using Nat.le_induction with
    | base => exact ⟨ha, le_refl _⟩
    | succ b hab ih =>
      have step := queue_movement ih.1 (ρ.valid b).1
        (by rw [← (ρ.valid b).2]; exact noflight (b + 1) (by omega))
      rw [← (ρ.valid b).2] at step
      exact ⟨step.1, step.2.1.trans ih.2⟩
  have existsRank : ∃ d, ∃ a, k ≤ a ∧ (ρ.state a).token.queue.idxOf j = d :=
    ⟨_, k, le_refl _, rfl⟩
  obtain ⟨a, hka, ha⟩ := Nat.find_spec existsRank
  obtain ⟨b, hab, i, hi, hm⟩ := eventually_idle_holder ρ hd hw hc a
  have hkb := hka.trans hab
  have hmem := (grow k (le_refl _) hj b hkb).1
  have hnonempty : (ρ.state b).token.queue ≠ [] := List.ne_nil_of_mem hmem
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hnonempty
  have hen : Enabled (ρ.state b) (.send i x) := ⟨hi, hm, by simp [hx]⟩
  obtain ⟨c, hbc, hevent⟩ := idle_holder_sends ρ hw hen
  have hkc := hkb.trans hbc
  have hcmem := (grow k (le_refl _) hj c hkc).1
  have hstep := queue_movement hcmem (ρ.valid c).1
    (by rw [← (ρ.valid c).2]; exact noflight (c + 1) (by omega))
  rw [← (ρ.valid c).2] at hstep
  have hlt := hstep.2.2 (by simp [hevent, IsSend])
  have hmin : Nat.find existsRank ≤ (ρ.state (c + 1)).token.queue.idxOf j :=
    Nat.find_min' existsRank ⟨c + 1, by omega, rfl⟩
  have hca := (grow a hka (grow k (le_refl _) hj a hka).1 c (hab.trans hbc)).2
  omega


theorem requesting_next {s : State n} {j} (hj : s.mode j = .requesting)
    {e} (he : Enabled s e) :
    (next s e).mode j = .requesting ∨ (next s e).mode j = .inCS := by
  cases e with
  | request a =>
    have hja : j ≠ a := by intro ha; subst j; rw [he.1] at hj; cases hj
    left; by_cases ho : a ∈ s.owners <;> simpa [next, ho, hja] using hj
  | receive => exact Or.inl hj
  | send => exact Or.inl hj
  | deliver => exact Or.inl hj
  | enter a =>
    by_cases hja : j = a
    · right; simp [next, hja]
    · left; simpa [next, hja] using hj
  | leave a =>
    have hja : j ≠ a := by intro ha; subst j; rw [he] at hj; cases hj
    left; simpa [next, hja] using hj
  | idle => exact Or.inl hj

theorem requesting_self_stable {s : State n} (hc : Counters s) {j}
    (hj : s.mode j = .requesting) {e} (he : Enabled s e) :
    (next s e).rn j j = s.rn j j := by
  cases e with
  | request a =>
    have hja : j ≠ a := by intro ha; subst j; rw [he.1] at hj; cases hj
    exact self_unchanged_request hja
  | receive r => exact self_receive (hc.sent_bound r he.1).1 j
  | send => rfl
  | deliver => rfl
  | enter => rfl
  | leave => rfl
  | idle => rfl

/-- Every observed pending invocation enters; later client requests are permitted.
The assumptions contain delivery, local scheduling and CS exit, not the conclusion. -/
theorem starvation_freedom_under_liveness (ρ : Run n) (hd : ReliableDelivery ρ)
    (hf : WeakFairness ρ) (hc : FiniteCS ρ) {k j}
    (hj : (ρ.state k).mode j = .requesting) :
    ∃ l, k ≤ l ∧ (ρ.state l).mode j = .inCS := by
  classical
  by_contra hn
  push Not at hn
  have waiting : ∀ l, k ≤ l → (ρ.state l).mode j = .requesting := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => exact hj
    | succ l hkl ih =>
      have hstep := requesting_next ih (ρ.valid l).1
      rw [← (ρ.valid l).2] at hstep
      exact hstep.resolve_right (hn (l + 1) (by omega))
  have noowner : ∀ l, k ≤ l → j ∉ (ρ.state l).owners := by
    intro l hkl ho
    obtain ⟨b, hlb, hb⟩ := holder_enters ρ hf ⟨waiting l hkl, ho⟩
    exact hn b (hkl.trans hlb) hb
  have stable : ∀ l, k ≤ l → (ρ.state l).rn j j = (ρ.state k).rn j j := by
    intro l hkl
    induction l, hkl using Nat.le_induction with
    | base => rfl
    | succ l hkl ih =>
      rw [(ρ.valid l).2, requesting_self_stable
        (reachable_counters (ρ.reachable l)) (waiting l hkl) (ρ.valid l).1, ih]
  have broadcast := (reachable_routing (ρ.reachable k)).foreign j ⟨hj, noowner k (le_refl _)⟩
  have delivery : ∀ i, ∃ a, k ≤ a ∧ (ρ.state k).rn j j ≤ (ρ.state a).rn i j := by
    intro i
    by_cases hi : i = j
    · subst i; exact ⟨k, le_refl _, le_refl _⟩
    · obtain ⟨a, hka, ha⟩ := hd.1 k ⟨j, (ρ.state k).rn j j, i⟩ (broadcast.2 i hi)
      exact ⟨a, hka, received_bound (ρ.reachable a) _ ha⟩
  choose times ht using delivery
  let b := max k (Finset.univ.sup times)
  have hkb : k ≤ b := le_max_left _ _
  have known : ∀ l, b ≤ l → ∀ i, (ρ.state k).rn j j ≤ (ρ.state l).rn i j := by
    intro l hbl i
    have hib : times i ≤ b := (Finset.le_sup (Finset.mem_univ i)).trans (le_max_right _ _)
    exact (ht i).2.trans (ρ.rn_mono (hib.trans hbl) i j)
  obtain ⟨a, hba, i, hi, hm⟩ := eventually_idle_holder ρ hd hf hc b
  have hka := hkb.trans hba
  have hgap := ((reachable_routing (ρ.reachable a)).foreign j ⟨waiting a hka, noowner a hka⟩).1
  have hupper := (reachable_counters (ρ.reachable a)).rn_bound i j
  have hlower := known a hba i
  have hstable := stable a hka
  have hout : (ρ.state a).rn i j = (ρ.state a).token.ln j + 1 := by omega
  have hqueued := reachable_ready (ρ.reachable a) i hi hm j hout
  obtain ⟨l, hal, hl⟩ := queued_eventually_token ρ hd hf hc hqueued
  exact noowner l (hka.trans hal) hl


theorem sequence_number_monotonicity {owner : NodeId n} {s t : State n} {e}
    (hr : Reachable owner s) (he : Step s e t) :
    (∀ i j, s.rn i j ≤ t.rn i j) ∧ (∀ j, s.token.ln j ≤ t.token.ln j) ∧
    (∀ j, t.token.ln j ≤ t.rn j j) := by
  rcases he with ⟨he, rfl⟩
  exact ⟨rn_monotone_step s e, ln_monotone_step (reachable_counters hr) e,
    (counters_step (reachable_counters hr) he).ln_bound⟩

theorem nonholder_request_strict {s : State n} {i} (h : i ∉ s.owners) :
    (next s (.request i)).rn i i = s.rn i i + 1 := by simp [next, h]

theorem holder_request_keeps_sequence {s : State n} {i} (h : i ∈ s.owners) :
    (next s (.request i)).rn i i = s.rn i i := by simp [next, h]

/-- The shared semantic payload coordinate cannot mutate while its only location
is the in-flight message. Delivery transfers that same payload. -/
theorem in_flight_payload_stability {owner : NodeId n} {s : State n} (hr : Reachable owner s)
    {j e} (hj : s.flight = some j) (he : Enabled s e) : (next s e).token = s.token := by
  have hs := reachable_safety hr
  have ho := flight_empty_owners hs.conserved hj
  cases e with
  | request i => simp [next, ho]
  | receive r => simp [next, ho]
  | send i k => have hm := he.1; simp [ho] at hm
  | deliver => rfl
  | enter => rfl
  | leave i => have hm := hs.cs_owner i he; simp [ho] at hm
  | idle => rfl

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
  | cons e es ih => intro u hu; exact ih h.2 u (.tail hu ⟨h.1, rfl⟩)

theorem valid_trace_reachable {owner : NodeId n} {es} (h : ValidTrace (initial owner) es) :
    Reachable owner (runTrace (initial owner) es) :=
  valid_trace_execution h _ (.refl _)

/-- A reachable holder can know less than the service history transported by the token. -/
def staleHolderTrace : List (Event 3) :=
  [.request 1, .request 2, .receive ⟨1,1,0⟩, .receive ⟨2,1,0⟩,
   .send 0 1, .deliver 1, .enter 1, .leave 1, .send 1 2, .deliver 2]

def staleHolder : State 3 := runTrace (initial 0) staleHolderTrace

theorem holder_rn_can_lag_ln : Reachable 0 staleHolder ∧ 2 ∈ staleHolder.owners ∧
    staleHolder.rn 2 1 = 0 ∧ staleHolder.token.ln 1 = 1 := by
  refine ⟨valid_trace_reachable (by decide : ValidTrace (initial 0) staleHolderTrace), ?_⟩
  decide

/-- An execution with a real pending request and no network service. -/
def withheldRun : Run 2 where
  owner := 0
  state k := if k = 0 then initial 0 else next (initial 0) (.request 1)
  event k := if k = 0 then .request 1 else .idle
  start := rfl
  valid k := by cases k <;> simp [Step, Enabled, next, initial]

theorem reliable_delivery_is_necessary :
    (withheldRun.state 1).mode 1 = .requesting ∧
    (∀ k, (withheldRun.state k).mode 1 ≠ .inCS) ∧ ¬ ReliableDelivery withheldRun := by
  refine ⟨rfl, ?_, ?_⟩
  · intro k; cases k <;> simp [withheldRun, next, initial]
  · intro hd
    obtain ⟨l, _, hl⟩ := hd.1 1 ⟨1,1,0⟩ (by decide)
    cases l <;> simp [withheldRun, next, initial] at hl

structure DistributedSuzukiKasamiSuite : Prop where
  conservation : ∀ n (owner : NodeId n) s, Reachable owner s → tokenCount s = 1
  exclusion : ∀ n (owner : NodeId n) s, Reachable owner s → ∀ i j, i ≠ j →
    s.mode i = .inCS → s.mode j = .inCS → False
  counters : ∀ n (owner : NodeId n) s, Reachable owner s → Counters s
  queue : ∀ n (owner : NodeId n) s, Reachable owner s → s.token.queue.Nodup
  routing : ∀ n (owner : NodeId n) s, Reachable owner s → Routing s
  progress : ∀ n (ρ : Run n), ReliableDelivery ρ → WeakFairness ρ → FiniteCS ρ →
    ∀ k j, (ρ.state k).mode j = .requesting → ∃ l, k ≤ l ∧ (ρ.state l).mode j = .inCS
  stale_view : Reachable 0 staleHolder ∧ 2 ∈ staleHolder.owners ∧
    staleHolder.rn 2 1 = 0 ∧ staleHolder.token.ln 1 = 1

theorem distributed_suzuki_kasami_master_suite : DistributedSuzukiKasamiSuite where
  conservation := fun _ _ _ => token_uniqueness_invariant
  exclusion := fun _ _ _ h _ _ => mutual_exclusion_safety h
  counters := fun _ _ _ => reachable_counters
  queue := fun _ _ _ => queue_nodup_preservation
  routing := fun _ _ _ => reachable_routing
  progress := fun _ ρ hd hf hc _ _ => starvation_freedom_under_liveness ρ hd hf hc
  stale_view := holder_rn_can_lag_ln

end DistributedSuzukiKasamiMutex
