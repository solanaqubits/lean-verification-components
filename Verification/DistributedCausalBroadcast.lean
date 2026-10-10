/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedVectorClocksCausalOrder
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union

/-! Causal multicast in a fixed, failure-free group. Archive parents and delivery
logs are ghost observations: readiness only reads message timestamps and counters.
Network arrival is separate from application delivery. -/
namespace DistributedCausalBroadcast

abbrev NodeId (n : ℕ) := Fin n
abbrev VectorClock (n : ℕ) := NodeId n → ℕ

@[ext] structure MessageId (n : ℕ) where
  sender : NodeId n
  seq : ℕ
  deriving DecidableEq, Repr

structure Message (n : ℕ) where
  id : MessageId n
  timestamp : VectorClock n

instance : DecidableEq (Message n) := fun a b =>
  decidable_of_iff (a.id = b.id ∧ a.timestamp = b.timestamp) (by
    cases a; cases b; simp)

structure Record (n : ℕ) where
  message : Message n
  parents : Finset (MessageId n)
  birth : ℕ

instance : DecidableEq (Record n) := fun a b =>
  decidable_of_iff (a.message = b.message ∧ a.parents = b.parents ∧ a.birth = b.birth) (by
    cases a; cases b; simp)

structure NodeState (n : ℕ) where
  delivered : VectorClock n
  buffer : Finset (Message n)
  log : List (MessageId n)

structure Config (n : ℕ) where
  node : NodeId n → NodeState n
  archive : List (Record n)

variable {n : ℕ}

def prefixIds (v : VectorClock n) : Finset (MessageId n) :=
  Finset.univ.biUnion fun s => (Finset.range (v s)).image fun j => ⟨s, j + 1⟩

@[simp] theorem mem_prefix (a : MessageId n) (v : VectorClock n) :
    a ∈ prefixIds v ↔ 0 < a.seq ∧ a.seq ≤ v a.sender := by
  rcases a with ⟨s,j⟩
  simp only [prefixIds, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image,
    Finset.mem_range, MessageId.mk.injEq]
  constructor
  · rintro ⟨k,i,hi,hk,hj⟩
    subst k
    omega
  · rintro ⟨hj,hv⟩
    exact ⟨s,j - 1,by omega,rfl,by omega⟩

def tick (s : NodeId n) (v : VectorClock n) : VectorClock n :=
  Function.update v s (v s + 1)

def nextMessage (C : Config n) (s : NodeId n) : Message n :=
  ⟨⟨s, (C.node s).delivered s + 1⟩, tick s (C.node s).delivered⟩

def NodeState.accept (st : NodeState n) (m : Message n) : NodeState n :=
  ⟨tick m.id.sender st.delivered, st.buffer.erase m, st.log ++ [m.id]⟩

def IsReady (st : NodeState n) (m : Message n) : Prop :=
  m.timestamp m.id.sender = st.delivered m.id.sender + 1 ∧
    ∀ k, k ≠ m.id.sender → m.timestamp k ≤ st.delivered k

instance (st : NodeState n) (m : Message n) : Decidable (IsReady st m) :=
  inferInstanceAs (Decidable (_ ∧ _))

def broadcast (C : Config n) (s : NodeId n) : Config n :=
  let m := nextMessage C s
  ⟨Function.update C.node s ((C.node s).accept m),
    C.archive ++ [⟨m,(C.node s).log.toFinset,C.archive.length⟩]⟩

def arrive (C : Config n) (p : NodeId n) (m : Message n) : Config n :=
  ⟨Function.update C.node p { C.node p with buffer := insert m (C.node p).buffer },C.archive⟩

def deliver (C : Config n) (p : NodeId n) (m : Message n) : Config n :=
  ⟨Function.update C.node p ((C.node p).accept m),C.archive⟩

def initial (n : ℕ) : Config n := ⟨fun _ => ⟨fun _ => 0,∅,[]⟩,[]⟩

inductive Action (n : ℕ) where
  | idle
  | broadcast (sender : NodeId n)
  | arrive (receiver : NodeId n) (message : Message n)
  | deliver (receiver : NodeId n) (message : Message n)

/-- Only authenticity at arrival and the numerical Ready test guard deliveries. -/
inductive Step : Config n → Action n → Config n → Prop where
  | idle (C : Config n) : Step C .idle C
  | broadcast (C : Config n) (s : NodeId n) : Step C (.broadcast s) (broadcast C s)
  | arrive (C : Config n) (p : NodeId n) (r : Record n) (hr : r ∈ C.archive) :
      Step C (.arrive p r.message) (arrive C p r.message)
  | deliver (C : Config n) (p : NodeId n) (m : Message n)
      (hm : m ∈ (C.node p).buffer) (ready : IsReady (C.node p) m) :
      Step C (.deliver p m) (deliver C p m)

inductive Reachable : Config n → Prop where
  | initial : Reachable (initial n)
  | step {C D : Config n} {a : Action n} : Reachable C → Step C a D → Reachable D

/-- Independent graph: an edge records an actual delivery observed before a broadcast.
In particular it contains the sender's previous self-deliveries. No clock comparison. -/
def Parent (C : Config n) (a b : MessageId n) : Prop :=
  ∃ r ∈ C.archive, r.message.id = b ∧ a ∈ r.parents

def MsgHappensBefore (C : Config n) := Relation.TransGen (Parent C)

def OccursBefore (a b : MessageId n) (l : List (MessageId n)) : Prop :=
  a ∈ l ∧ b ∈ l ∧ l.idxOf a < l.idxOf b

/-- The following is a derived invariant, never a transition guard. -/
structure Invariant (C : Config n) : Prop where
  prefix_log : ∀ p a, a ∈ (C.node p).log ↔ a ∈ prefixIds (C.node p).delivered
  nodup : ∀ p, (C.node p).log.Nodup
  bounded : ∀ p k, (C.node p).delivered k ≤ (C.node k).delivered k
  issued : ∀ a, (∃ r ∈ C.archive, r.message.id = a) ↔ a ∈ prefixIds (fun k => (C.node
    k).delivered k)
  unique : ∀ r ∈ C.archive, ∀ t ∈ C.archive, r.message.id = t.message.id → r = t
  authentic : ∀ p m, m ∈ (C.node p).buffer → ∃ r ∈ C.archive, r.message = m
  stamp : ∀ r ∈ C.archive, r.message.timestamp r.message.id.sender = r.message.id.seq
  past : ∀ r ∈ C.archive, insert r.message.id r.parents = prefixIds r.message.timestamp
  not_self : ∀ r ∈ C.archive, r.message.id ∉ r.parents
  past_closed : ∀ r ∈ C.archive, ∀ t ∈ C.archive,
    t.message.id ∈ r.parents → t.parents ⊆ r.parents
  parent_rank : ∀ r ∈ C.archive, ∀ t ∈ C.archive,
    t.message.id ∈ r.parents → t.birth < r.birth
  birth_bound : ∀ r ∈ C.archive, r.birth < C.archive.length
  ordered : ∀ p r, r ∈ C.archive → r.message.id ∈ (C.node p).log →
    ∀ a ∈ r.parents, OccursBefore a r.message.id (C.node p).log


@[simp] theorem tick_self (s : NodeId n) (v : VectorClock n) : tick s v s = v s + 1 := by
  simp [tick]

@[simp] theorem tick_other (s k : NodeId n) (v : VectorClock n) (h : k ≠ s) :
    tick s v k = v k := by simp [tick,h]

theorem le_tick (s : NodeId n) (v : VectorClock n) (k : NodeId n) : v k ≤ tick s v k := by
  by_cases h : k = s
  · subst k; simp
  · simp [tick,h]

theorem prefix_tick (s : NodeId n) (v : VectorClock n) :
    prefixIds (tick s v) = insert ⟨s,v s + 1⟩ (prefixIds v) := by
  ext a
  simp only [mem_prefix, Finset.mem_insert]
  by_cases h : a.sender = s
  · have eqid : a = ⟨s,v s + 1⟩ ↔ a.seq = v s + 1 := by
      cases a; simp_all
    simp only [h,tick_self,eqid]
    omega
  · have hn : a ≠ ⟨s,v s + 1⟩ := by intro he; exact h (congrArg MessageId.sender he)
    simp [tick_other _ _ _ h,hn]

theorem prefix_mono {v w : VectorClock n} (h : ∀ k, v k ≤ w k) : prefixIds v ⊆ prefixIds w := by
  intro a ha
  exact (mem_prefix _ _).2 ⟨((mem_prefix _ _).1 ha).1,
    le_trans ((mem_prefix _ _).1 ha).2 (h a.sender)⟩

theorem before_append {a b : MessageId n} {l : List (MessageId n)}
    (h : OccursBefore a b l) (xs : List (MessageId n)) : OccursBefore a b (l ++ xs) := by
  rcases h with ⟨ha,hb,hi⟩
  exact ⟨List.mem_append_left _ ha,List.mem_append_left _ hb,by
    simpa only [List.idxOf_append_of_mem ha,List.idxOf_append_of_mem hb] using hi⟩

theorem before_new {a b : MessageId n} {l : List (MessageId n)}
    (ha : a ∈ l) (hb : b ∉ l) : OccursBefore a b (l ++ [b]) := by
  refine ⟨by simp [ha],by simp,?_⟩
  simpa only [List.idxOf_append_of_mem ha,List.idxOf_append_of_notMem hb,
    List.idxOf_cons_self,Nat.add_zero] using List.idxOf_lt_length_of_mem ha

theorem Invariant.log_issued {C : Config n} (h : Invariant C) {p : NodeId n}
    {a : MessageId n} (ha : a ∈ (C.node p).log) : ∃ r ∈ C.archive, r.message.id = a := by
  apply (h.issued a).2
  exact prefix_mono (h.bounded p) ((h.prefix_log p a).1 ha)

theorem Invariant.record_in_own_log {C : Config n} (h : Invariant C)
    {r : Record n} (hr : r ∈ C.archive) : r.message.id ∈ (C.node r.message.id.sender).log := by
  apply (h.prefix_log _ _).2
  simpa only [mem_prefix] using (h.issued r.message.id).1 ⟨r,hr,rfl⟩

theorem Invariant.parent_issued {C : Config n} (h : Invariant C)
    {r : Record n} (hr : r ∈ C.archive) {a : MessageId n} (ha : a ∈ r.parents) :
    ∃ t ∈ C.archive, t.message.id = a :=
  h.log_issued (h.ordered _ _ hr (h.record_in_own_log hr) _ ha).1

theorem Invariant.fresh {C : Config n} (h : Invariant C) (s : NodeId n) :
    ¬ ∃ r ∈ C.archive, r.message.id = (nextMessage C s).id := by
  rw [h.issued]
  simp [nextMessage]

theorem Invariant.fresh_log {C : Config n} (h : Invariant C) (s p : NodeId n) :
    (nextMessage C s).id ∉ (C.node p).log := fun ha => h.fresh s (h.log_issued ha)

theorem Invariant.ready_new {C : Config n} (h : Invariant C) {p : NodeId n}
    {r : Record n} (hr : r ∈ C.archive) (ready : IsReady (C.node p) r.message) :
    r.message.id ∉ (C.node p).log := by
  intro ha
  have he := ((mem_prefix _ _).1 ((h.prefix_log _ _).1 ha)).2
  have hs := h.stamp r hr
  have ht := ready.1
  omega

theorem Invariant.ready_parents {C : Config n} (h : Invariant C) {p : NodeId n}
    {r : Record n} (hr : r ∈ C.archive) (ready : IsReady (C.node p) r.message) :
    ∀ a ∈ r.parents, a ∈ (C.node p).log := by
  intro a ha
  have ht : a ∈ prefixIds r.message.timestamp := by
    rw [← h.past r hr]
    exact Finset.mem_insert_of_mem ha
  rcases (mem_prefix _ _).1 ht with ⟨hp,hle⟩
  apply (h.prefix_log _ _).2
  apply (mem_prefix _ _).2
  refine ⟨hp,?_⟩
  by_cases hs : a.sender = r.message.id.sender
  · have hne : a.seq ≠ r.message.id.seq := by
      intro hh
      have : a = r.message.id := MessageId.ext hs hh
      subst a
      exact h.not_self r hr ha
    have st := h.stamp r hr
    have rt := ready.1
    rw [hs] at hle ⊢
    omega
  · exact le_trans hle (ready.2 _ hs)

theorem initial_invariant : Invariant (initial n) where
  prefix_log := by simp [initial,mem_prefix]; omega
  nodup := by simp [initial]
  bounded := by simp [initial]
  issued := by simp [initial,mem_prefix]; omega
  unique := by simp [initial]
  authentic := by simp [initial]
  stamp := by simp [initial]
  past := by simp [initial]
  not_self := by simp [initial]
  past_closed := by simp [initial]
  parent_rank := by simp [initial]
  birth_bound := by simp [initial]
  ordered := by simp [initial]


theorem Invariant.arrive_preserves {C : Config n} (h : Invariant C) (p : NodeId n)
    (r : Record n) (hr : r ∈ C.archive) : Invariant (arrive C p r.message) := by
  have clocks : ∀ q, ((arrive C p r.message).node q).delivered = (C.node q).delivered := by
    intro q; by_cases he : q = p <;> simp [arrive,he]
  have logs : ∀ q, ((arrive C p r.message).node q).log = (C.node q).log := by
    intro q; by_cases he : q = p <;> simp [arrive,he]
  refine ⟨?_,?_,?_,?_,h.unique,?_,h.stamp,h.past,h.not_self,h.past_closed,
    h.parent_rank,h.birth_bound,?_⟩
  · simpa only [logs,clocks] using h.prefix_log
  · simpa only [logs] using h.nodup
  · simpa only [clocks] using h.bounded
  · simp only [clocks]
    exact h.issued
  · intro q m hm
    by_cases he : q = p
    · subst q
      simp only [arrive,Function.update_self,Finset.mem_insert] at hm
      rcases hm with rfl | hm
      · exact ⟨r,hr,rfl⟩
      · exact h.authentic p m hm
    · simp only [arrive,Function.update_of_ne he] at hm
      exact h.authentic q m hm
  · simp only [logs]
    exact h.ordered

theorem accept_prefix {st : NodeState n} {m : Message n}
    (hp : ∀ a, a ∈ st.log ↔ a ∈ prefixIds st.delivered)
    (hs : m.id.seq = st.delivered m.id.sender + 1) :
    ∀ a, a ∈ (st.accept m).log ↔ a ∈ prefixIds (st.accept m).delivered := by
  intro a
  simp only [NodeState.accept,List.mem_append,List.mem_singleton,prefix_tick,Finset.mem_insert,hp]
  have he : (⟨m.id.sender,st.delivered m.id.sender + 1⟩ : MessageId n) = m.id :=
    MessageId.ext rfl hs.symm
  rw [he,or_comm]

theorem accept_nodup {st : NodeState n} {m : Message n}
    (h : st.log.Nodup) (hm : m.id ∉ st.log) : (st.accept m).log.Nodup := by
  suffices ∀ a ∈ st.log, a ≠ m.id by
    simpa [NodeState.accept,List.nodup_append,h] using this
  intro a ha he
  subst a
  exact hm ha

theorem Invariant.deliver_preserves {C : Config n} (h : Invariant C) (p : NodeId n)
    (r : Record n) (hr : r ∈ C.archive) (ready : IsReady (C.node p) r.message) :
    Invariant (deliver C p r.message) := by
  have seqeq : r.message.id.seq = (C.node p).delivered r.message.id.sender + 1 :=
    (h.stamp r hr).symm.trans ready.1
  have fresh := h.ready_new hr ready
  have parents := h.ready_parents hr ready
  have pn : p ≠ r.message.id.sender := by
    intro he
    subst p
    exact fresh (h.record_in_own_log hr)
  have own : ∀ k, ((deliver C p r.message).node k).delivered k = (C.node k).delivered k := by
    intro k
    by_cases he : k = p
    · subst k; simp [deliver,NodeState.accept,tick,pn]
    · simp [deliver,he]
  have logs (q : NodeId n) : ((deliver C p r.message).node q).log =
      if q = p then (C.node p).log ++ [r.message.id] else (C.node q).log := by
    by_cases he : q = p <;> simp [deliver,NodeState.accept,he]
  refine ⟨?_,?_,?_,?_,h.unique,?_,h.stamp,h.past,h.not_self,h.past_closed,
    h.parent_rank,h.birth_bound,?_⟩
  · intro q a
    by_cases he : q = p
    · subst q
      simpa only [deliver,Function.update_self] using accept_prefix (h.prefix_log p) seqeq a
    · simpa [deliver,he] using h.prefix_log q a
  · intro q
    by_cases he : q = p
    · subst q; simpa only [deliver,Function.update_self] using accept_nodup (h.nodup p) fresh
    · simpa [deliver,he] using h.nodup q
  · intro q k
    rw [own]
    by_cases he : q = p
    · subst q
      simp only [deliver,Function.update_self,NodeState.accept]
      by_cases hk : k = r.message.id.sender
      · subst k
        rw [tick_self,← seqeq]
        exact ((mem_prefix _ _).1 ((h.issued _).1 ⟨r,hr,rfl⟩)).2
      · simpa [tick,hk] using h.bounded p k
    · simpa [deliver,he] using h.bounded q k
  · simp only [own]
    exact h.issued
  · intro q m hm
    by_cases he : q = p
    · subst q
      simp only [deliver,Function.update_self,NodeState.accept,Finset.mem_erase] at hm
      exact h.authentic p m hm.2
    · simp only [deliver,Function.update_of_ne he] at hm
      exact h.authentic q m hm
  · intro q t ht hmem a ha
    by_cases he : q = p
    · subst q
      rw [logs,if_pos rfl] at hmem ⊢
      rcases List.mem_append.mp hmem with hm | hm
      · exact before_append (h.ordered p t ht hm a ha) _
      · have eqid : t.message.id = r.message.id := List.mem_singleton.mp hm
        have eqr : t = r := h.unique t ht r hr eqid
        subst t
        exact before_new (parents a ha) fresh
    · rw [logs,if_neg he] at hmem ⊢
      exact h.ordered q t ht hmem a ha


theorem Invariant.broadcast_preserves {C : Config n} (h : Invariant C) (s : NodeId n) :
    Invariant (broadcast C s) := by
  let m := nextMessage C s
  let r : Record n := ⟨m,(C.node s).log.toFinset,C.archive.length⟩
  have fresh : ∀ t ∈ C.archive, t.message.id ≠ m.id := by
    intro t ht he; exact h.fresh s ⟨t,ht,he⟩
  have notparent : ∀ t ∈ C.archive, m.id ∉ t.parents := by
    intro t ht hm; exact h.fresh s (h.parent_issued ht hm)
  have own : (fun k => ((broadcast C s).node k).delivered k) =
      tick s (fun k => (C.node k).delivered k) := by
    funext k
    by_cases hk : k = s <;> simp [broadcast,NodeState.accept,nextMessage,tick,hk]
  have logs (p : NodeId n) : ((broadcast C s).node p).log =
      if p = s then (C.node s).log ++ [m.id] else (C.node p).log := by
    by_cases hp : p = s <;> simp [broadcast,NodeState.accept,hp,m]
  have old_ordered : ∀ p t, t ∈ C.archive →
      t.message.id ∈ ((broadcast C s).node p).log →
      ∀ a ∈ t.parents, OccursBefore a t.message.id ((broadcast C s).node p).log := by
    intro p t ht hm a ha
    by_cases hp : p = s
    · subst p
      rw [logs,if_pos rfl] at hm ⊢
      rcases List.mem_append.mp hm with hm | hm
      · exact before_append (h.ordered s t ht hm a ha) _
      · exact (fresh t ht (List.mem_singleton.mp hm)).elim
    · rw [logs,if_neg hp] at hm ⊢
      exact h.ordered p t ht hm a ha
  have archive : (broadcast C s).archive = C.archive ++ [r] := rfl
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro p a
    by_cases hp : p = s
    · subst p
      simpa only [broadcast,Function.update_self] using
        accept_prefix (h.prefix_log s) (m := m) rfl a
    · simpa [broadcast,hp] using h.prefix_log p a
  · intro p
    by_cases hp : p = s
    · subst p
      simpa only [broadcast,Function.update_self] using
        accept_nodup (h.nodup s) (h.fresh_log s s)
    · simpa [broadcast,hp] using h.nodup p
  · intro p k
    change _ ≤ (fun k => ((broadcast C s).node k).delivered k) k
    rw [own]
    by_cases hp : p = s
    · subst p
      simp only [broadcast,Function.update_self,NodeState.accept,nextMessage]
      by_cases hk : k = s
      · subst k; simp
      · simpa [tick,hk] using h.bounded s k
    · simp only [broadcast,Function.update_of_ne hp]
      exact le_trans (h.bounded p k) (le_tick s (fun k => (C.node k).delivered k) k)
  · intro a
    rw [archive,own,prefix_tick]
    simp only [List.mem_append,List.mem_singleton,or_and_right,exists_or,exists_eq_left,
      Finset.mem_insert,h.issued]
    change (_ ∨ m.id = a) ↔ a = m.id ∨ _
    tauto
  · intro t ht u hu he
    rw [archive] at ht hu
    rcases List.mem_append.mp ht with ht | ht <;>
      rcases List.mem_append.mp hu with hu | hu
    · exact h.unique t ht u hu he
    · have hu := List.mem_singleton.mp hu; subst u
      exact (fresh t ht he).elim
    · have ht := List.mem_singleton.mp ht; subst t
      exact (fresh u hu he.symm).elim
    · exact (List.mem_singleton.mp ht).trans (List.mem_singleton.mp hu).symm
  · intro p v hv
    have old : v ∈ (C.node p).buffer := by
      by_cases hp : p = s
      · subst p
        simp only [broadcast,Function.update_self,NodeState.accept,Finset.mem_erase] at hv
        exact hv.2
      · simpa [broadcast,hp] using hv
    rcases h.authentic p v old with ⟨t,ht,he⟩
    exact ⟨t,List.mem_append_left _ ht,he⟩
  · intro t ht
    rw [archive] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h.stamp t ht
    · have ht := List.mem_singleton.mp ht; subst t
      simp [r,m,nextMessage]
  · intro t ht
    rw [archive] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h.past t ht
    · have ht := List.mem_singleton.mp ht; subst t
      change insert m.id (C.node s).log.toFinset = prefixIds (tick s (C.node s).delivered)
      rw [prefix_tick]
      congr 1
      ext a
      simpa only [List.mem_toFinset] using h.prefix_log s a
  · intro t ht
    rw [archive] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact h.not_self t ht
    · have ht := List.mem_singleton.mp ht; subst t
      simpa only [r,List.mem_toFinset] using h.fresh_log s s
  · intro t ht u hu hmem
    rw [archive] at ht hu
    rcases List.mem_append.mp ht with ht | ht <;>
      rcases List.mem_append.mp hu with hu | hu
    · exact h.past_closed t ht u hu hmem
    · have hu := List.mem_singleton.mp hu; subst u
      exact (notparent t ht hmem).elim
    · have ht := List.mem_singleton.mp ht; subst t
      have huLog : u.message.id ∈ (C.node s).log := List.mem_toFinset.mp hmem
      intro a ha
      exact List.mem_toFinset.mpr (h.ordered s u hu huLog a ha).1
    · have ht := List.mem_singleton.mp ht; have hu := List.mem_singleton.mp hu
      subst t; subst u
      exact (h.fresh_log s s (List.mem_toFinset.mp hmem)).elim
  · intro t ht u hu hmem
    rw [archive] at ht hu
    rcases List.mem_append.mp ht with ht | ht <;>
      rcases List.mem_append.mp hu with hu | hu
    · exact h.parent_rank t ht u hu hmem
    · have hu := List.mem_singleton.mp hu; subst u
      exact (notparent t ht hmem).elim
    · have ht := List.mem_singleton.mp ht; subst t
      exact h.birth_bound u hu
    · have ht := List.mem_singleton.mp ht; have hu := List.mem_singleton.mp hu
      subst t; subst u
      exact (h.fresh_log s s (List.mem_toFinset.mp hmem)).elim
  · intro t ht
    rw [archive] at ht ⊢
    simp only [List.length_append,List.length_singleton]
    rcases List.mem_append.mp ht with ht | ht
    · exact Nat.lt_succ_of_lt (h.birth_bound t ht)
    · have ht := List.mem_singleton.mp ht; subst t
      exact Nat.lt_succ_self _
  · intro p t ht hm a ha
    rw [archive] at ht
    rcases List.mem_append.mp ht with ht | ht
    · exact old_ordered p t ht hm a ha
    · have ht := List.mem_singleton.mp ht; subst t
      by_cases hp : p = s
      · subst p
        rw [logs,if_pos rfl]
        exact before_new (List.mem_toFinset.mp ha) (h.fresh_log s s)
      · rw [logs,if_neg hp] at hm
        exact (h.fresh_log s p hm).elim

theorem invariant_step {C D : Config n} {a : Action n} (h : Invariant C)
    (hs : Step C a D) : Invariant D := by
  cases hs with
  | idle => exact h
  | broadcast s => exact h.broadcast_preserves s
  | arrive p r hr => exact h.arrive_preserves p r hr
  | deliver p m hm ready =>
    obtain ⟨r,hr,he⟩ := h.authentic p m hm
    subst m
    exact h.deliver_preserves p r hr ready

theorem reachable_invariant {C : Config n} (h : Reachable C) : Invariant C := by
  induction h with
  | initial => exact initial_invariant
  | step _ hs ih => exact invariant_step ih hs


theorem prefix_integrity_invariant {C : Config n} (hc : Reachable C) (p : NodeId n)
    (a : MessageId n) : a ∈ (C.node p).log ↔ 0 < a.seq ∧ a.seq ≤ (C.node p).delivered a.sender := by
  simpa only [mem_prefix] using (reachable_invariant hc).prefix_log p a

theorem no_duplicate_delivery {C : Config n} (hc : Reachable C) (p : NodeId n) :
    (C.node p).log.Nodup := (reachable_invariant hc).nodup p

theorem Invariant.parent_trans {C : Config n} (h : Invariant C)
    {a b c : MessageId n} (hab : Parent C a b) (hbc : Parent C b c) : Parent C a c := by
  rcases hab with ⟨r,hr,rfl,ha⟩
  rcases hbc with ⟨t,ht,hc,hb⟩
  exact ⟨t,ht,hc,h.past_closed t ht r hr hb ha⟩

theorem causal_iff_parent {C : Config n} (hc : Reachable C) {a b : MessageId n} :
    MsgHappensBefore C a b ↔ Parent C a b := by
  constructor
  · intro hab
    induction hab with
    | single he => exact he
    | tail _ he ih => exact (reachable_invariant hc).parent_trans ih he
  · exact Relation.TransGen.single

theorem causal_iff_record_parent {C : Config n} (hc : Reachable C) {r : Record n}
    (hr : r ∈ C.archive) (a : MessageId n) : MsgHappensBefore C a r.message.id ↔ a ∈ r.parents := by
  rw [causal_iff_parent hc]
  constructor
  · rintro ⟨t,ht,he,ha⟩
    have := (reachable_invariant hc).unique t ht r hr he
    subst t
    exact ha
  · exact fun ha => ⟨r,hr,rfl,ha⟩

theorem happens_before_irrefl {C : Config n} (hc : Reachable C) (a : MessageId n) :
    ¬ MsgHappensBefore C a a := by
  intro ha
  rcases (causal_iff_parent hc).1 ha with ⟨r,hr,he,ha⟩
  exact (reachable_invariant hc).not_self r hr (he ▸ ha)

theorem happens_before_trans {C : Config n} {a b c : MessageId n}
    (hab : MsgHappensBefore C a b) (hbc : MsgHappensBefore C b c) : MsgHappensBefore C a c :=
  hab.trans hbc

theorem sender_sequence_causal {C : Config n} (hc : Reachable C) {r : Record n}
    (hr : r ∈ C.archive) (a : MessageId n) (hs : a.sender = r.message.id.sender)
    (hp : 0 < a.seq) (hl : a.seq < r.message.id.seq) : MsgHappensBefore C a r.message.id := by
  rw [causal_iff_record_parent hc hr]
  have h := reachable_invariant hc
  have ha : a ∈ prefixIds r.message.timestamp := by
    apply (mem_prefix _ _).2
    refine ⟨hp,?_⟩
    rw [hs,h.stamp r hr]
    exact Nat.le_of_lt hl
  rw [← h.past r hr,Finset.mem_insert] at ha
  rcases ha with ha | ha
  · exact (Nat.lt_irrefl _ (ha ▸ hl)).elim
  · exact ha

theorem causal_delivery_log_safety {C : Config n} (hc : Reachable C) {a b : MessageId n}
    (hab : MsgHappensBefore C a b) (p : NodeId n) (hb : b ∈ (C.node p).log) :
    OccursBefore a b (C.node p).log := by
  rcases (causal_iff_parent hc).1 hab with ⟨r,hr,he,ha⟩
  subst b
  exact (reachable_invariant hc).ordered p r hr hb a ha

theorem prefix_sender_card (v : VectorClock n) (k : NodeId n) :
    ((prefixIds v).filter fun a => a.sender = k).card = v k := by
  rw [← Finset.card_range (v k)]
  apply Finset.card_bij (fun a _ => a.seq - 1)
  · intro a ha
    simp only [Finset.mem_filter,mem_prefix] at ha
    simp only [Finset.mem_range]
    rw [ha.2] at ha
    omega
  · intro a ha b hb he
    simp only [Finset.mem_filter,mem_prefix] at ha hb
    apply MessageId.ext (ha.2.trans hb.2.symm)
    omega
  · intro j hj
    simp only [Finset.mem_range] at hj
    refine ⟨⟨k,j + 1⟩,?_,by simp⟩
    simp only [Finset.mem_filter,mem_prefix]
    exact ⟨⟨by omega,by omega⟩,by trivial⟩

/-- Cardinality of the reflexive causal past, including this message itself. -/
theorem timestamp_causal_past_exact {C : Config n} (hc : Reachable C) {r : Record n}
    (hr : r ∈ C.archive) (k : NodeId n) :
    ((insert r.message.id r.parents).filter fun a => a.sender = k).card = r.message.timestamp k ∧
      (∀ a, a ∈ insert r.message.id r.parents ↔ a = r.message.id ∨ MsgHappensBefore C a
        r.message.id) := by
  refine ⟨?_,?_⟩
  · rw [(reachable_invariant hc).past r hr]
    exact prefix_sender_card _ _
  · intro a
    rw [Finset.mem_insert,causal_iff_record_parent hc hr]

theorem ready_merge_bridge (st : NodeState n) (m : Message n) (h : IsReady st m) :
    DistributedVectorClocksCausalOrder.merge st.delivered m.timestamp =
      DistributedVectorClocksCausalOrder.tick m.id.sender st.delivered := by
  funext k
  simp only [DistributedVectorClocksCausalOrder.merge,DistributedVectorClocksCausalOrder.tick]
  by_cases hk : k = m.id.sender
  · subst k
    simp [h.1]
  · simp [hk,Nat.max_eq_left (h.2 k hk)]

theorem tick_bridge (p : NodeId n) (v : VectorClock n) :
    tick p v = DistributedVectorClocksCausalOrder.tick p v := by
  funext k
  by_cases hk : k = p <;> simp [tick,DistributedVectorClocksCausalOrder.tick,hk]


def deliveries (C : Config n) (a : Action n) (p : NodeId n) : List (MessageId n) :=
  match a with
  | .broadcast s => if p = s then [(nextMessage C s).id] else []
  | .deliver q m => if p = q then [m.id] else []
  | _ => []

theorem step_log {C D : Config n} {a : Action n} (hs : Step C a D) (p : NodeId n) :
    (D.node p).log = (C.node p).log ++ deliveries C a p := by
  cases hs with
  | idle => simp [deliveries]
  | broadcast s => by_cases hp : p = s <;> simp [broadcast,NodeState.accept,deliveries,hp]
  | arrive q r _ => by_cases hp : p = q <;> simp [arrive,deliveries,hp]
  | deliver q m _ _ => by_cases hp : p = q <;> simp [deliver,NodeState.accept,deliveries,hp]

theorem deliveries_unique (C : Config n) (a : Action n) (p : NodeId n)
    {x y : MessageId n} (hx : x ∈ deliveries C a p) (hy : y ∈ deliveries C a p) : x = y := by
  cases a <;> simp only [deliveries] at hx hy
  · simp at hx
  · split at hx <;> simp_all
  · simp at hx
  · split at hx <;> simp_all

theorem step_delivery_fresh {C D : Config n} {a : Action n} (hc : Reachable C)
    (hs : Step C a D) (p : NodeId n) {m : MessageId n} (hm : m ∈ deliveries C a p) :
    m ∉ (C.node p).log := by
  have h := reachable_invariant hc
  cases hs with
  | idle => simp [deliveries] at hm
  | arrive => simp [deliveries] at hm
  | broadcast s =>
    simp only [deliveries] at hm
    split at hm
    · rename_i he
      subst p
      have hm := List.mem_singleton.mp hm; subst m
      exact h.fresh_log s s
    · simp at hm
  | deliver q v hv ready =>
    simp only [deliveries] at hm
    split at hm
    · rename_i he
      subst p
      have hm := List.mem_singleton.mp hm; subst m
      obtain ⟨r,hr,he⟩ := h.authentic q v hv
      subst v
      exact h.ready_new hr ready
    · simp at hm

theorem step_archive {C D : Config n} {a : Action n} (hs : Step C a D) :
    ∀ r ∈ C.archive, r ∈ D.archive := by
  cases hs with
  | idle => simp
  | broadcast s => intro r hr; exact List.mem_append_left _ hr
  | arrive => simp [arrive]
  | deliver => simp [deliver]

/-- Infinite executions allow idle steps, so completed finite schedules extend naturally. -/
structure Execution (n : ℕ) where
  state : ℕ → Config n
  action : ℕ → Action n
  start : state 0 = initial n
  step : ∀ t, Step (state t) (action t) (state (t + 1))

def DeliveredAt (E : Execution n) (p : NodeId n) (m : MessageId n) (t : ℕ) : Prop :=
  m ∈ deliveries (E.state t) (E.action t) p

theorem Execution.reachable (E : Execution n) (t : ℕ) : Reachable (E.state t) := by
  induction t with
  | zero => rw [E.start]; exact Reachable.initial
  | succ t ih => exact Reachable.step ih (E.step t)

theorem Execution.log_mono (E : Execution n) (p : NodeId n) {t u : ℕ} (htu : t ≤ u)
    {m : MessageId n} (hm : m ∈ ((E.state t).node p).log) : m ∈ ((E.state u).node p).log := by
  induction u,htu using Nat.le_induction with
  | base => exact hm
  | succ u _ ih => rw [step_log (E.step u)]; exact List.mem_append_left _ ih

theorem Execution.archive_mono (E : Execution n) {t u : ℕ} (htu : t ≤ u)
    {r : Record n} (hr : r ∈ (E.state t).archive) : r ∈ (E.state u).archive := by
  induction u,htu using Nat.le_induction with
  | base => exact hr
  | succ u _ ih => exact step_archive (E.step u) r ih

theorem log_iff_delivered_before (E : Execution n) (p : NodeId n) (m : MessageId n) (t : ℕ) :
    m ∈ ((E.state t).node p).log ↔ ∃ u < t, DeliveredAt E p m u := by
  induction t with
  | zero => simp [E.start,initial]
  | succ t ih =>
    rw [step_log (E.step t),List.mem_append,ih]
    change ((∃ u < t, DeliveredAt E p m u) ∨ DeliveredAt E p m t) ↔ _
    constructor
    · rintro (⟨u,hu,hm⟩ | hm)
      · exact ⟨u,by omega,hm⟩
      · exact ⟨t,by omega,hm⟩
    · rintro ⟨u,hu,hm⟩
      by_cases he : u = t
      · subst u; exact Or.inr hm
      · exact Or.inl ⟨u,by omega,hm⟩

/-- Global step-index form, including the atomic self-delivery on Broadcast. -/
theorem causal_delivery_safety (E : Execution n) (p : NodeId n) (a b : MessageId n) (t : ℕ)
    (hab : MsgHappensBefore (E.state (t + 1)) a b) (hb : DeliveredAt E p b t) :
    ∃ u < t, DeliveredAt E p a u := by
  have hbLog : b ∈ ((E.state (t + 1)).node p).log := by
    rw [step_log (E.step t)]; exact List.mem_append_right _ hb
  have h := causal_delivery_log_safety (E.reachable (t + 1)) hab p hbLog
  have hne : a ≠ b := by intro he; subst a; exact Nat.lt_irrefl _ h.2.2
  have ha := h.1
  rw [step_log (E.step t),List.mem_append] at ha
  rcases ha with ha | ha
  · exact (log_iff_delivered_before E p a t).1 ha
  · exact (hne (deliveries_unique _ _ _ ha hb)).elim

theorem no_duplicate_delivery_steps (E : Execution n) (p : NodeId n) (m : MessageId n)
    {t u : ℕ} (ht : DeliveredAt E p m t) (hu : DeliveredAt E p m u) : t = u := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact step_delivery_fresh (E.reachable u) (E.step u) p hu
      ((log_iff_delivered_before E p m u).2 ⟨t,hlt,ht⟩)
  · exact step_delivery_fresh (E.reachable t) (E.step t) p ht
      ((log_iff_delivered_before E p m t).2 ⟨u,hgt,hu⟩)

theorem observed_delivery_causes_broadcast (C : Config n) (s : NodeId n)
    (a : MessageId n) (ha : a ∈ (C.node s).log) :
    MsgHappensBefore (broadcast C s) a (nextMessage C s).id := by
  apply Relation.TransGen.single
  exact ⟨⟨nextMessage C s,(C.node s).log.toFinset,C.archive.length⟩,
    List.mem_append_right _ (by simp),rfl,List.mem_toFinset.mpr ha⟩


theorem Invariant.ready_of_parents {C : Config n} (h : Invariant C) {r : Record n}
    (hr : r ∈ C.archive) (p : NodeId n) (hn : r.message.id ∉ (C.node p).log)
    (hp : ∀ a ∈ r.parents, a ∈ (C.node p).log) : IsReady (C.node p) r.message := by
  have bound : ∀ a, a ∈ prefixIds r.message.timestamp → a ≠ r.message.id →
      a.seq ≤ (C.node p).delivered a.sender := by
    intro a ha hne
    rw [← h.past r hr,Finset.mem_insert] at ha
    have hm : a ∈ r.parents := ha.resolve_left hne
    exact ((mem_prefix _ _).1 ((h.prefix_log p a).1 (hp a hm))).2
  have positive : 0 < r.message.id.seq :=
    ((mem_prefix _ _).1 ((h.issued _).1 ⟨r,hr,rfl⟩)).1
  have greater : (C.node p).delivered r.message.id.sender < r.message.id.seq := by
    by_contra hh
    exact hn ((h.prefix_log _ _).2 ((mem_prefix _ _).2 ⟨positive,by omega⟩))
  constructor
  · rw [h.stamp r hr]
    by_cases hs : r.message.id.seq = 1
    · omega
    · have hb := bound ⟨r.message.id.sender,r.message.id.seq - 1⟩
        ((mem_prefix _ _).2 ⟨by dsimp; omega,by dsimp; rw [h.stamp r hr]; omega⟩)
        (by intro he; have he' := congrArg MessageId.seq he; simp only at he'; omega)
      simp only at hb
      omega
  · intro k hk
    by_cases hz : r.message.timestamp k = 0
    · simp [hz]
    · exact bound ⟨k,r.message.timestamp k⟩
        ((mem_prefix _ _).2 ⟨by dsimp; omega,le_rfl⟩)
        (by intro he; exact hk (congrArg MessageId.sender he))

theorem step_buffer_persist {C D : Config n} {a : Action n} (hs : Step C a D)
    (p : NodeId n) (m : Message n) (hm : m ∈ (C.node p).buffer)
    (hn : m.id ∉ (D.node p).log) : m ∈ (D.node p).buffer := by
  have no_event : m.id ∉ deliveries C a p := by
    intro he
    exact hn (by rw [step_log hs]; exact List.mem_append_right _ he)
  cases hs with
  | idle => exact hm
  | arrive q r _ =>
    by_cases hp : p = q
    · subst p; simp [arrive,hm]
    · simpa [arrive,hp] using hm
  | broadcast s =>
    by_cases hp : p = s
    · subst p
      have hne : m ≠ nextMessage C s := by
        intro he
        subst m
        simp [deliveries] at no_event
      simpa [broadcast,NodeState.accept,hne] using hm
    · simpa [broadcast,hp] using hm
  | deliver q v _ _ =>
    by_cases hp : p = q
    · subst p
      have hne : m ≠ v := by
        intro he
        subst m
        simp [deliveries] at no_event
      simpa [deliver,NodeState.accept,hne] using hm
    · simpa [deliver,hp] using hm

theorem Execution.buffer_persist (E : Execution n) (p : NodeId n) (m : Message n)
    {t u : ℕ} (htu : t ≤ u) (hm : m ∈ ((E.state t).node p).buffer)
    (hn : ∀ v, m.id ∉ ((E.state v).node p).log) : m ∈ ((E.state u).node p).buffer := by
  induction u,htu using Nat.le_induction with
  | base => exact hm
  | succ u _ ih => exact step_buffer_persist (E.step u) p m ih (hn (u + 1))

/-- An authentic sent message eventually arrives, unless already application-delivered.
This includes the immediate self-delivery and permits duplicated network arrivals. -/
def ReliableArrival (E : Execution n) : Prop :=
  ∀ t r, r ∈ (E.state t).archive → ∀ p,
    ∃ u, t ≤ u ∧ (r.message ∈ ((E.state u).node p).buffer ∨ r.message.id ∈ ((E.state u).node p).log)

/-- Per-message weak fairness, not merely fairness of scheduling each process. -/
def WeakFairness (E : Execution n) : Prop :=
  ∀ p m t, (∀ u, t ≤ u → m ∈ ((E.state u).node p).buffer ∧ IsReady ((E.state u).node p) m) →
    ∃ u, t ≤ u ∧ DeliveredAt E p m.id u

def EventualDelivery (E : Execution n) : Prop :=
  ∀ t r, r ∈ (E.state t).archive → ∀ p, ∃ u, DeliveredAt E p r.message.id u

theorem finite_delivery_bound (E : Execution n) (p : NodeId n) (S : Finset (MessageId n))
    (hs : ∀ a ∈ S, ∃ t, a ∈ ((E.state t).node p).log) :
    ∃ t, ∀ a ∈ S, a ∈ ((E.state t).node p).log := by
  induction S using Finset.induction_on with
  | empty => exact ⟨0,by simp⟩
  | @insert a S ha ih =>
    obtain ⟨t,ht⟩ := hs a (by simp)
    obtain ⟨u,hu⟩ := ih (by intro b hb; exact hs b (Finset.mem_insert_of_mem hb))
    refine ⟨max t u,?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact E.log_mono p (Nat.le_max_left _ _) ht
    · exact E.log_mono p (Nat.le_max_right _ _) (hu b hb)

theorem parent_card_lt {C : Config n} (hc : Reachable C) {r q : Record n}
    (hr : r ∈ C.archive) (hq : q ∈ C.archive) (hp : q.message.id ∈ r.parents) :
    q.parents.card < r.parents.card := by
  have h := reachable_invariant hc
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨h.past_closed r hr q hq hp,?_⟩
  intro he
  exact h.not_self q hq (he.symm ▸ hp)

/-- Strong induction on the finite strict causal past; future broadcasts need not stop. -/
theorem liveness_under_fairness (E : Execution n) (reliable : ReliableArrival E)
    (fair : WeakFairness E) : EventualDelivery E := by
  have eventual : ∀ c, ∀ r : Record n, r.parents.card = c →
      (∃ t, r ∈ (E.state t).archive) → ∀ p, ∃ u, r.message.id ∈ ((E.state u).node p).log := by
    intro c
    induction c using Nat.strong_induction_on with
    | h c ih =>
      intro r hcard issued p
      obtain ⟨t,hr⟩ := issued
      have inv := reachable_invariant (E.reachable t)
      have preds : ∀ a ∈ r.parents, ∃ v, a ∈ ((E.state v).node p).log := by
        intro a ha
        obtain ⟨q,hq,he⟩ := inv.parent_issued hr ha
        have lt := parent_card_lt (E.reachable t) hr hq (he.symm ▸ ha)
        obtain ⟨v,hv⟩ := ih q.parents.card (by omega) q rfl ⟨t,hq⟩ p
        exact ⟨v,he ▸ hv⟩
      obtain ⟨b,hb⟩ := finite_delivery_bound E p r.parents preds
      by_contra never
      push Not at never
      obtain ⟨a,hta,arr⟩ := reliable t r hr p
      have buffered : r.message ∈ ((E.state a).node p).buffer := arr.resolve_right (never a)
      let start := max a b
      have enabled : ∀ u, start ≤ u → r.message ∈ ((E.state u).node p).buffer ∧
          IsReady ((E.state u).node p) r.message := by
        intro u hu
        have hau : a ≤ u := le_trans (Nat.le_max_left _ _) hu
        have hbu : b ≤ u := le_trans (Nat.le_max_right _ _) hu
        refine ⟨E.buffer_persist p r.message hau buffered never,?_⟩
        apply (reachable_invariant (E.reachable u)).ready_of_parents
          (E.archive_mono (le_trans hta hau) hr) p (never u)
        intro x hx
        exact E.log_mono p hbu (hb x hx)
      obtain ⟨u,_,hu⟩ := fair p r.message start enabled
      exact never (u + 1) ((log_iff_delivered_before E p r.message.id (u + 1)).2 ⟨u,by omega,hu⟩)
  intro t r hr p
  obtain ⟨u,hu⟩ := eventual r.parents.card r rfl ⟨t,hr⟩ p
  obtain ⟨v,_,hv⟩ := (log_iff_delivered_before E p r.message.id u).1 hu
  exact ⟨v,hv⟩


theorem causal_reflect_of_issued {C D : Config n} (hc : Reachable C) (hd : Reachable D)
    (ext : ∀ r ∈ C.archive, r ∈ D.archive) {a b : MessageId n}
    (hb : ∃ r ∈ C.archive, r.message.id = b) (hab : MsgHappensBefore D a b) :
    MsgHappensBefore C a b := by
  obtain ⟨r,hr,rfl⟩ := hb
  rw [causal_iff_record_parent hc hr]
  exact (causal_iff_record_parent hd (ext r hr) a).1 hab

/-- Later broadcasts cannot retrospectively change the causal past of an issued message. -/
theorem causal_delivery_safety_extended (E : Execution n) (p : NodeId n)
    (a b : MessageId n) (t v : ℕ) (htv : t + 1 ≤ v)
    (hab : MsgHappensBefore (E.state v) a b) (hb : DeliveredAt E p b t) :
    ∃ u < t, DeliveredAt E p a u := by
  apply causal_delivery_safety E p a b t _ hb
  apply causal_reflect_of_issued (E.reachable (t + 1)) (E.reachable v)
    (fun _ hr => E.archive_mono htv hr) _ hab
  apply (reachable_invariant (E.reachable (t + 1))).log_issued (p := p)
  exact (log_iff_delivered_before E p b (t + 1)).2 ⟨t,by omega,hb⟩

/-- Executable schedules, used to check complete finite operational witnesses. -/
def perform (C : Config n) : Action n → Config n
  | .idle => C
  | .broadcast s => broadcast C s
  | .arrive p m => arrive C p m
  | .deliver p m => deliver C p m

def Enabled (C : Config n) : Action n → Prop
  | .idle => True
  | .broadcast _ => True
  | .arrive _ m => m ∈ C.archive.map Record.message
  | .deliver p m => m ∈ (C.node p).buffer ∧ IsReady (C.node p) m

instance (C : Config n) (a : Action n) : Decidable (Enabled C a) := by
  cases a <;> unfold Enabled <;> infer_instance

def runSchedule (C : Config n) : List (Action n) → Config n
  | [] => C
  | a :: rest => runSchedule (perform C a) rest

def LegalSchedule (C : Config n) : List (Action n) → Prop
  | [] => True
  | a :: rest => Enabled C a ∧ LegalSchedule (perform C a) rest

instance (C : Config n) (as : List (Action n)) : Decidable (LegalSchedule C as) := by
  induction as generalizing C with
  | nil => exact isTrue trivial
  | cons a as ih => exact instDecidableAnd

theorem enabled_step (C : Config n) (a : Action n) (ha : Enabled C a) : Step C a (perform C a) := by
  cases a with
  | idle => exact Step.idle C
  | broadcast s => exact Step.broadcast C s
  | arrive p m =>
    obtain ⟨r,hr,he⟩ := List.mem_map.mp ha
    subst m
    exact Step.arrive C p r hr
  | deliver p m => exact Step.deliver C p m ha.1 ha.2

theorem schedule_reachable {C : Config n} (hc : Reachable C) (as : List (Action n))
    (ha : LegalSchedule C as) : Reachable (runSchedule C as) := by
  induction as generalizing C with
  | nil => exact hc
  | cons a as ih => exact ih (Reachable.step hc (enabled_step C a ha.1)) ha.2

namespace Regression

def first : Message 3 := ⟨⟨0,1⟩,![1,0,0]⟩
def second : Message 3 := ⟨⟨0,2⟩,![2,0,0]⟩
def relay : Message 3 := ⟨⟨1,1⟩,![1,1,0]⟩
def independent : Message 3 := ⟨⟨1,1⟩,![0,1,0]⟩

def reorderedPrefix : List (Action 3) := [.broadcast 0,.broadcast 0,.arrive 1 second]
def reordered : Config 3 := runSchedule (initial 3) reorderedPrefix

theorem reordered_legal : LegalSchedule (initial 3) reorderedPrefix := by decide +kernel

theorem out_of_order_buffering : second ∈ (reordered.node 1).buffer ∧
    ¬ IsReady (reordered.node 1) second ∧ (reordered.node 1).log = [] := by decide +kernel

def reorderFinish : List (Action 3) := [.arrive 1 first,.deliver 1 first,.deliver 1 second]

theorem out_of_order_completion : LegalSchedule reordered reorderFinish ∧
    ((runSchedule reordered reorderFinish).node 1).log = [first.id,second.id] := by decide +kernel

def causalPrefix : List (Action 3) :=
  [.broadcast 0,.arrive 1 first,.deliver 1 first,.broadcast 1,.arrive 2 relay]
def causalBlocked : Config 3 := runSchedule (initial 3) causalPrefix

theorem causal_prefix_legal : LegalSchedule (initial 3) causalPrefix := by decide +kernel

theorem causal_prefix_reachable : Reachable causalBlocked :=
  schedule_reachable Reachable.initial _ causal_prefix_legal

theorem relay_has_dependency : MsgHappensBefore causalBlocked first.id relay.id := by
  apply Relation.TransGen.single
  exact ⟨⟨relay,{first.id},1⟩,by decide +kernel,rfl,by decide +kernel⟩

def chainFinish : List (Action 3) := [.arrive 2 first,.deliver 2 first,.deliver 2 relay]

theorem three_process_chain : ¬ IsReady (causalBlocked.node 2) relay ∧
    LegalSchedule causalBlocked chainFinish ∧
    ((runSchedule causalBlocked chainFinish).node 2).log = [first.id,relay.id] := by decide +kernel

def parallelSchedule : List (Action 3) := [.broadcast 0,.broadcast 1,
  .arrive 0 independent,.deliver 0 independent,.arrive 1 first,.deliver 1 first]
def parallel : Config 3 := runSchedule (initial 3) parallelSchedule

theorem parallel_different_orders : LegalSchedule (initial 3) parallelSchedule ∧
    (parallel.node 0).log = [first.id,independent.id] ∧
    (parallel.node 1).log = [independent.id,first.id] := by decide +kernel

theorem parallel_causally_unrelated : ¬ MsgHappensBefore parallel first.id independent.id ∧
    ¬ MsgHappensBefore parallel independent.id first.id := by
  have hc : Reachable parallel := schedule_reachable Reachable.initial _ parallel_different_orders.1
  have ha : (⟨first,∅,0⟩ : Record 3) ∈ parallel.archive := by decide +kernel
  have hb : (⟨independent,∅,1⟩ : Record 3) ∈ parallel.archive := by decide +kernel
  constructor
  · rw [causal_iff_record_parent hc hb]; simp
  · rw [causal_iff_record_parent hc ha]; simp

theorem immediate_self_delivery :
    ((broadcast (initial 3) 0).node 0).log = [first.id] ∧
    ((broadcast (initial 3) 0).node 0).buffer = ∅ := by decide +kernel

theorem single_process : LegalSchedule (initial 1) [.broadcast 0,.broadcast 0] ∧
    ((runSchedule (initial 1) [.broadcast 0,.broadcast 0]).node 0).log = [⟨0,1⟩,⟨0,2⟩] := by
      decide +kernel

def duplicateSchedule : List (Action 3) := [.broadcast 0,.arrive 1 first,.arrive 1 first,
  .deliver 1 first,.arrive 1 first]

theorem duplicate_arrival_no_redelivery : LegalSchedule (initial 3) duplicateSchedule ∧
    let C := runSchedule (initial 3) duplicateSchedule
    (C.node 1).log = [first.id] ∧ first ∈ (C.node 1).buffer ∧ ¬ IsReady (C.node 1) first := by
      decide +kernel

end Regression

/-- Removing cross-sender checks admits a causally premature delivery from a reachable state. -/
theorem counterexample_missing_cross_check :
    Reachable Regression.causalBlocked ∧
    MsgHappensBefore Regression.causalBlocked Regression.first.id Regression.relay.id ∧
    Regression.relay ∈ (Regression.causalBlocked.node 2).buffer ∧
    Regression.relay.timestamp Regression.relay.id.sender =
      (Regression.causalBlocked.node 2).delivered Regression.relay.id.sender + 1 ∧
    ¬ IsReady (Regression.causalBlocked.node 2) Regression.relay ∧
    Regression.relay.id ∈ ((deliver Regression.causalBlocked 2 Regression.relay).node 2).log ∧
    Regression.first.id ∉ ((deliver Regression.causalBlocked 2 Regression.relay).node 2).log := by
  refine ⟨Regression.causal_prefix_reachable,Regression.relay_has_dependency,?_⟩
  decide +kernel

/-- Permitting a sender sequence gap violates both FIFO prefix integrity and causality. -/
theorem counterexample_skip_sequence :
    Reachable Regression.reordered ∧
    MsgHappensBefore Regression.reordered Regression.first.id Regression.second.id ∧
    Regression.second ∈ (Regression.reordered.node 1).buffer ∧
    Regression.second.timestamp Regression.second.id.sender >
      (Regression.reordered.node 1).delivered Regression.second.id.sender + 1 ∧
    (∀ k, k ≠ Regression.second.id.sender →
      Regression.second.timestamp k ≤ (Regression.reordered.node 1).delivered k) ∧
    Regression.second.id ∈ ((deliver Regression.reordered 1 Regression.second).node 1).log ∧
    Regression.first.id ∉ ((deliver Regression.reordered 1 Regression.second).node 1).log := by
  have hc : Reachable Regression.reordered :=
    schedule_reachable Reachable.initial _ Regression.reordered_legal
  refine ⟨hc,?_,by decide +kernel⟩
  exact sender_sequence_causal hc
    (r := ⟨Regression.second,{Regression.first.id},1⟩) (by decide +kernel)
    Regression.first.id (by decide +kernel) (by decide +kernel) (by decide +kernel)


def broadcastRecord (C : Config n) (s : NodeId n) : Record n :=
  ⟨nextMessage C s,(C.node s).log.toFinset,C.archive.length⟩

def BroadcastAt (E : Execution n) (r : Record n) (t : ℕ) : Prop :=
  ∃ s, E.action t = .broadcast s ∧ r = broadcastRecord (E.state t) s

theorem step_archive_exact {C D : Config n} {a : Action n} (hs : Step C a D) (r : Record n) :
    r ∈ D.archive ↔ r ∈ C.archive ∨ ∃ s, a = .broadcast s ∧ r = broadcastRecord C s := by
  cases hs <;> simp [broadcast,arrive,deliver,broadcastRecord]

theorem archive_iff_broadcast_before (E : Execution n) (r : Record n) (t : ℕ) :
    r ∈ (E.state t).archive ↔ ∃ u < t, BroadcastAt E r u := by
  induction t with
  | zero => simp [E.start,initial]
  | succ t ih =>
    rw [step_archive_exact (E.step t),ih]
    change ((∃ u < t, BroadcastAt E r u) ∨ BroadcastAt E r t) ↔ _
    constructor
    · rintro (⟨u,hu,hm⟩ | hm)
      · exact ⟨u,by omega,hm⟩
      · exact ⟨t,by omega,hm⟩
    · rintro ⟨u,hu,hm⟩
      by_cases he : u = t
      · subst u; exact Or.inr hm
      · exact Or.inl ⟨u,by omega,hm⟩

/-- Ghost parent edges coincide with actual delivery-before-broadcast event edges. -/
theorem parent_event_trace_bridge (E : Execution n) (a b : MessageId n) (t : ℕ) :
    Parent (E.state t) a b ↔ ∃ u < t, ∃ s, E.action u = .broadcast s ∧
      b = (nextMessage (E.state u) s).id ∧ ∃ v < u, DeliveredAt E s a v := by
  constructor
  · rintro ⟨r,hr,hb,ha⟩
    obtain ⟨u,hu,s,hs,rfl⟩ := (archive_iff_broadcast_before E r t).1 hr
    exact ⟨u,hu,s,hs,hb.symm,(log_iff_delivered_before E s a u).1 (List.mem_toFinset.mp ha)⟩
  · rintro ⟨u,hu,s,hs,rfl,ha⟩
    exact ⟨broadcastRecord (E.state u) s,
      (archive_iff_broadcast_before E _ t).2 ⟨u,hu,s,hs,rfl⟩,rfl,
      List.mem_toFinset.mpr ((log_iff_delivered_before E s a u).2 ha)⟩

structure DistributedCausalBroadcastSuite : Prop where
  prefix_integrity : ∀ n (C : Config n), Reachable C → ∀ p a,
    a ∈ (C.node p).log ↔ 0 < a.seq ∧ a.seq ≤ (C.node p).delivered a.sender
  no_duplicates : ∀ n (C : Config n), Reachable C → ∀ p, (C.node p).log.Nodup
  exact_past : ∀ n (C : Config n), Reachable C → ∀ r ∈ C.archive, ∀ k,
    ((insert r.message.id r.parents).filter fun a => a.sender = k).card = r.message.timestamp k ∧
      (∀ a, a ∈ insert r.message.id r.parents ↔ a = r.message.id ∨ MsgHappensBefore C a
        r.message.id)
  causal_safety : ∀ n (E : Execution n) p a b t,
    MsgHappensBefore (E.state (t + 1)) a b → DeliveredAt E p b t →
      ∃ u < t, DeliveredAt E p a u
  no_repeat_steps : ∀ n (E : Execution n) p m t u,
    DeliveredAt E p m t → DeliveredAt E p m u → t = u
  conditional_liveness : ∀ n (E : Execution n), ReliableArrival E → WeakFairness E →
    EventualDelivery E
  trace_bridge : ∀ n (E : Execution n) a b t,
    Parent (E.state t) a b ↔ ∃ u < t, ∃ s, E.action u = .broadcast s ∧
      b = (nextMessage (E.state u) s).id ∧ ∃ v < u, DeliveredAt E s a v
  clock_bridge : ∀ n (st : NodeState n) (m : Message n), IsReady st m →
    DistributedVectorClocksCausalOrder.merge st.delivered m.timestamp =
      DistributedVectorClocksCausalOrder.tick m.id.sender st.delivered
  reordered : LegalSchedule (initial 3) Regression.reorderedPrefix ∧
    ¬ IsReady (Regression.reordered.node 1) Regression.second
  parallel_orders : (Regression.parallel.node 0).log =
    [Regression.first.id,Regression.independent.id] ∧
    (Regression.parallel.node 1).log = [Regression.independent.id,Regression.first.id]
  missing_cross_check : Regression.relay.id ∈ ((deliver Regression.causalBlocked 2
    Regression.relay).node 2).log ∧
    Regression.first.id ∉ ((deliver Regression.causalBlocked 2 Regression.relay).node 2).log
  skipped_sequence : Regression.second.id ∈ ((deliver Regression.reordered 1
    Regression.second).node 1).log ∧
    Regression.first.id ∉ ((deliver Regression.reordered 1 Regression.second).node 1).log

theorem distributed_causal_broadcast_master_suite : DistributedCausalBroadcastSuite where
  prefix_integrity := fun _ _ hc => prefix_integrity_invariant hc
  no_duplicates := fun _ _ hc => no_duplicate_delivery hc
  exact_past := fun _ _ hc _ hr => timestamp_causal_past_exact hc hr
  causal_safety := fun _ => causal_delivery_safety
  no_repeat_steps := fun _ E p m _ _ => no_duplicate_delivery_steps E p m
  conditional_liveness := fun _ => liveness_under_fairness
  trace_bridge := fun _ => parent_event_trace_bridge
  clock_bridge := fun _ => ready_merge_bridge
  reordered := ⟨Regression.reordered_legal,Regression.out_of_order_buffering.2.1⟩
  parallel_orders := Regression.parallel_different_orders.2
  missing_cross_check := counterexample_missing_cross_check.2.2.2.2.2
  skipped_sequence := counterexample_skip_sequence.2.2.2.2.2

end DistributedCausalBroadcast
