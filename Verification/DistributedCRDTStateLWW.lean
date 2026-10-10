/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedCausalBroadcast
import Mathlib.Data.Prod.Lex
import Mathlib.Order.WithBot

/-! Fixed-group state-based LWW registers. Histories and the sent archive are ghost
observations; operational merge reads only the transmitted register. -/
namespace DistributedCRDTStateLWW

abbrev ReplicaId (n : ℕ) := Fin n

@[ext] structure Stamp (n : ℕ) where
  counter : ℕ
  node : ReplicaId n
  deriving DecidableEq, Repr

def Stamp.key (s : Stamp n) : ℕ ×ₗ Fin n := toLex (s.counter, s.node)

instance : LinearOrder (Stamp n) := LinearOrder.lift' Stamp.key (by
  intro a b h
  have h' : (a.counter, a.node) = (b.counter, b.node) := h
  exact Stamp.ext (congrArg Prod.fst h') (congrArg Prod.snd h'))

theorem stamp_le_iff (a b : Stamp n) :
    a ≤ b ↔ a.counter < b.counter ∨ (a.counter = b.counter ∧ a.node ≤ b.node) :=
  Prod.Lex.toLex_le_toLex

theorem counter_mono {a b : Stamp n} (h : a ≤ b) : a.counter ≤ b.counter := by
  rcases (stamp_le_iff a b).1 h with h | ⟨h, _⟩ <;> omega

abbrev Entry (α : Type*) (n : ℕ) := Stamp n × α
abbrev LWWReg (α : Type*) (n : ℕ) := Option (Entry α n)

def rank : LWWReg α n → WithBot (Stamp n)
  | none => ⊥
  | some a => a.1

def counter : LWWReg α n → ℕ
  | none => 0
  | some a => a.1.counter

def merge : LWWReg α n → LWWReg α n → LWWReg α n
  | none, r => r
  | r, none => r
  | some a, some b => if a.1 ≤ b.1 then some b else some a

def RegLE (r s : LWWReg α n) : Prop := rank r ≤ rank s

instance (r s : LWWReg α n) : Decidable (RegLE r s) :=
  inferInstanceAs (Decidable (rank r ≤ rank s))

def RegIn (r : LWWReg α n) (H : List (Entry α n)) : Prop :=
  ∀ a, r = some a → a ∈ H

def Unique (H : List (Entry α n)) : Prop :=
  ∀ a ∈ H, ∀ b ∈ H, a.1 = b.1 → a = b

def IsMax (r : LWWReg α n) (H : List (Entry α n)) : Prop :=
  RegIn r H ∧ ∀ a ∈ H, RegLE (some a) r

@[simp] theorem merge_none (r : LWWReg α n) : merge r none = r := by cases r <;> rfl
@[simp] theorem none_merge (r : LWWReg α n) : merge none r = r := rfl

theorem merge_choice (r s : LWWReg α n) : merge r s = r ∨ merge r s = s := by
  cases r with
  | none => exact Or.inr rfl
  | some a =>
    cases s with
    | none => exact Or.inl rfl
    | some b => by_cases h : a.1 ≤ b.1 <;> simp [merge, h]

theorem rank_merge (r s : LWWReg α n) : rank (merge r s) = max (rank r) (rank s) := by
  cases r with
  | none => simp [merge, rank]
  | some a =>
    cases s with
    | none => simp [merge, rank]
    | some b =>
      by_cases h : a.1 ≤ b.1
      · simp [merge, h, rank]
      · simp [merge, h, rank, max_eq_left (WithBot.coe_le_coe.mpr (le_of_not_ge h))]

theorem merge_inflationary (r s : LWWReg α n) : RegLE r (merge r s) ∧ RegLE s (merge r s) := by
  simp only [RegLE, rank_merge]
  exact ⟨le_max_left _ _, le_max_right _ _⟩

theorem merge_lub {r s t : LWWReg α n} (hr : RegLE r t) (hs : RegLE s t) :
    RegLE (merge r s) t := by simpa only [RegLE, rank_merge] using max_le hr hs

theorem reg_le_counter {r s : LWWReg α n} (h : RegLE r s) : counter r ≤ counter s := by
  cases r with
  | none => exact Nat.zero_le _
  | some a =>
    cases s with
    | none => simp [RegLE, rank] at h
    | some b => exact counter_mono (WithBot.coe_le_coe.mp h)

theorem regIn_mono {r : LWWReg α n} {H K : List (Entry α n)}
    (hr : RegIn r H) (hk : ∀ a ∈ H, a ∈ K) : RegIn r K := fun a ha => hk a (hr a ha)

theorem regIn_merge {r s : LWWReg α n} {H : List (Entry α n)}
    (hr : RegIn r H) (hs : RegIn s H) : RegIn (merge r s) H := by
  rcases merge_choice r s with h | h <;> rw [h] <;> assumption

theorem compatible_antisymm {H : List (Entry α n)} (hu : Unique H)
    {r s : LWWReg α n} (hr : RegIn r H) (hs : RegIn s H)
    (hrs : RegLE r s) (hsr : RegLE s r) : r = s := by
  have he := le_antisymm hrs hsr
  cases r with
  | none => cases s <;> simp_all [rank]
  | some a =>
    cases s with
    | none => simp [rank] at he
    | some b =>
      have hab : a.1 = b.1 := WithBot.coe_inj.mp he
      exact congrArg some (hu a (hr a rfl) b (hs b rfl) hab)

theorem merge_comm {H : List (Entry α n)} (hu : Unique H)
    {r s : LWWReg α n} (hr : RegIn r H) (hs : RegIn s H) : merge r s = merge s r := by
  apply compatible_antisymm hu (regIn_merge hr hs) (regIn_merge hs hr)
  all_goals simp [RegLE, rank_merge, max_comm]

theorem merge_assoc {H : List (Entry α n)} (hu : Unique H)
    {r s t : LWWReg α n} (hr : RegIn r H) (hs : RegIn s H) (ht : RegIn t H) :
    merge (merge r s) t = merge r (merge s t) := by
  apply compatible_antisymm hu (regIn_merge (regIn_merge hr hs) ht)
    (regIn_merge hr (regIn_merge hs ht))
  all_goals simp [RegLE, rank_merge, max_assoc]

theorem merge_idem (r : LWWReg α n) : merge r r = r := by cases r <;> simp [merge]

/-- A genuine partial order and join on states from a common compatible history. -/
abbrev ValidState (H : List (Entry α n)) := {r : LWWReg α n // RegIn r H}

instance (H : List (Entry α n)) [Fact (Unique H)] : PartialOrder (ValidState H) :=
  PartialOrder.lift (fun r => rank r.val) (by
    intro r s h
    apply Subtype.ext
    exact compatible_antisymm Fact.out r.property s.property (le_of_eq h) (le_of_eq h.symm))

instance (H : List (Entry α n)) [Fact (Unique H)] : SemilatticeSup (ValidState H) where
  sup r s := ⟨merge r.val s.val, regIn_merge r.property s.property⟩
  le_sup_left r s := (merge_inflationary r.val s.val).1
  le_sup_right r s := (merge_inflationary r.val s.val).2
  sup_le _ _ _ := fun hr hs => merge_lub hr hs

theorem isMax_empty : IsMax (none : LWWReg α n) [] := by simp [IsMax, RegIn]

theorem isMax_single (a : Entry α n) : IsMax (some a) [a] := by
  simp [IsMax, RegIn, RegLE]

theorem isMax_append {r s : LWWReg α n} {H K : List (Entry α n)}
    (hr : IsMax r H) (hs : IsMax s K) : IsMax (merge r s) (H ++ K) := by
  constructor
  · exact regIn_merge (regIn_mono hr.1 (fun _ h => List.mem_append_left _ h))
      (regIn_mono hs.1 (fun _ h => List.mem_append_right _ h))
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact le_trans (hr.2 a ha) (merge_inflationary r s).1
    · exact le_trans (hs.2 a ha) (merge_inflationary r s).2

def summarize : List (Entry α n) → LWWReg α n
  | [] => none
  | a :: H => merge (some a) (summarize H)

theorem summarize_isMax (H : List (Entry α n)) : IsMax (summarize H) H := by
  induction H with
  | nil => exact isMax_empty
  | cons a H ih => exact isMax_append (isMax_single a) ih

theorem isMax_unique {H K U : List (Entry α n)} (hu : Unique U)
    (hH : ∀ a ∈ H, a ∈ U) (hK : ∀ a ∈ K, a ∈ U)
    {r s : LWWReg α n} (hr : IsMax r H) (hs : IsMax s K)
    (he : ∀ a, a ∈ H ↔ a ∈ K) : r = s := by
  apply compatible_antisymm hu (regIn_mono hr.1 hH) (regIn_mono hs.1 hK)
  · cases r with
    | none => exact bot_le
    | some a => exact hs.2 a ((he a).1 (hr.1 a rfl))
  · cases s with
    | none => exact bot_le
    | some a => exact hr.2 a ((he a).2 (hs.1 a rfl))

theorem history_order_and_duplicates_irrelevant {H K : List (Entry α n)}
    (hu : Unique (H ++ K)) (he : ∀ a, a ∈ H ↔ a ∈ K) : summarize H = summarize K :=
  isMax_unique hu (fun _ h => List.mem_append_left _ h) (fun _ h => List.mem_append_right _ h)
    (summarize_isMax H) (summarize_isMax K) he

structure Snapshot (α : Type*) (n : ℕ) where
  reg : LWWReg α n
  history : List (Entry α n)

structure NodeState (α : Type*) (n : ℕ) extends Snapshot α n where
  clock : ℕ

structure Config (α : Type*) (n : ℕ) where
  node : ReplicaId n → NodeState α n
  issued : List (Entry α n)
  sent : List (Snapshot α n)

def initial (α : Type*) (n : ℕ) : Config α n :=
  ⟨fun _ => ⟨⟨none, []⟩, 0⟩, [], []⟩

def nextEntry (C : Config α n) (p : ReplicaId n) (v : α) : Entry α n :=
  (⟨(C.node p).clock + 1, p⟩, v)

def write (C : Config α n) (p : ReplicaId n) (v : α) : Config α n :=
  { C with
    node := fun q => if q = p then
      ⟨⟨some (nextEntry C p v), (C.node p).history ++ [nextEntry C p v]⟩,
        (C.node p).clock + 1⟩ else C.node q
    issued := C.issued ++ [nextEntry C p v] }

def send (C : Config α n) (p : ReplicaId n) : Config α n :=
  { C with sent := C.sent ++ [(C.node p).toSnapshot] }

/-- Histories are ghost metadata. Only the register affects operational state. -/
def receive (C : Config α n) (p : ReplicaId n) (S : Snapshot α n) : Config α n :=
  { C with node := fun q => if q = p then
      ⟨⟨merge (C.node p).reg S.reg, (C.node p).history ++ S.history⟩,
        max (C.node p).clock (counter S.reg)⟩ else C.node q }

inductive Action (α : Type*) (n : ℕ) where
  | idle
  | write (p : ReplicaId n) (v : α)
  | send (p : ReplicaId n)
  | receive (p : ReplicaId n) (packet : Snapshot α n)

/-- A sent snapshot remains available for delayed and repeated reception. -/
inductive Step : Config α n → Action α n → Config α n → Prop where
  | idle : Step C .idle C
  | write (p v) : Step C (.write p v) (write C p v)
  | send (p) : Step C (.send p) (send C p)
  | receive (p S) (hs : S ∈ C.sent) : Step C (.receive p S) (receive C p S)

inductive Reachable : Config α n → Prop where
  | initial : Reachable (initial α n)
  | step : Reachable C → Step C a D → Reachable D

structure Invariant (C : Config α n) : Prop where
  unique : Unique C.issued
  origin_bound : ∀ a ∈ C.issued, a.1.counter ≤ (C.node a.1.node).clock
  local_max : ∀ p, IsMax (C.node p).reg (C.node p).history
  histories : ∀ p a, a ∈ (C.node p).history → a ∈ C.issued
  clock_bound : ∀ p, counter (C.node p).reg ≤ (C.node p).clock
  packets : ∀ S ∈ C.sent, IsMax S.reg S.history ∧ ∀ a ∈ S.history, a ∈ C.issued
  covered : ∀ a ∈ C.issued, RegLE (some a) (C.node a.1.node).reg

theorem invariant_initial : Invariant (initial α n) := by
  constructor <;> simp [initial, Unique, isMax_empty, counter]

theorem Invariant.next_fresh {C : Config α n} (h : Invariant C) (p : ReplicaId n) (v : α)
    {a : Entry α n} (ha : a ∈ C.issued) : a.1 ≠ (nextEntry C p v).1 := by
  intro he
  have hb := h.origin_bound a ha
  have hn := congrArg Stamp.node he
  have hc := congrArg Stamp.counter he
  simp only [nextEntry] at hn hc
  rw [hn] at hb
  omega

theorem next_above {C : Config α n} (p : ReplicaId n) (v : α)
    (hc : counter (C.node p).reg ≤ (C.node p).clock) :
    RegLE (C.node p).reg (some (nextEntry C p v)) := by
  cases hr : (C.node p).reg with
  | none => exact bot_le
  | some a =>
    simp only [hr, counter] at hc
    exact WithBot.coe_le_coe.mpr ((stamp_le_iff _ _).2 (Or.inl (by dsimp [nextEntry]; omega)))

theorem write_clock_mono (C : Config α n) (p q : ReplicaId n) (v : α) :
    (C.node q).clock ≤ ((write C p v).node q).clock := by
  by_cases he : q = p <;> simp [write, he]

theorem write_reg_mono {C : Config α n} (h : Invariant C) (p q : ReplicaId n) (v : α) :
    RegLE (C.node q).reg ((write C p v).node q).reg := by
  by_cases he : q = p
  · subst q; simpa [write] using next_above p v (h.clock_bound p)
  · simp [write, he, RegLE]

theorem receive_clock_mono (C : Config α n) (p q : ReplicaId n) (S : Snapshot α n) :
    (C.node q).clock ≤ ((receive C p S).node q).clock := by
  by_cases he : q = p <;> simp [receive, he]

theorem receive_reg_mono (C : Config α n) (p q : ReplicaId n) (S : Snapshot α n) :
    RegLE (C.node q).reg ((receive C p S).node q).reg := by
  by_cases he : q = p
  · subst q; simpa [receive] using (merge_inflationary (C.node p).reg S.reg).1
  · simp [receive, he, RegLE]

theorem counter_merge_bound (r s : LWWReg α n) :
    counter (merge r s) ≤ max (counter r) (counter s) := by
  rcases merge_choice r s with h | h <;> rw [h]
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem Invariant.preserve_write {C : Config α n} (h : Invariant C) (p : ReplicaId n) (v : α) :
    Invariant (write C p v) := by
  have hin (a : Entry α n) (ha : a ∈ C.issued) : a ∈ (write C p v).issued :=
    List.mem_append_left _ ha
  have hnew : nextEntry C p v ∈ (write C p v).issued := List.mem_append_right _ (by simp)
  have hmem (a : Entry α n) : a ∈ (write C p v).issued ↔ a ∈ C.issued ∨ a = nextEntry C p v := by
    simp [write]
  constructor
  · intro a ha b hb he
    rcases (hmem a).1 ha with ha | rfl <;> rcases (hmem b).1 hb with hb | rfl
    · exact h.unique a ha b hb he
    · exact (h.next_fresh p v ha he).elim
    · exact (h.next_fresh p v hb he.symm).elim
    · rfl
  · intro a ha
    rcases (hmem a).1 ha with ha | rfl
    · exact le_trans (h.origin_bound a ha) (write_clock_mono C p a.1.node v)
    · simp [write, nextEntry]
  · intro q
    by_cases he : q = p
    · subst q
      simp only [write, ↓reduceIte]
      constructor
      · intro a ha; cases ha; exact List.mem_append_right _ (by simp)
      · intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact le_trans ((h.local_max p).2 a ha) (next_above p v (h.clock_bound p))
        · have he := List.mem_singleton.mp ha; subst a; exact le_rfl
    · simpa [write, he] using h.local_max q
  · intro q a ha
    by_cases he : q = p
    · subst q
      simp only [write, ↓reduceIte, List.mem_append, List.mem_singleton] at ha
      rcases ha with ha | rfl
      · exact hin a (h.histories p a ha)
      · exact hnew
    · exact hin a (h.histories q a (by simpa [write, he] using ha))
  · intro q
    by_cases he : q = p
    · subst q; simp [write, counter, nextEntry]
    · simpa [write, he] using h.clock_bound q
  · intro S hs
    exact ⟨(h.packets S hs).1, fun a ha => hin a ((h.packets S hs).2 a ha)⟩
  · intro a ha
    rcases (hmem a).1 ha with ha | rfl
    · exact le_trans (h.covered a ha) (write_reg_mono h p a.1.node v)
    · simp [write, nextEntry, RegLE]

theorem Invariant.preserve_send {C : Config α n} (h : Invariant C) (p : ReplicaId n) :
    Invariant (send C p) := by
  refine { h with packets := ?_ }
  intro S hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h.packets S hs
  · have he := List.mem_singleton.mp hs; subst S
    exact ⟨h.local_max p, h.histories p⟩

theorem Invariant.preserve_receive {C : Config α n} (h : Invariant C) (p : ReplicaId n)
    (S : Snapshot α n) (hs : S ∈ C.sent) : Invariant (receive C p S) := by
  have hp := h.packets S hs
  constructor
  · exact h.unique
  · intro a ha; exact le_trans (h.origin_bound a ha) (receive_clock_mono C p a.1.node S)
  · intro q
    by_cases he : q = p
    · subst q; simpa [receive] using isMax_append (h.local_max p) hp.1
    · simpa [receive, he] using h.local_max q
  · intro q a ha
    by_cases he : q = p
    · subst q
      simp only [receive, ↓reduceIte, List.mem_append] at ha
      exact ha.elim (h.histories p a) (hp.2 a)
    · exact h.histories q a (by simpa [receive, he] using ha)
  · intro q
    by_cases he : q = p
    · subst q
      simp only [receive, ↓reduceIte]
      exact le_trans (counter_merge_bound _ _) (max_le_max (h.clock_bound p) le_rfl)
    · simpa [receive, he] using h.clock_bound q
  · exact h.packets
  · intro a ha; exact le_trans (h.covered a ha) (receive_reg_mono C p a.1.node S)

theorem reachable_invariant {C : Config α n} (h : Reachable C) : Invariant C := by
  induction h with
  | initial => exact invariant_initial
  | step _ hs ih =>
    cases hs with
    | idle => exact ih
    | write p v => exact ih.preserve_write p v
    | send p => exact ih.preserve_send p
    | receive p S hs => exact ih.preserve_receive p S hs

theorem stamp_uniqueness {C : Config α n} (h : Reachable C)
    {a b : Entry α n} (ha : a ∈ C.issued) (hb : b ∈ C.issued) (he : a.1 = b.1) : a.2 = b.2 :=
  congrArg Prod.snd ((reachable_invariant h).unique a ha b hb he)

theorem payload_is_max_history {C : Config α n} (h : Reachable C) (p : ReplicaId n) :
    IsMax (C.node p).reg (C.node p).history ∧
    (C.node p).reg = summarize (C.node p).history := by
  have hi := reachable_invariant h
  exact ⟨hi.local_max p, isMax_unique hi.unique (hi.histories p) (hi.histories p)
    (hi.local_max p) (summarize_isMax _) (fun _ => Iff.rfl)⟩

theorem sec_strong_convergence {C : Config α n} (h : Reachable C) (p q : ReplicaId n)
    (he : ∀ a, a ∈ (C.node p).history ↔ a ∈ (C.node q).history) :
    (C.node p).reg = (C.node q).reg := by
  have hi := reachable_invariant h
  exact isMax_unique hi.unique (hi.histories p) (hi.histories q)
    (hi.local_max p) (hi.local_max q) he

theorem sec_across_traces {C D : Config α n} (hc : Reachable C) (hd : Reachable D)
    (p q : ReplicaId n)
    (he : ∀ a, a ∈ (C.node p).history ↔ a ∈ (D.node q).history) :
    (C.node p).reg = (D.node q).reg := by
  have hC := reachable_invariant hc
  have hD := reachable_invariant hd
  exact isMax_unique hC.unique (hC.histories p)
    (fun a ha => hC.histories p a ((he a).2 ha)) (hC.local_max p) (hD.local_max q) he

def read (r : LWWReg α n) : Option α := r.map Prod.snd

theorem read_after_write (C : Config α n) (p : ReplicaId n) (v : α) :
    read ((write C p v).node p).reg = some v := by simp [write, read, nextEntry]

theorem fresh_above_observed {C : Config α n} (hc : Reachable C) (p : ReplicaId n) (v : α)
    {a : Entry α n} (ha : a ∈ (C.node p).history) :
    a.1.counter < (nextEntry C p v).1.counter := by
  have hi := reachable_invariant hc
  have h := le_trans (reg_le_counter ((hi.local_max p).2 a ha)) (hi.clock_bound p)
  change a.1.counter ≤ (C.node p).clock at h
  change a.1.counter < (C.node p).clock + 1
  omega

theorem step_issued {C D : Config α n} {a : Action α n} (hs : Step C a D) :
    ∀ w ∈ C.issued, w ∈ D.issued := by
  cases hs with
  | write => exact fun _ h => List.mem_append_left _ h
  | idle => exact fun _ h => h
  | send => exact fun _ h => h
  | receive => exact fun _ h => h

theorem step_sent {C D : Config α n} {a : Action α n} (hs : Step C a D) :
    ∀ S ∈ C.sent, S ∈ D.sent := by
  cases hs with
  | send => exact fun _ h => List.mem_append_left _ h
  | idle => exact fun _ h => h
  | write => exact fun _ h => h
  | receive => exact fun _ h => h

theorem step_reg_mono {C D : Config α n} {a : Action α n}
    (hc : Reachable C) (hs : Step C a D) (p : ReplicaId n) :
    RegLE (C.node p).reg (D.node p).reg := by
  cases hs with
  | idle => exact le_rfl
  | write q v => exact write_reg_mono (reachable_invariant hc) q p v
  | send => exact le_rfl
  | receive q S => exact receive_reg_mono C q p S

theorem received_packet_le {C D : Config α n} {p : ReplicaId n} {S : Snapshot α n}
    (hs : Step C (.receive p S) D) : RegLE S.reg (D.node p).reg := by
  cases hs
  simpa [receive] using (merge_inflationary (C.node p).reg S.reg).2

theorem sent_packet_mem {C D : Config α n} {p : ReplicaId n}
    (hs : Step C (.send p) D) : (C.node p).toSnapshot ∈ D.sent := by
  cases hs
  exact List.mem_append_right _ (by simp)

theorem no_write_issued {C D : Config α n} {a : Action α n} (hs : Step C a D)
    (hn : ∀ p v, a ≠ .write p v) : D.issued = C.issued := by
  cases hs with
  | idle => rfl
  | send => rfl
  | receive => rfl
  | write p v => exact (hn p v rfl).elim

structure Execution (α : Type*) (n : ℕ) where
  state : ℕ → Config α n
  action : ℕ → Action α n
  start : state 0 = initial α n
  step : ∀ t, Step (state t) (action t) (state (t + 1))

theorem Execution.reachable (E : Execution α n) (t : ℕ) : Reachable (E.state t) := by
  induction t with
  | zero => rw [E.start]; exact Reachable.initial
  | succ t ih => exact Reachable.step ih (E.step t)

theorem Execution.reg_mono (E : Execution α n) (p : ReplicaId n) {t u : ℕ} (h : t ≤ u) :
    RegLE ((E.state t).node p).reg ((E.state u).node p).reg := by
  induction u, h using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih => exact le_trans ih (step_reg_mono (E.reachable u) (E.step u) p)

theorem Execution.issued_mono (E : Execution α n) {t u : ℕ} (h : t ≤ u)
    {a : Entry α n} (ha : a ∈ (E.state t).issued) : a ∈ (E.state u).issued := by
  induction u, h using Nat.le_induction with
  | base => exact ha
  | succ u _ ih => exact step_issued (E.step u) a ih

theorem Execution.sent_mono (E : Execution α n) {t u : ℕ} (h : t ≤ u)
    {S : Snapshot α n} (hs : S ∈ (E.state t).sent) : S ∈ (E.state u).sent := by
  induction u, h using Nat.le_induction with
  | base => exact hs
  | succ u _ ih => exact step_sent (E.step u) S ih

/-- Sending the current state is continuously enabled at every replica. -/
def FairSend (E : Execution α n) : Prop :=
  ∀ p t, ∃ u ≥ t, E.action u = .send p

/-- Per-packet weak fairness for continuously available, still useful snapshots.
The persistent sent archive models reliable availability, without a delay bound. -/
def WeakFairness (E : Execution α n) : Prop :=
  ∀ p S t, (∀ u ≥ t, S ∈ (E.state u).sent ∧ ¬ RegLE S.reg ((E.state u).node p).reg) →
    ∃ u ≥ t, E.action u = .receive p S

theorem packet_eventually_subsumed (E : Execution α n) (fair : WeakFairness E)
    {S : Snapshot α n} {t : ℕ} (hs : S ∈ (E.state t).sent) (p : ReplicaId n) :
    ∃ u ≥ t, RegLE S.reg ((E.state u).node p).reg := by
  by_contra hn
  push Not at hn
  obtain ⟨u, hu, he⟩ := fair p S t (fun u hu => ⟨E.sent_mono hu hs, hn u hu⟩)
  have hstep := E.step u
  rw [he] at hstep
  exact hn (u + 1) (by omega) (received_packet_le hstep)

/-- Every issued update is eventually subsumed, even when intermediate snapshots
are superseded. This theorem does not assume that writes cease. -/
theorem eventual_dissemination (E : Execution α n) (sending : FairSend E)
    (fair : WeakFairness E) {a : Entry α n} {t : ℕ} (ha : a ∈ (E.state t).issued)
    (p : ReplicaId n) : ∃ u ≥ t, RegLE (some a) ((E.state u).node p).reg := by
  obtain ⟨v, hv, he⟩ := sending a.1.node t
  have hs := E.step v
  rw [he] at hs
  have packet := sent_packet_mem hs
  obtain ⟨u, hu, hsub⟩ := packet_eventually_subsumed E fair packet p
  refine ⟨u, by omega, ?_⟩
  exact le_trans ((reachable_invariant (E.reachable v)).covered a (E.issued_mono hv ha)) hsub

def NoWritesAfter (E : Execution α n) (T : ℕ) : Prop :=
  ∀ t ≥ T, ∀ p v, E.action t ≠ .write p v

theorem issued_stable (E : Execution α n) {T : ℕ} (stop : NoWritesAfter E T)
    {u : ℕ} (hu : T ≤ u) : (E.state u).issued = (E.state T).issued := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    have he := no_write_issued (E.step u) (stop u hu)
    exact he.trans ih

theorem finite_history_bound (E : Execution α n) (p : ReplicaId n) (H : List (Entry α n))
    (h : ∀ a ∈ H, ∃ t, RegLE (some a) ((E.state t).node p).reg) :
    ∃ t, ∀ a ∈ H, RegLE (some a) ((E.state t).node p).reg := by
  induction H with
  | nil => exact ⟨0, by simp⟩
  | cons a H ih =>
    obtain ⟨v, hv⟩ := h a (by simp)
    obtain ⟨u, hu⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max v u, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_trans hv (E.reg_mono p (le_max_left _ _))
    · exact le_trans (hu b hb) (E.reg_mono p (le_max_right _ _))

/-- Quiescent stabilization is a consequence of operational fairness, not a premise
that replicas have already exchanged all updates or reached their common maximum. -/
theorem eventual_consistency_stabilization (E : Execution α n) (sending : FairSend E)
    (fair : WeakFairness E) (T : ℕ) (stop : NoWritesAfter E T) :
    ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).reg = summarize (E.state T).issued := by
  classical
  have each (p : ReplicaId n) :
      ∃ t, ∀ a ∈ (E.state T).issued, RegLE (some a) ((E.state t).node p).reg := by
    apply finite_history_bound E p
    intro a ha
    obtain ⟨t, _, ht⟩ := eventual_dissemination E sending fair ha p
    exact ⟨t, ht⟩
  choose time cover using each
  let B := max T (Finset.univ.sup time)
  refine ⟨B, le_max_left _ _, ?_⟩
  intro u hu p
  have hT : T ≤ u := le_trans (le_max_left _ _) hu
  have hp : time p ≤ u := le_trans
    (le_trans (Finset.le_sup (f := time) (Finset.mem_univ p)) (le_max_right _ _)) hu
  have hi := reachable_invariant (E.reachable u)
  have he := issued_stable E stop hT
  have hin : RegIn ((E.state u).node p).reg (E.state T).issued := by
    rw [← he]
    exact regIn_mono (hi.local_max p).1 (hi.histories p)
  have hm : IsMax ((E.state u).node p).reg (E.state T).issued :=
    ⟨hin, fun a ha => le_trans (cover p a ha) (E.reg_mono p hp)⟩
  exact isMax_unique (reachable_invariant (E.reachable T)).unique (fun _ h => h)
    (fun _ h => h) hm (summarize_isMax _) (fun _ => Iff.rfl)

namespace BroadcastBridge

abbrev MessageId (n : ℕ) := DistributedCausalBroadcast.MessageId n
abbrev CBExecution (n : ℕ) := DistributedCausalBroadcast.Execution n

def history (packet : MessageId n → Snapshot α n) (ids : List (MessageId n)) : List (Entry α n) :=
  ids.flatMap fun m => (packet m).history

def replay (packet : MessageId n → Snapshot α n) : List (MessageId n) → LWWReg α n
  | [] => none
  | m :: ids => merge (packet m).reg (replay packet ids)

def ValidPacket (H : List (Entry α n)) (S : Snapshot α n) : Prop :=
  IsMax S.reg S.history ∧ ∀ a ∈ S.history, a ∈ H

theorem replay_max (packet : MessageId n → Snapshot α n) (ids : List (MessageId n))
    (h : ∀ m ∈ ids, IsMax (packet m).reg (packet m).history) :
    IsMax (replay packet ids) (history packet ids) := by
  induction ids with
  | nil => exact isMax_empty
  | cons m ids ih =>
    exact isMax_append (h m (by simp)) (ih (fun a ha => h a (List.mem_cons_of_mem _ ha)))

theorem history_subset {packet : MessageId n → Snapshot α n} {ids : List (MessageId n)}
    {H : List (Entry α n)} (h : ∀ m ∈ ids, ValidPacket H (packet m)) :
    ∀ a ∈ history packet ids, a ∈ H := by
  intro a ha
  obtain ⟨m, hm, ha⟩ := List.mem_flatMap.mp ha
  exact (h m hm).2 a ha

theorem replay_append {packet : MessageId n → Snapshot α n} {xs ys : List (MessageId n)}
    {H : List (Entry α n)} (hu : Unique H)
    (h : ∀ m ∈ xs ++ ys, ValidPacket H (packet m)) :
    replay packet (xs ++ ys) = merge (replay packet xs) (replay packet ys) := by
  have hx m hm := h m (List.mem_append_left ys hm)
  have hy m hm := h m (List.mem_append_right xs hm)
  apply isMax_unique hu (history_subset h)
    (fun a ha => (List.mem_append.mp ha).elim (history_subset hx a) (history_subset hy a))
    (replay_max _ _ (fun m hm => (h m hm).1))
    (isMax_append (replay_max _ _ (fun m hm => (hx m hm).1))
      (replay_max _ _ (fun m hm => (hy m hm).1)))
  intro a
  simp [history]

theorem replay_same_messages {packet : MessageId n → Snapshot α n} {xs ys : List (MessageId n)}
    {H : List (Entry α n)} (hu : Unique H)
    (hx : ∀ m ∈ xs, ValidPacket H (packet m)) (hy : ∀ m ∈ ys, ValidPacket H (packet m))
    (he : ∀ m, m ∈ xs ↔ m ∈ ys) : replay packet xs = replay packet ys := by
  apply isMax_unique hu (history_subset hx) (history_subset hy)
    (replay_max _ _ (fun m hm => (hx m hm).1)) (replay_max _ _ (fun m hm => (hy m hm).1))
  intro a
  simp only [history, List.mem_flatMap]
  constructor <;> rintro ⟨m, hm, ha⟩
  · exact ⟨m, (he m).1 hm, ha⟩
  · exact ⟨m, (he m).2 hm, ha⟩

/-- Immutable message-ID payload binding. The base transport has no application
payload field, so the adapter supplies it without changing transport clocks. -/
def adapter (E : CBExecution n) (packet : MessageId n → Snapshot α n)
    (t : ℕ) (p : ReplicaId n) : LWWReg α n := replay packet ((E.state t).node p).log

theorem adapter_step (E : CBExecution n) (packet : MessageId n → Snapshot α n)
    (H : List (Entry α n)) (hu : Unique H) (valid : ∀ m, ValidPacket H (packet m))
    (t : ℕ) (p : ReplicaId n) :
    adapter E packet (t + 1) p = merge (adapter E packet t p)
      (replay packet (DistributedCausalBroadcast.deliveries (E.state t) (E.action t) p)) := by
  unfold adapter
  rw [DistributedCausalBroadcast.step_log (E.step t)]
  exact replay_append hu (fun m _ => valid m)

theorem packet_le_replay {packet : MessageId n → Snapshot α n} {ids : List (MessageId n)}
    (valid : ∀ m ∈ ids, IsMax (packet m).reg (packet m).history)
    {m : MessageId n} (hm : m ∈ ids) : RegLE (packet m).reg (replay packet ids) := by
  cases hr : (packet m).reg with
  | none => exact bot_le
  | some a =>
    exact (replay_max packet ids valid).2 a
      (List.mem_flatMap.mpr ⟨m, hm, (valid m hm).1 a hr⟩)

/-- A checkpoint packet contains the final snapshot of its sender. Repeated
broadcasts of that checkpoint are harmless; metadata histories remain ghost state. -/
def checkpointPacket (C : Config α n) (m : MessageId n) : Snapshot α n :=
  (C.node m.sender).toSnapshot

theorem checkpoint_valid {C : Config α n} (hc : Reachable C) (m : MessageId n) :
    ValidPacket C.issued (checkpointPacket C m) :=
  ⟨(reachable_invariant hc).local_max m.sender, (reachable_invariant hc).histories m.sender⟩

/-- Every participant broadcasts its checkpoint at least once by the given prefix. -/
def CheckpointAnnounced (E : CBExecution n) (T : ℕ) : Prop :=
  ∀ p, ∃ r ∈ (E.state T).archive, r.message.id.sender = p

theorem causal_broadcast_batch_bridge (H : List (Entry α n)) (unique : Unique H)
    (packet : MessageId n → Snapshot α n) (valid : ∀ m, ValidPacket H (packet m))
    (E : CBExecution n)
    (reliable : DistributedCausalBroadcast.ReliableArrival E)
    (fair : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (coverage : ∀ a ∈ H, ∃ r ∈ (E.state T).archive, RegLE (some a) (packet r.message.id).reg) :
    ∃ B, ∀ u ≥ B, ∀ p, adapter E packet u p = summarize H := by
  classical
  have live := DistributedCausalBroadcast.liveness_under_fairness E reliable fair
  let S := ((E.state T).archive.map fun r => r.message.id).toFinset
  have each (p : ReplicaId n) : ∃ t, ∀ m ∈ S, m ∈ ((E.state t).node p).log := by
    apply DistributedCausalBroadcast.finite_delivery_bound E p S
    intro m hm
    obtain ⟨r, hr, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    subst m
    obtain ⟨t, ht⟩ := live T r hr p
    exact ⟨t + 1, (DistributedCausalBroadcast.log_iff_delivered_before E p r.message.id
      (t + 1)).2 ⟨t, by omega, ht⟩⟩
  choose time cover using each
  refine ⟨Finset.univ.sup time, ?_⟩
  intro u hu p
  have hp : time p ≤ u := le_trans (Finset.le_sup (Finset.mem_univ p)) hu
  have maxPayload := replay_max packet ((E.state u).node p).log
    (fun m _ => (valid m).1)
  have hin := history_subset (fun m (_ : m ∈ ((E.state u).node p).log) => valid m)
  have hg : IsMax (adapter E packet u p) H := by
    refine ⟨regIn_mono maxPayload.1 hin, ?_⟩
    intro a ha
    obtain ⟨r, hr, hcover⟩ := coverage a ha
    have hm : r.message.id ∈ S := List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
    have hlog := E.log_mono p hp (cover p r.message.id hm)
    have bound := packet_le_replay (fun m (_ : m ∈ ((E.state u).node p).log) =>
      (valid m).1) hlog
    exact le_trans hcover bound
  exact isMax_unique unique (fun _ h => h) (fun _ h => h) hg (summarize_isMax _)
    (fun _ => Iff.rfl)

theorem causal_broadcast_bridge {C : Config α n} (hc : Reachable C) (E : CBExecution n)
    (reliable : DistributedCausalBroadcast.ReliableArrival E)
    (fair : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (announced : CheckpointAnnounced E T) :
    ∃ B, ∀ u ≥ B, ∀ p, adapter E (checkpointPacket C) u p = summarize C.issued := by
  apply causal_broadcast_batch_bridge C.issued (reachable_invariant hc).unique
    (checkpointPacket C) (checkpoint_valid hc) E reliable fair T
  intro a ha
  obtain ⟨r, hr, he⟩ := announced a.1.node
  refine ⟨r, hr, ?_⟩
  simpa only [checkpointPacket, he] using (reachable_invariant hc).covered a ha

theorem snapshot_valid_at (E : Execution α n) {t T : ℕ} (ht : t ≤ T) (p : ReplicaId n) :
    ValidPacket (E.state T).issued ((E.state t).node p).toSnapshot := by
  have hi := reachable_invariant (E.reachable t)
  exact ⟨hi.local_max p, fun a ha => E.issued_mono ht (hi.histories p a ha)⟩

end BroadcastBridge

instance (H : List (Entry α n)) [Fact (Unique H)] : OrderBot (ValidState H) where
  bot := ⟨none, by simp [RegIn]⟩
  bot_le r := by
    change (⊥ : WithBot (Stamp n)) ≤ rank r.val
    exact bot_le

theorem merge_monotone {a b c d : LWWReg α n} (hab : RegLE a b) (hcd : RegLE c d) :
    RegLE (merge a c) (merge b d) := by
  simpa only [RegLE, rank_merge] using max_le_max hab hcd

inductive Trace : Config α n → List (Action α n) → Config α n → Prop where
  | nil : Trace C [] C
  | cons {actions : List (Action α n)} : Step C a D → Trace D actions F → Trace C (a :: actions) F

theorem Trace.reachable {C D : Config α n} {actions : List (Action α n)}
    (trace : Trace C actions D) (hc : Reachable C) : Reachable D := by
  induction trace with
  | nil => exact hc
  | cons hs _ ih => exact ih (Reachable.step hc hs)

theorem reachable_write {C : Config α n} (h : Reachable C) (p : ReplicaId n) (v : α) :
    Reachable (write C p v) := Reachable.step h (.write p v)

theorem reachable_send {C : Config α n} (h : Reachable C) (p : ReplicaId n) :
    Reachable (send C p) := Reachable.step h (.send p)

theorem reachable_receive {C : Config α n} (h : Reachable C) (p : ReplicaId n)
    (S : Snapshot α n) (hs : S ∈ C.sent) : Reachable (receive C p S) :=
  Reachable.step h (.receive p S hs)

namespace Regression

def concurrent : Config ℕ 3 := write (write (initial ℕ 3) 0 10) 1 20
def leftPacket : Snapshot ℕ 3 := (concurrent.node 0).toSnapshot
def rightPacket : Snapshot ℕ 3 := (concurrent.node 1).toSnapshot
def transmitted : Config ℕ 3 := send (send concurrent 0) 1
def leftFirst : Config ℕ 3 := receive (receive transmitted 2 leftPacket) 2 rightPacket
def rightFirst : Config ℕ 3 := receive (receive transmitted 2 rightPacket) 2 leftPacket

theorem concurrent_reachable : Reachable concurrent :=
  reachable_write (reachable_write Reachable.initial 0 10) 1 20

theorem transmitted_reachable : Reachable transmitted :=
  reachable_send (reachable_send concurrent_reachable 0) 1

theorem both_orders_reachable : Reachable leftFirst ∧ Reachable rightFirst := by
  constructor
  · exact reachable_receive (reachable_receive transmitted_reachable 2 leftPacket (by
      simp [transmitted, send, leftPacket])) 2 rightPacket (by
      simp [receive, transmitted, send, rightPacket])
  · exact reachable_receive (reachable_receive transmitted_reachable 2 rightPacket (by
      simp [transmitted, send, rightPacket])) 2 leftPacket (by
      simp [receive, transmitted, send, leftPacket])

theorem reg_bottom (r : LWWReg α n) : merge none r = r ∧ merge r none = r :=
  ⟨none_merge r, merge_none r⟩

theorem reg_concurrent_tie :
    (leftFirst.node 2).reg = some (⟨1, 1⟩, 20) ∧
    (rightFirst.node 2).reg = some (⟨1, 1⟩, 20) := by decide +kernel

theorem reg_duplicate :
    ((receive leftFirst 2 rightPacket).node 2).reg = (leftFirst.node 2).reg := by decide +kernel

theorem reg_late_snapshot :
    ((receive leftFirst 2 leftPacket).node 2).reg = (leftFirst.node 2).reg := by decide +kernel

def localTwice : Config ℕ 1 := write (write (initial ℕ 1) 0 10) 0 20

theorem reg_single_replica : Reachable localTwice ∧
    (localTwice.node 0).reg = some (⟨2, 0⟩, 20) :=
  ⟨reachable_write (reachable_write Reachable.initial 0 10) 0 20, by decide +kernel⟩

def sourceTwice : Config ℕ 2 := write (write (initial ℕ 2) 0 10) 0 20
def sourcePacket : Snapshot ℕ 2 := (sourceTwice.node 0).toSnapshot
def observed : Config ℕ 2 := receive (send sourceTwice 0) 1 sourcePacket

theorem observed_reachable : Reachable observed :=
  reachable_receive (reachable_send
    (reachable_write (reachable_write Reachable.initial 0 10) 0 20) 0) 1 sourcePacket
      (by simp [send, sourcePacket, sourceTwice])

theorem reg_observed_counter :
    ((write observed 1 30).node 1).reg = some (⟨3, 1⟩, 30) := by decide +kernel

def badCounterMerge (a b : Entry ℕ 2) : Entry ℕ 2 :=
  if a.1.counter ≤ b.1.counter then b else a

def staleOverwrite (C : Config ℕ 2) (p : ReplicaId 2) (v : ℕ) : Config ℕ 2 :=
  { C with node := fun q => if q = p then
    { C.node p with reg := some (⟨1, p⟩, v) } else C.node q }

end Regression

theorem counterexample_tie_breaking :
    Regression.badCounterMerge (⟨1, 0⟩, 10) (⟨1, 1⟩, 20) ≠
    Regression.badCounterMerge (⟨1, 1⟩, 20) (⟨1, 0⟩, 10) := by decide +kernel

/-- Equal complete stamps with different values are excluded by the reachable
invariant; merge is deliberately not claimed commutative on malformed records. -/
theorem counterexample_colliding_stamp :
    merge (some ((⟨1, 0⟩ : Stamp 1), 10)) (some (⟨1, 0⟩, 20)) ≠
    merge (some (⟨1, 0⟩, 20)) (some (⟨1, 0⟩, 10)) := by decide +kernel

theorem counterexample_stale_stamp : Reachable Regression.observed ∧
    ¬ RegLE (Regression.observed.node 1).reg
      ((Regression.staleOverwrite Regression.observed 1 30).node 1).reg :=
  ⟨Regression.observed_reachable, by decide +kernel⟩

structure DistributedCRDTStateLWWSuite : Prop where
  stamp_total : ∀ n (a b : Stamp n), a ≤ b ∨ b ≤ a
  unique : ∀ (α : Type) n (C : Config α n), Reachable C → Unique C.issued
  algebra : ∀ (α : Type) n (H : List (Entry α n)), Unique H →
    ∀ r s t, RegIn r H → RegIn s H → RegIn t H →
      merge r s = merge s r ∧ merge (merge r s) t = merge r (merge s t) ∧ merge r r = r
  inflationary : ∀ (α : Type) n (r s : LWWReg α n),
    RegLE r (merge r s) ∧ RegLE s (merge r s)
  payload : ∀ (α : Type) n (C : Config α n), Reachable C → ∀ p,
    IsMax (C.node p).reg (C.node p).history ∧ (C.node p).reg = summarize (C.node p).history
  strong_convergence : ∀ (α : Type) n (C : Config α n), Reachable C → ∀ p q,
    (∀ a, a ∈ (C.node p).history ↔ a ∈ (C.node q).history) → (C.node p).reg = (C.node q).reg
  dissemination : ∀ (α : Type) n (E : Execution α n), FairSend E → WeakFairness E →
    ∀ t a, a ∈ (E.state t).issued → ∀ p, ∃ u ≥ t, RegLE (some a) ((E.state u).node p).reg
  stabilization : ∀ (α : Type) n (E : Execution α n), FairSend E → WeakFairness E →
    ∀ T, NoWritesAfter E T →
      ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).reg = summarize (E.state T).issued
  broadcast : ∀ (α : Type) n (C : Config α n), Reachable C →
    ∀ E : BroadcastBridge.CBExecution n, DistributedCausalBroadcast.ReliableArrival E →
      DistributedCausalBroadcast.WeakFairness E → ∀ T, BroadcastBridge.CheckpointAnnounced E T →
        ∃ B, ∀ u ≥ B, ∀ p,
          BroadcastBridge.adapter E (BroadcastBridge.checkpointPacket C) u p = summarize C.issued
  guards :
    Regression.badCounterMerge (⟨1, 0⟩, 10) (⟨1, 1⟩, 20) ≠
      Regression.badCounterMerge (⟨1, 1⟩, 20) (⟨1, 0⟩, 10) ∧
    ¬ RegLE (Regression.observed.node 1).reg
      ((Regression.staleOverwrite Regression.observed 1 30).node 1).reg
  regressions : Reachable Regression.leftFirst ∧ Reachable Regression.rightFirst ∧
    (Regression.leftFirst.node 2).reg = some (⟨1, 1⟩, 20) ∧
    (Regression.rightFirst.node 2).reg = some (⟨1, 1⟩, 20)

theorem distributed_crdt_state_lww_master_suite : DistributedCRDTStateLWWSuite where
  stamp_total := fun _ _ _ => le_total _ _
  unique := fun _ _ _ h => (reachable_invariant h).unique
  algebra := fun _ _ _ hu _ _ _ hr hs ht =>
    ⟨merge_comm hu hr hs, merge_assoc hu hr hs ht, merge_idem _⟩
  inflationary := fun _ _ => merge_inflationary
  payload := fun _ _ _ h => payload_is_max_history h
  strong_convergence := fun _ _ _ h => sec_strong_convergence h
  dissemination := fun _ _ E sending fair _ _ ha p => eventual_dissemination E sending fair ha p
  stabilization := fun _ _ => eventual_consistency_stabilization
  broadcast := fun _ _ _ hc => BroadcastBridge.causal_broadcast_bridge hc
  guards := ⟨counterexample_tie_breaking, counterexample_stale_stamp.2⟩
  regressions := ⟨Regression.both_orders_reachable.1, Regression.both_orders_reachable.2,
    Regression.reg_concurrent_tie.1, Regression.reg_concurrent_tie.2⟩

end DistributedCRDTStateLWW
