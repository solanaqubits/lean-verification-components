/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedCRDTStateLWW
import Verification.DistributedCausalBroadcast
import Mathlib.Order.Lattice

/-! A state-based observed-remove set with permanent tombstones. Ghost histories
record immutable operations and their observed causal context; merge reads only
metadata. No total order on tags or on delivered messages is required. -/
namespace DistributedCRDTORSet

abbrev NodeId (n : ℕ) := Fin n
abbrev Tag (n : ℕ) := ℕ × Fin n

@[ext] structure ORSetState (α : Type*) (n : ℕ) where
  added : Finset (α × Tag n)
  removed : Finset (α × Tag n)
  deriving DecidableEq

variable {α : Type*} {n : ℕ} [DecidableEq α]

def Invariant (S : ORSetState α n) : Prop := S.removed ⊆ S.added

def contains (x : α) (S : ORSetState α n) : Prop :=
  ∃ t, (x, t) ∈ S.added ∧ (x, t) ∉ S.removed

def merge (S T : ORSetState α n) : ORSetState α n :=
  ⟨S.added ∪ T.added, S.removed ∪ T.removed⟩

instance : PartialOrder (ORSetState α n) where
  le S T := S.added ⊆ T.added ∧ S.removed ⊆ T.removed
  le_refl _ := ⟨Finset.Subset.refl _, Finset.Subset.refl _⟩
  le_trans _ _ _ h k := ⟨h.1.trans k.1, h.2.trans k.2⟩
  le_antisymm _ _ h k := ORSetState.ext (Finset.Subset.antisymm h.1 k.1)
    (Finset.Subset.antisymm h.2 k.2)

instance : SemilatticeSup (ORSetState α n) where
  sup := merge
  le_sup_left _ _ := ⟨Finset.subset_union_left, Finset.subset_union_left⟩
  le_sup_right _ _ := ⟨Finset.subset_union_right, Finset.subset_union_right⟩
  sup_le _ _ _ h k := ⟨Finset.union_subset h.1 k.1, Finset.union_subset h.2 k.2⟩

instance : OrderBot (ORSetState α n) where
  bot := ⟨∅, ∅⟩
  bot_le _ := ⟨Finset.empty_subset _, Finset.empty_subset _⟩

@[simp] theorem sup_added (S T : ORSetState α n) : (S ⊔ T).added = S.added ∪ T.added := rfl
@[simp] theorem sup_removed (S T : ORSetState α n) : (S ⊔ T).removed = S.removed ∪ T.removed := rfl
omit [DecidableEq α] in
@[simp] theorem bot_added : (⊥ : ORSetState α n).added = ∅ := rfl
omit [DecidableEq α] in
@[simp] theorem bot_removed : (⊥ : ORSetState α n).removed = ∅ := rfl

theorem merge_assoc (S T U : ORSetState α n) : merge (merge S T) U = merge S (merge T U) :=
  sup_assoc S T U
theorem merge_comm (S T : ORSetState α n) : merge S T = merge T S := sup_comm S T
theorem merge_idem (S : ORSetState α n) : merge S S = S := sup_idem S
theorem merge_inflationary (S T : ORSetState α n) : S ≤ S ⊔ T ∧ T ≤ S ⊔ T :=
  ⟨le_sup_left, le_sup_right⟩
theorem invariant_merge {S T : ORSetState α n} (hS : Invariant S) (hT : Invariant T) :
    Invariant (S ⊔ T) := Finset.union_subset_union hS hT

def observed (x : α) (S : ORSetState α n) : Finset (α × Tag n) :=
  S.added.filter fun z => z.1 = x ∧ z ∉ S.removed

def addTag (x : α) (t : Tag n) (S : ORSetState α n) : ORSetState α n :=
  ⟨insert (x, t) S.added, S.removed⟩

def remove (x : α) (S : ORSetState α n) : ORSetState α n :=
  ⟨S.added, S.removed ∪ observed x S⟩

theorem observed_remove_exact (x y : α) (t : Tag n) (S : ORSetState α n) :
    ((y, t) ∈ (remove x S).removed ↔ (y, t) ∈ S.removed ∨
      ((y, t) ∈ S.added ∧ y = x ∧ (y, t) ∉ S.removed)) ∧
    (contains y (remove x S) ↔ contains y S ∧ y ≠ x) := by
  constructor
  · simp [remove, observed]
  · simp only [contains, remove, Finset.mem_union, observed, Finset.mem_filter]
    constructor
    · rintro ⟨t, ha, hn⟩
      exact ⟨⟨t, ha, fun h => hn (Or.inl h)⟩,
        fun he => hn (Or.inr ⟨ha, he, fun h => hn (Or.inl h)⟩)⟩
    · rintro ⟨⟨t, ha, hn⟩, hne⟩
      exact ⟨t, ha, fun h => h.elim hn (fun h => hne h.2.1)⟩

theorem removed_tag_never_resurrects {x : α} {t : Tag n} {S : ORSetState α n}
    (h : (x, t) ∈ S.removed) (T : ORSetState α n) : (x, t) ∈ (S ⊔ T).removed :=
  Finset.mem_union_left _ h

theorem readd_after_remove (x : α) (S : ORSetState α n) (t : Tag n)
    (fresh : (x, t) ∉ S.added) (valid : Invariant S) :
    contains x (addTag x t (remove x S)) := by
  refine ⟨t, Finset.mem_insert_self _ _, ?_⟩
  simp only [addTag, remove, Finset.mem_union, not_or]
  exact ⟨fun h => fresh (valid h), fun h => fresh (Finset.mem_filter.mp h).1⟩

inductive Kind (α : Type*) (n : ℕ) where
  | add (value : α)
  | remove (value : α) (context : Finset (α × Tag n))
  deriving DecidableEq

/-- IDs identify all local updates, not just additions. Past is ghost observation
of operation IDs received before this update, independent of element visibility. -/
structure Update (α : Type*) (n : ℕ) where
  id : Tag n
  serial : ℕ
  past : Finset (Tag n)
  kind : Kind α n
  deriving DecidableEq

def effect (a : Update α n) : ORSetState α n :=
  match a.kind with
  | .add x => ⟨{(x, a.id)}, ∅⟩
  | .remove _ R => ⟨R, R⟩

def summarize : List (Update α n) → ORSetState α n
  | [] => ⊥
  | a :: H => effect a ⊔ summarize H

@[simp] theorem summarize_nil : summarize ([] : List (Update α n)) = ⊥ := rfl
@[simp] theorem summarize_cons (a : Update α n) (H : List (Update α n)) :
    summarize (a :: H) = effect a ⊔ summarize H := rfl

theorem summarize_append (H K : List (Update α n)) :
    summarize (H ++ K) = summarize H ⊔ summarize K := by
  induction H with
  | nil => simp
  | cons a H ih => simp [ih, sup_assoc]

theorem effect_le_summary {a : Update α n} {H : List (Update α n)} (h : a ∈ H) :
    effect a ≤ summarize H := by
  induction H with
  | nil => simp at h
  | cons b H ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact le_sup_left
    · exact le_trans (ih h) le_sup_right

theorem summary_le {H : List (Update α n)} {S : ORSetState α n}
    (h : ∀ a ∈ H, effect a ≤ S) : summarize H ≤ S := by
  induction H with
  | nil => exact bot_le
  | cons a H ih => exact sup_le (h a (by simp)) (ih (fun b hb => h b (by simp [hb])))

theorem summary_same_set {H K : List (Update α n)} (h : ∀ a, a ∈ H ↔ a ∈ K) :
    summarize H = summarize K := by
  apply le_antisymm
  · exact summary_le (fun a ha => effect_le_summary ((h a).1 ha))
  · exact summary_le (fun a ha => effect_le_summary ((h a).2 ha))

theorem summary_invariant (H : List (Update α n)) : Invariant (summarize H) := by
  induction H with
  | nil => exact Finset.empty_subset _
  | cons a H ih =>
    apply invariant_merge _ ih
    cases hk : a.kind <;> simp [effect, hk, Invariant]

structure Snapshot (α : Type*) (n : ℕ) where
  payload : ORSetState α n
  history : List (Update α n)

structure NodeState (α : Type*) (n : ℕ) extends Snapshot α n where
  clock : ℕ

structure Config (α : Type*) (n : ℕ) where
  node : NodeId n → NodeState α n
  issued : List (Update α n)
  sent : List (Snapshot α n)

def initial (α : Type*) (n : ℕ) : Config α n :=
  ⟨fun _ => ⟨⟨⊥, []⟩, 0⟩, [], []⟩

def nextUpdate (C : Config α n) (p : NodeId n) (k : Kind α n) : Update α n :=
  ⟨((C.node p).clock + 1, p), C.issued.length, ((C.node p).history.map Update.id).toFinset, k⟩

def commit (C : Config α n) (p : NodeId n) (k : Kind α n) : Config α n :=
  { C with
    node := fun q => if q = p then
      ⟨⟨(C.node p).payload ⊔ effect (nextUpdate C p k),
        (C.node p).history ++ [nextUpdate C p k]⟩, (C.node p).clock + 1⟩ else C.node q
    issued := C.issued ++ [nextUpdate C p k] }

def add (C : Config α n) (p : NodeId n) (x : α) : Config α n := commit C p (.add x)
def erase (C : Config α n) (p : NodeId n) (x : α) : Config α n :=
  commit C p (.remove x (observed x (C.node p).payload))

def send (C : Config α n) (p : NodeId n) : Config α n :=
  { C with sent := C.sent ++ [(C.node p).toSnapshot] }

def receive (C : Config α n) (p : NodeId n) (S : Snapshot α n) : Config α n :=
  { C with node := fun q => if q = p then
    ⟨⟨(C.node p).payload ⊔ S.payload, (C.node p).history ++ S.history⟩,
      (C.node p).clock⟩ else C.node q }

inductive Action (α : Type*) (n : ℕ) where
  | idle
  | add (p : NodeId n) (x : α)
  | remove (p : NodeId n) (x : α)
  | send (p : NodeId n)
  | receive (p : NodeId n) (packet : Snapshot α n)

inductive Step : Config α n → Action α n → Config α n → Prop where
  | idle : Step C .idle C
  | add (p x) : Step C (.add p x) (add C p x)
  | remove (p x) : Step C (.remove p x) (erase C p x)
  | send (p) : Step C (.send p) (send C p)
  | receive (p S) (hs : S ∈ C.sent) : Step C (.receive p S) (receive C p S)

inductive Reachable : Config α n → Prop where
  | initial : Reachable (initial α n)
  | step : Reachable C → Step C a D → Reachable D

/-- Every tag in a snapshot originates in an actual add in its ghost history. -/
def Provenance (S : Snapshot α n) : Prop :=
  ∀ z ∈ S.payload.added, ∃ a ∈ S.history, a.id = z.2 ∧ a.kind = .add z.1

/-- Causal closure contains the observed past of every included update. -/
def Closed (H : List (Update α n)) : Prop :=
  ∀ a ∈ H, ∀ t ∈ a.past, ∃ b ∈ H, b.id = t

def SoundSnapshot (S : Snapshot α n) : Prop :=
  S.payload = summarize S.history ∧ Provenance S ∧ Closed S.history

def RemovalOrigin (a : Update α n) (H : List (Update α n)) : Prop :=
  ∀ z ∈ (effect a).removed, ∃ b ∈ H, b.id = z.2 ∧ b.kind = .add z.1 ∧ b.id ∈ a.past

structure ConfigInvariant (C : Config α n) : Prop where
  unique : ∀ a ∈ C.issued, ∀ b ∈ C.issued, a.id = b.id → a = b
  origin_bound : ∀ a ∈ C.issued, a.id.1 ≤ (C.node a.id.2).clock
  sound : ∀ p, SoundSnapshot (C.node p).toSnapshot
  histories : ∀ p a, a ∈ (C.node p).history → a ∈ C.issued
  packets : ∀ S ∈ C.sent, SoundSnapshot S ∧ ∀ a ∈ S.history, a ∈ C.issued
  removals : ∀ a ∈ C.issued, RemovalOrigin a C.issued
  covered : ∀ a ∈ C.issued, effect a ≤ (C.node a.id.2).payload
  issued_closed : Closed C.issued
  serial_bound : ∀ a ∈ C.issued, a.serial < C.issued.length
  past_earlier : ∀ a ∈ C.issued, ∀ b ∈ C.issued, b.id ∈ a.past → b.serial < a.serial
  past_closed : ∀ a ∈ C.issued, ∀ b ∈ C.issued, b.id ∈ a.past → b.past ⊆ a.past

theorem invariant_initial : ConfigInvariant (initial α n) := by
  constructor <;> simp [initial, SoundSnapshot, Provenance, Closed]

theorem next_fresh {C : Config α n} (h : ConfigInvariant C) (p : NodeId n) (k : Kind α n)
    {a : Update α n} (ha : a ∈ C.issued) : a.id ≠ (nextUpdate C p k).id := by
  intro he
  have hb := h.origin_bound a ha
  have hn := congrArg Prod.snd he
  have hc := congrArg Prod.fst he
  simp only [nextUpdate] at hn hc
  rw [hn] at hb
  omega

theorem commit_clock_mono (C : Config α n) (p q : NodeId n) (k : Kind α n) :
    (C.node q).clock ≤ ((commit C p k).node q).clock := by
  by_cases he : q = p <;> simp [commit, he]

theorem commit_payload_mono (C : Config α n) (p q : NodeId n) (k : Kind α n) :
    (C.node q).payload ≤ ((commit C p k).node q).payload := by
  by_cases he : q = p
  · subst q; simpa only [commit, receive, ↓reduceIte] using
      (le_sup_left : (C.node p).payload ≤ (C.node p).payload ⊔ _)
  · simp [commit, he]

omit [DecidableEq α] in
theorem closed_append {H K : List (Update α n)} (hH : Closed H) (hK : Closed K) :
    Closed (H ++ K) := by
  intro a ha t ht
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨b, hb, he⟩ := hH a ha t ht
    exact ⟨b, List.mem_append_left _ hb, he⟩
  · obtain ⟨b, hb, he⟩ := hK a ha t ht
    exact ⟨b, List.mem_append_right _ hb, he⟩

theorem ConfigInvariant.preserve_commit {C : Config α n} (h : ConfigInvariant C)
    (p : NodeId n) (k : Kind α n)
    (prov : ∀ z ∈ (effect (nextUpdate C p k)).added,
      ∃ a ∈ (C.node p).history ++ [nextUpdate C p k], a.id = z.2 ∧ a.kind = .add z.1)
    (rem : ∀ z ∈ (effect (nextUpdate C p k)).removed,
      ∃ a ∈ (C.node p).history, a.id = z.2 ∧ a.kind = .add z.1) :
    ConfigInvariant (commit C p k) := by
  let u := nextUpdate C p k
  have hin (a : Update α n) (ha : a ∈ C.issued) : a ∈ (commit C p k).issued :=
    List.mem_append_left _ ha
  have hnew : u ∈ (commit C p k).issued := List.mem_append_right _ (by simp [u])
  have hmem (a : Update α n) : a ∈ (commit C p k).issued ↔ a ∈ C.issued ∨ a = u := by
    simp [commit, u]
  have past (b : Update α n) (hb : b ∈ (C.node p).history) : b.id ∈ u.past := by
    simp only [u, nextUpdate, List.mem_toFinset, List.mem_map]
    exact ⟨b, hb, rfl⟩
  have lookup {b : Update α n} (hb : b ∈ C.issued) (hp : b.id ∈ u.past) :
      b ∈ (C.node p).history := by
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
    have heq := h.unique a (h.histories p a ha) b hb he
    simpa only [heq] using ha
  have unot {a : Update α n} (ha : a ∈ C.issued) : u.id ∉ a.past := by
    intro hp
    obtain ⟨b, hb, he⟩ := h.issued_closed a ha u.id hp
    exact next_fresh h p k hb he
  constructor
  · intro a ha b hb he
    rcases (hmem a).1 ha with ha | rfl <;> rcases (hmem b).1 hb with hb | rfl
    · exact h.unique a ha b hb he
    · exact (next_fresh h p k ha he).elim
    · exact (next_fresh h p k hb he.symm).elim
    · rfl
  · intro a ha
    rcases (hmem a).1 ha with ha | rfl
    · exact le_trans (h.origin_bound a ha) (commit_clock_mono C p a.id.2 k)
    · simp [commit, u, nextUpdate]
  · intro q
    by_cases he : q = p
    · subst q
      simp only [commit, ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩
      · simpa [commit, summarize_append] using congrArg (fun S => S ⊔ effect u) (h.sound p).1
      · intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨a, ha, hid, hk⟩ := (h.sound p).2.1 z hz
          exact ⟨a, List.mem_append_left _ ha, hid, hk⟩
        · exact prov z hz
      · intro a ha t ht
        rcases List.mem_append.mp ha with ha | ha
        · obtain ⟨b, hb, he⟩ := (h.sound p).2.2 a ha t ht
          exact ⟨b, List.mem_append_left _ hb, he⟩
        · have he := List.mem_singleton.mp ha; subst a
          obtain ⟨b, hb, he⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
          exact ⟨b, List.mem_append_left _ hb, he⟩
    · simpa [commit, he] using h.sound q
  · intro q a ha
    by_cases he : q = p
    · subst q
      simp only [commit, ↓reduceIte] at ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hin a (h.histories p a ha)
      · simpa only [List.mem_singleton.mp ha] using hnew
    · exact hin a (h.histories q a (by simpa [commit, he] using ha))
  · intro S hs
    exact ⟨(h.packets S hs).1, fun a ha => hin a ((h.packets S hs).2 a ha)⟩
  · intro a ha z hz
    rcases (hmem a).1 ha with ha | rfl
    · obtain ⟨b, hb, hid, hk, hp⟩ := h.removals a ha z hz
      exact ⟨b, hin b hb, hid, hk, hp⟩
    · obtain ⟨b, hb, hid, hk⟩ := rem z hz
      exact ⟨b, hin b (h.histories p b hb), hid, hk, past b hb⟩
  · intro a ha
    rcases (hmem a).1 ha with ha | rfl
    · exact le_trans (h.covered a ha) (commit_payload_mono C p a.id.2 k)
    · simpa only [u, nextUpdate, commit, ↓reduceIte] using
        (le_sup_right : effect (nextUpdate C p k) ≤ (C.node p).payload ⊔ effect (nextUpdate C p k))
  · intro a ha t ht
    rcases (hmem a).1 ha with ha | rfl
    · obtain ⟨b, hb, he⟩ := h.issued_closed a ha t ht
      exact ⟨b, hin b hb, he⟩
    · obtain ⟨b, hb, he⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
      exact ⟨b, hin b (h.histories p b hb), he⟩
  · intro a ha
    rcases (hmem a).1 ha with ha | rfl
    · have hb := h.serial_bound a ha
      simpa only [commit, List.length_append, List.length_singleton] using Nat.lt_succ_of_lt hb
    · simp [u, nextUpdate, commit]
  · intro a ha b hb hp
    rcases (hmem a).1 ha with ha | rfl <;> rcases (hmem b).1 hb with hb | rfl
    · exact h.past_earlier a ha b hb hp
    · exact (unot ha hp).elim
    · exact h.serial_bound b hb
    · obtain ⟨b, hb, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      exact (next_fresh h p k (h.histories p b hb) he).elim
  · intro a ha b hb hp
    rcases (hmem a).1 ha with ha | rfl <;> rcases (hmem b).1 hb with hb | rfl
    · exact h.past_closed a ha b hb hp
    · exact (unot ha hp).elim
    · intro t ht
      obtain ⟨c, hc, he⟩ := (h.sound p).2.2 b (lookup hb hp) t ht
      rw [← he]; exact past c hc
    · obtain ⟨b, hb, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hp)
      exact (next_fresh h p k (h.histories p b hb) he).elim

theorem ConfigInvariant.preserve_add {C : Config α n} (h : ConfigInvariant C)
    (p : NodeId n) (x : α) : ConfigInvariant (add C p x) := by
  apply h.preserve_commit
  · intro z hz
    have he : z = (x, (nextUpdate C p (.add x)).id) := Finset.mem_singleton.mp hz
    subst z
    exact ⟨_, List.mem_append_right _ (by simp), rfl, rfl⟩
  · simp [effect, nextUpdate]

theorem ConfigInvariant.preserve_remove {C : Config α n} (h : ConfigInvariant C)
    (p : NodeId n) (x : α) : ConfigInvariant (erase C p x) := by
  apply h.preserve_commit
  · intro z hz
    obtain ⟨a, ha, hid, hk⟩ := (h.sound p).2.1 z (Finset.mem_filter.mp hz).1
    exact ⟨a, List.mem_append_left _ ha, hid, hk⟩
  · intro z hz
    exact (h.sound p).2.1 z (Finset.mem_filter.mp hz).1

theorem ConfigInvariant.preserve_send {C : Config α n} (h : ConfigInvariant C) (p : NodeId n) :
    ConfigInvariant (send C p) := by
  refine { h with packets := ?_ }
  intro S hs
  rcases List.mem_append.mp hs with hs | hs
  · exact h.packets S hs
  · have he := List.mem_singleton.mp hs; subst S
    exact ⟨h.sound p, h.histories p⟩

theorem receive_payload_mono (C : Config α n) (p q : NodeId n) (S : Snapshot α n) :
    (C.node q).payload ≤ ((receive C p S).node q).payload := by
  by_cases he : q = p
  · subst q; simpa only [commit, receive, ↓reduceIte] using
      (le_sup_left : (C.node p).payload ≤ (C.node p).payload ⊔ _)
  · simp [receive, he]

theorem ConfigInvariant.preserve_receive {C : Config α n} (h : ConfigInvariant C)
    (p : NodeId n) (S : Snapshot α n) (hs : S ∈ C.sent) : ConfigInvariant (receive C p S) := by
  have hp := h.packets S hs
  refine { h with origin_bound := ?_, sound := ?_, histories := ?_, covered := ?_ }
  · intro a ha
    by_cases he : a.id.2 = p <;> simpa [receive, he] using h.origin_bound a ha
  · intro q
    by_cases he : q = p
    · subst q
      simp only [receive, ↓reduceIte]
      refine ⟨?_, ?_, closed_append (h.sound p).2.2 hp.1.2.2⟩
      · simp [summarize_append, (h.sound p).1, hp.1.1]
      · intro z hz
        rcases Finset.mem_union.mp hz with hz | hz
        · obtain ⟨a, ha, hid, hk⟩ := (h.sound p).2.1 z hz
          exact ⟨a, List.mem_append_left _ ha, hid, hk⟩
        · obtain ⟨a, ha, hid, hk⟩ := hp.1.2.1 z hz
          exact ⟨a, List.mem_append_right _ ha, hid, hk⟩
    · simpa [receive, he] using h.sound q
  · intro q a ha
    by_cases he : q = p
    · subst q
      simp only [receive, ↓reduceIte] at ha
      exact (List.mem_append.mp ha).elim (h.histories p a) (hp.2 a)
    · exact h.histories q a (by simpa [receive, he] using ha)
  · intro a ha
    exact le_trans (h.covered a ha) (receive_payload_mono C p a.id.2 S)

theorem reachable_invariant {C : Config α n} (hc : Reachable C) : ConfigInvariant C := by
  induction hc with
  | initial => exact invariant_initial
  | step _ hs ih =>
    cases hs with
    | idle => exact ih
    | add p x => exact ih.preserve_add p x
    | remove p x => exact ih.preserve_remove p x
    | send p => exact ih.preserve_send p
    | receive p S hs => exact ih.preserve_receive p S hs

theorem tag_uniqueness {C : Config α n} (hc : Reachable C) {a b : Update α n}
    (ha : a ∈ C.issued) (hb : b ∈ C.issued) (he : a.id = b.id) : a = b :=
  (reachable_invariant hc).unique a ha b hb he

theorem state_is_join_history {C : Config α n} (hc : Reachable C) (p : NodeId n) :
    (C.node p).payload = summarize (C.node p).history := (reachable_invariant hc).sound p |>.1

theorem reachable_metadata_invariant {C : Config α n} (hc : Reachable C) (p : NodeId n) :
    Invariant (C.node p).payload := by
  rw [state_is_join_history hc p]
  exact summary_invariant _

theorem sec_strong_convergence {C D : Config α n} (hc : Reachable C) (hd : Reachable D)
    (p q : NodeId n) (he : ∀ a, a ∈ (C.node p).history ↔ a ∈ (D.node q).history) :
    (C.node p).payload = (D.node q).payload := by
  rw [state_is_join_history hc p, state_is_join_history hd q]
  exact summary_same_set he

/-- Observation causality: local updates inherit all operation IDs from local and
received snapshot histories. It is independent of the merge order and visible set. -/
def HappensBefore (a b : Update α n) : Prop := a.id ∈ b.past

def Concurrent (a b : Update α n) : Prop :=
  a ≠ b ∧ ¬ HappensBefore a b ∧ ¬ HappensBefore b a

theorem happens_before_irrefl {C : Config α n} (hc : Reachable C)
    {a : Update α n} (ha : a ∈ C.issued) : ¬ HappensBefore a a := by
  intro h
  exact Nat.lt_irrefl _ ((reachable_invariant hc).past_earlier a ha a ha h)

theorem happens_before_trans {C : Config α n} (hc : Reachable C)
    {a b c : Update α n} (hb : b ∈ C.issued) (hc' : c ∈ C.issued)
    (hab : HappensBefore a b) (hbc : HappensBefore b c) : HappensBefore a c :=
  (reachable_invariant hc).past_closed c hc' b hb hbc hab

theorem remove_context_excludes_concurrent_add {C : Config α n} (hc : Reachable C)
    {a b : Update α n} {x : α} (ha : a ∈ C.issued) (hb : b ∈ C.issued)
    (_hk : a.kind = .add x) (concurrent : Concurrent a b) : (x, a.id) ∉ (effect b).removed := by
  intro hz
  obtain ⟨d, hd, hid, _, hp⟩ := (reachable_invariant hc).removals b hb (x, a.id) hz
  have he := tag_uniqueness hc hd ha hid
  subst d
  exact concurrent.2.1 hp

/-- The merged effects of this concurrent pair keep the new addition. Other,
later observed removals are not excluded from removing the same tag. -/
theorem concurrent_add_wins {C : Config α n} (hc : Reachable C)
    {a b : Update α n} {x : α} (ha : a ∈ C.issued) (hb : b ∈ C.issued)
    (hk : a.kind = .add x) (concurrent : Concurrent a b) :
    contains x (effect a ⊔ effect b) := by
  refine ⟨a.id, ?_, ?_⟩
  · simp [effect, hk]
  · simpa [effect, hk] using remove_context_excludes_concurrent_add hc ha hb hk concurrent

theorem add_payload (C : Config α n) (p : NodeId n) (x : α) :
    ((add C p x).node p).payload = addTag x ((C.node p).clock + 1, p) (C.node p).payload := by
  ext <;> simp [add, commit, effect, nextUpdate, addTag, Finset.union_singleton]

theorem remove_payload (C : Config α n) (p : NodeId n) (x : α) :
    ((erase C p x).node p).payload = remove x (C.node p).payload := by
  apply ORSetState.ext
  · simp only [erase, commit, ↓reduceIte, sup_added, effect, nextUpdate, remove]
    exact Finset.union_eq_left.mpr (Finset.filter_subset _ _)
  · simp [erase, commit, effect, nextUpdate, remove]

theorem operational_readd {C : Config α n} (hc : Reachable C) (p : NodeId n) (x : α) :
    contains x ((add C p x).node p).payload := by
  rw [add_payload]
  refine ⟨_, Finset.mem_insert_self _ _, ?_⟩
  intro hr
  have ha := reachable_metadata_invariant hc p hr
  obtain ⟨a, ha, hid, _⟩ := (reachable_invariant hc).sound p |>.2.1 _ ha
  exact next_fresh (reachable_invariant hc) p (.add x)
    ((reachable_invariant hc).histories p a ha) hid

theorem step_issued {C D : Config α n} {a : Action α n} (hs : Step C a D) :
    ∀ w ∈ C.issued, w ∈ D.issued := by
  cases hs with
  | add => exact fun _ h => List.mem_append_left _ h
  | remove => exact fun _ h => List.mem_append_left _ h
  | idle => exact fun _ h => h
  | send => exact fun _ h => h
  | receive => exact fun _ h => h

theorem step_sent {C D : Config α n} {a : Action α n} (hs : Step C a D) :
    ∀ S ∈ C.sent, S ∈ D.sent := by
  cases hs with
  | send => exact fun _ h => List.mem_append_left _ h
  | idle => exact fun _ h => h
  | add => exact fun _ h => h
  | remove => exact fun _ h => h
  | receive => exact fun _ h => h

theorem step_payload_mono {C D : Config α n} {a : Action α n}
    (hs : Step C a D) (p : NodeId n) : (C.node p).payload ≤ (D.node p).payload := by
  cases hs with
  | idle => exact le_rfl
  | add q x => exact commit_payload_mono C q p (.add x)
  | remove q x => exact commit_payload_mono C q p _
  | send => exact le_rfl
  | receive q S => exact receive_payload_mono C q p S

theorem received_packet_le {C D : Config α n} {p : NodeId n} {S : Snapshot α n}
    (hs : Step C (.receive p S) D) : S.payload ≤ (D.node p).payload := by
  cases hs
  simp [receive]

theorem sent_packet_mem {C D : Config α n} {p : NodeId n}
    (hs : Step C (.send p) D) : (C.node p).toSnapshot ∈ D.sent := by
  cases hs
  exact List.mem_append_right _ (by simp)

structure Execution (α : Type*) (n : ℕ) [DecidableEq α] where
  state : ℕ → Config α n
  action : ℕ → Action α n
  start : state 0 = initial α n
  step : ∀ t, Step (state t) (action t) (state (t + 1))

theorem Execution.reachable (E : Execution α n) (t : ℕ) : Reachable (E.state t) := by
  induction t with
  | zero => rw [E.start]; exact Reachable.initial
  | succ t ih => exact Reachable.step ih (E.step t)

theorem Execution.payload_mono (E : Execution α n) (p : NodeId n) {t u : ℕ} (h : t ≤ u) :
    ((E.state t).node p).payload ≤ ((E.state u).node p).payload := by
  induction u, h using Nat.le_induction with
  | base => exact le_rfl
  | succ u _ ih => exact le_trans ih (step_payload_mono (E.step u) p)

theorem Execution.issued_mono (E : Execution α n) {t u : ℕ} (h : t ≤ u)
    {a : Update α n} (ha : a ∈ (E.state t).issued) : a ∈ (E.state u).issued := by
  induction u, h using Nat.le_induction with
  | base => exact ha
  | succ u _ ih => exact step_issued (E.step u) a ih

theorem Execution.sent_mono (E : Execution α n) {t u : ℕ} (h : t ≤ u)
    {S : Snapshot α n} (hs : S ∈ (E.state t).sent) : S ∈ (E.state u).sent := by
  induction u, h using Nat.le_induction with
  | base => exact hs
  | succ u _ ih => exact step_sent (E.step u) S ih

/-- Current-snapshot sends are continuously enabled. -/
def FairSend (E : Execution α n) : Prop := ∀ p t, ∃ u ≥ t, E.action u = .send p

/-- Reliable availability is modeled by the persistent authentic sent archive.
Weak fairness applies to each recipient and continuously useful snapshot. -/
def WeakFairness (E : Execution α n) : Prop :=
  ∀ p S t, (∀ u ≥ t, S ∈ (E.state u).sent ∧ ¬ S.payload ≤ ((E.state u).node p).payload) →
    ∃ u ≥ t, E.action u = .receive p S

theorem packet_eventually_subsumed (E : Execution α n) (fair : WeakFairness E)
    {S : Snapshot α n} {t : ℕ} (hs : S ∈ (E.state t).sent) (p : NodeId n) :
    ∃ u ≥ t, S.payload ≤ ((E.state u).node p).payload := by
  by_contra hn
  push Not at hn
  obtain ⟨u, hu, he⟩ := fair p S t (fun u hu => ⟨E.sent_mono hu hs, hn u hu⟩)
  have hstep := E.step u
  rw [he] at hstep
  exact hn (u + 1) (by omega) (received_packet_le hstep)

theorem eventual_dissemination (E : Execution α n) (sending : FairSend E)
    (fair : WeakFairness E) {a : Update α n} {t : ℕ} (ha : a ∈ (E.state t).issued)
    (p : NodeId n) : ∃ u ≥ t, effect a ≤ ((E.state u).node p).payload := by
  obtain ⟨v, hv, he⟩ := sending a.id.2 t
  have hs := E.step v
  rw [he] at hs
  obtain ⟨u, hu, hsub⟩ := packet_eventually_subsumed E fair (sent_packet_mem hs) p
  refine ⟨u, by omega, ?_⟩
  exact le_trans ((reachable_invariant (E.reachable v)).covered a (E.issued_mono hv ha)) hsub

def NoUpdatesAfter (E : Execution α n) (T : ℕ) : Prop :=
  ∀ t ≥ T, ∀ p x, E.action t ≠ .add p x ∧ E.action t ≠ .remove p x

theorem no_update_issued {C D : Config α n} {a : Action α n} (hs : Step C a D)
    (hn : ∀ p x, a ≠ .add p x ∧ a ≠ .remove p x) : D.issued = C.issued := by
  cases hs with
  | idle => rfl
  | send => rfl
  | receive => rfl
  | add p x => exact ((hn p x).1 rfl).elim
  | remove p x => exact ((hn p x).2 rfl).elim

theorem issued_stable (E : Execution α n) {T : ℕ} (stop : NoUpdatesAfter E T)
    {u : ℕ} (hu : T ≤ u) : (E.state u).issued = (E.state T).issued := by
  induction u, hu using Nat.le_induction with
  | base => rfl
  | succ u hu ih =>
    exact (no_update_issued (E.step u) (stop u hu)).trans ih

theorem finite_history_bound (E : Execution α n) (p : NodeId n) (H : List (Update α n))
    (h : ∀ a ∈ H, ∃ t, effect a ≤ ((E.state t).node p).payload) :
    ∃ t, ∀ a ∈ H, effect a ≤ ((E.state t).node p).payload := by
  induction H with
  | nil => exact ⟨0, by simp⟩
  | cons a H ih =>
    obtain ⟨v, hv⟩ := h a (by simp)
    obtain ⟨u, hu⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max v u, ?_⟩
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact le_trans hv (E.payload_mono p (le_max_left _ _))
    · exact le_trans (hu b hb) (E.payload_mono p (le_max_right _ _))

/-- A finite uniform stabilization time is derived from fairness and quiescence. -/
theorem eventual_stabilization (E : Execution α n) (sending : FairSend E)
    (fair : WeakFairness E) (T : ℕ) (stop : NoUpdatesAfter E T) :
    ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).payload = summarize (E.state T).issued := by
  classical
  have each (p : NodeId n) :
      ∃ t, ∀ a ∈ (E.state T).issued, effect a ≤ ((E.state t).node p).payload := by
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
  apply le_antisymm
  · rw [state_is_join_history (E.reachable u) p]
    apply summary_le
    intro a ha
    apply effect_le_summary
    rw [← issued_stable E stop hT]
    exact (reachable_invariant (E.reachable u)).histories p a ha
  · exact summary_le (fun a ha => le_trans (cover p a ha) (E.payload_mono p hp))

/-- The global history join is exactly the finite supremum of current replicas. -/
theorem global_join_exact {C : Config α n} (hc : Reachable C) :
    summarize C.issued = Finset.univ.sup (fun p => (C.node p).payload) := by
  classical
  apply le_antisymm
  · apply summary_le
    intro a ha
    exact le_trans ((reachable_invariant hc).covered a ha)
      (Finset.le_sup (f := fun p => (C.node p).payload) (Finset.mem_univ a.id.2))
  · apply Finset.sup_le
    intro p _
    rw [state_is_join_history hc p]
    exact summary_le (fun a ha => effect_le_summary ((reachable_invariant hc).histories p a ha))

namespace BroadcastBridge
abbrev MessageId (n : ℕ) := DistributedCausalBroadcast.MessageId n
abbrev CBExecution (n : ℕ) := DistributedCausalBroadcast.Execution n

/-- Immutable message-ID binding to snapshots; transport clocks are unchanged. -/
def replay (packet : MessageId n → ORSetState α n) : List (MessageId n) → ORSetState α n
  | [] => ⊥
  | m :: ids => packet m ⊔ replay packet ids

theorem replay_append (packet : MessageId n → ORSetState α n) (xs ys : List (MessageId n)) :
    replay packet (xs ++ ys) = replay packet xs ⊔ replay packet ys := by
  induction xs with
  | nil => simp [replay]
  | cons m xs ih => simp [replay, ih, sup_assoc]

theorem packet_le_replay (packet : MessageId n → ORSetState α n) {ids : List (MessageId n)}
    {m : MessageId n} (hm : m ∈ ids) : packet m ≤ replay packet ids := by
  induction ids with
  | nil => simp at hm
  | cons a ids ih =>
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_sup_left
    · exact le_trans (ih hm) le_sup_right

theorem replay_le (packet : MessageId n → ORSetState α n) {ids : List (MessageId n)}
    {S : ORSetState α n} (h : ∀ m ∈ ids, packet m ≤ S) : replay packet ids ≤ S := by
  induction ids with
  | nil => exact bot_le
  | cons a ids ih => exact sup_le (h a (by simp)) (ih (fun m hm => h m (by simp [hm])))

theorem replay_same_messages (packet : MessageId n → ORSetState α n)
    {xs ys : List (MessageId n)} (h : ∀ m, m ∈ xs ↔ m ∈ ys) :
    replay packet xs = replay packet ys := by
  exact le_antisymm (replay_le _ (fun m hm => packet_le_replay _ ((h m).1 hm)))
    (replay_le _ (fun m hm => packet_le_replay _ ((h m).2 hm)))

def adapter (E : CBExecution n) (packet : MessageId n → ORSetState α n)
    (t : ℕ) (p : NodeId n) : ORSetState α n := replay packet ((E.state t).node p).log

theorem adapter_step (E : CBExecution n) (packet : MessageId n → ORSetState α n)
    (t : ℕ) (p : NodeId n) :
    adapter E packet (t + 1) p = adapter E packet t p ⊔
      replay packet (DistributedCausalBroadcast.deliveries (E.state t) (E.action t) p) := by
  unfold adapter
  rw [DistributedCausalBroadcast.step_log (E.step t), replay_append]

theorem adapter_invariant (E : CBExecution n) (packet : MessageId n → ORSetState α n)
    (valid : ∀ m, Invariant (packet m)) (t : ℕ) (p : NodeId n) :
    Invariant (adapter E packet t p) := by
  unfold adapter
  generalize ((E.state t).node p).log = ids
  induction ids with
  | nil => exact Finset.empty_subset _
  | cons m ids ih => exact invariant_merge (valid m) ih

/-- General finite-batch bridge: all packets lie below the target and an already
announced finite batch covers it. Eventual application follows from CBcast liveness. -/
theorem causal_broadcast_batch_bridge (G : ORSetState α n)
    (packet : MessageId n → ORSetState α n) (valid : ∀ m, packet m ≤ G)
    (E : CBExecution n) (reliable : DistributedCausalBroadcast.ReliableArrival E)
    (fair : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (coverage : G ≤ replay packet ((E.state T).archive.map fun r => r.message.id)) :
    ∃ B, ∀ u ≥ B, ∀ p, adapter E packet u p = G := by
  classical
  have live := DistributedCausalBroadcast.liveness_under_fairness E reliable fair
  let S := ((E.state T).archive.map fun r => r.message.id).toFinset
  have each (p : NodeId n) : ∃ t, ∀ m ∈ S, m ∈ ((E.state t).node p).log := by
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
  have hp : time p ≤ u := le_trans (Finset.le_sup (f := time) (Finset.mem_univ p)) hu
  apply le_antisymm (replay_le _ (fun m _ => valid m))
  apply le_trans coverage
  apply replay_le
  intro m hm
  exact packet_le_replay packet
    (E.log_mono p hp (cover p m (List.mem_toFinset.mpr hm)))

def checkpointPacket (C : Config α n) (m : MessageId n) : ORSetState α n :=
  (C.node m.sender).payload

def CheckpointAnnounced (E : CBExecution n) (T : ℕ) : Prop :=
  ∀ p, ∃ r ∈ (E.state T).archive, r.message.id.sender = p

theorem causal_broadcast_bridge {C : Config α n} (hc : Reachable C) (E : CBExecution n)
    (reliable : DistributedCausalBroadcast.ReliableArrival E)
    (fair : DistributedCausalBroadcast.WeakFairness E) (T : ℕ)
    (announced : CheckpointAnnounced E T) :
    ∃ B, ∀ u ≥ B, ∀ p, adapter E (checkpointPacket C) u p = summarize C.issued := by
  refine causal_broadcast_batch_bridge (summarize C.issued) (checkpointPacket C) ?_
    E reliable fair T ?_
  · intro m
    rw [checkpointPacket, state_is_join_history hc m.sender]
    exact summary_le (fun a ha => effect_le_summary ((reachable_invariant hc).histories _ a ha))
  · apply summary_le
    intro a ha
    obtain ⟨r, hr, he⟩ := announced a.id.2
    have hh := packet_le_replay (checkpointPacket C)
      (ids := (E.state T).archive.map fun r => r.message.id) (m := r.message.id)
      (List.mem_map.mpr ⟨r, hr, rfl⟩)
    apply le_trans ((reachable_invariant hc).covered a ha)
    simpa only [checkpointPacket, he] using hh
end BroadcastBridge

/-- Reachability helpers for concrete executions. -/
theorem reachable_add {C : Config α n} (h : Reachable C) (p : NodeId n) (x : α) :
    Reachable (add C p x) := Reachable.step h (.add p x)
theorem reachable_remove {C : Config α n} (h : Reachable C) (p : NodeId n) (x : α) :
    Reachable (erase C p x) := Reachable.step h (.remove p x)
theorem reachable_send {C : Config α n} (h : Reachable C) (p : NodeId n) :
    Reachable (send C p) := Reachable.step h (.send p)
theorem reachable_receive {C : Config α n} (h : Reachable C) (p : NodeId n)
    (S : Snapshot α n) (hs : S ∈ C.sent) : Reachable (receive C p S) :=
  Reachable.step h (.receive p S hs)

/-- A post-update snapshot includes that operation and only earlier observations. -/
def OperationSnapshot (a : Update α n) (S : Snapshot α n) : Prop :=
  a ∈ S.history ∧ ∀ r ∈ S.history, r = a ∨ HappensBefore r a

theorem commit_operation_snapshot (C : Config α n) (p : NodeId n) (k : Kind α n) :
    OperationSnapshot (nextUpdate C p k) ((commit C p k).node p).toSnapshot := by
  simp only [OperationSnapshot, commit, ↓reduceIte]
  refine ⟨List.mem_append_right _ (by simp), ?_⟩
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · right
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, rfl⟩)
  · exact Or.inl (List.mem_singleton.mp hr)

theorem removed_in_summary {H : List (Update α n)} {z : α × Tag n}
    (hz : z ∈ (summarize H).removed) : ∃ r ∈ H, z ∈ (effect r).removed := by
  induction H with
  | nil => simp at hz
  | cons r H ih =>
    rcases Finset.mem_union.mp hz with hz | hz
    · exact ⟨r, by simp, hz⟩
    · obtain ⟨b, hb, hz⟩ := ih hz
      exact ⟨b, List.mem_cons_of_mem _ hb, hz⟩

theorem removed_implies_cause {C : Config α n} (hc : Reachable C)
    {a : Update α n} {x : α} (ha : a ∈ C.issued)
    {S : Snapshot α n} (hs : S.payload = summarize S.history)
    (hist : ∀ r ∈ S.history, r ∈ C.issued) (hz : (x, a.id) ∈ S.payload.removed) :
    ∃ r ∈ S.history, HappensBefore a r := by
  rw [hs] at hz
  obtain ⟨r, hr, hz⟩ := removed_in_summary hz
  obtain ⟨b, hb, hid, _, hp⟩ := (reachable_invariant hc).removals r (hist r hr) _ hz
  have he := tag_uniqueness hc hb ha hid
  exact ⟨r, hr, by simpa only [he, HappensBefore] using hp⟩

/-- Full post-operation snapshots, including previously observed metadata, retain
an addition concurrent with the other update. All records belong to one valid run. -/
theorem concurrent_add_wins_snapshots {C : Config α n} (hc : Reachable C)
    {a b : Update α n} {x : α} (ha : a ∈ C.issued) (hb : b ∈ C.issued)
    (hk : a.kind = .add x) (concurrent : Concurrent a b)
    {S T : Snapshot α n} (sS : SoundSnapshot S) (sT : SoundSnapshot T)
    (hS : ∀ r ∈ S.history, r ∈ C.issued) (hT : ∀ r ∈ T.history, r ∈ C.issued)
    (oS : OperationSnapshot a S) (oT : OperationSnapshot b T) :
    contains x (S.payload ⊔ T.payload) := by
  have hmem : (x, a.id) ∈ S.payload.added := by
    rw [sS.1]
    exact (effect_le_summary oS.1).1 (by simp [effect, hk])
  refine ⟨a.id, Finset.mem_union_left _ hmem, ?_⟩
  intro hz
  rcases Finset.mem_union.mp hz with hz | hz
  · obtain ⟨r, hr, hcau⟩ := removed_implies_cause hc ha sS.1 hS hz
    rcases oS.2 r hr with rfl | hbefore
    · exact happens_before_irrefl hc ha hcau
    · exact happens_before_irrefl hc ha (happens_before_trans hc (hS r hr) ha hcau hbefore)
  · obtain ⟨r, hr, hcau⟩ := removed_implies_cause hc ha sT.1 hT hz
    rcases oT.2 r hr with rfl | hbefore
    · exact concurrent.2.1 hcau
    · exact concurrent.2.1 (happens_before_trans hc (hT r hr) hb hcau hbefore)

namespace Regression

def localAdd : Config ℕ 1 := add (initial ℕ 1) 0 7
def localRemove : Config ℕ 1 := erase localAdd 0 7
def localReadd : Config ℕ 1 := add localRemove 0 7

theorem reg_empty : ¬ contains (7 : ℕ) (⊥ : ORSetState ℕ 1) := by simp [contains]
theorem local_reachable : Reachable localAdd ∧ Reachable localRemove ∧ Reachable localReadd := by
  have h := reachable_add (Reachable.initial (α := ℕ) (n := 1)) 0 7
  have hr := reachable_remove h 0 7
  exact ⟨h, hr, reachable_add hr 0 7⟩

theorem reg_local_sequence : contains 7 (localAdd.node 0).payload ∧
    ¬ contains 7 (localRemove.node 0).payload ∧ contains 7 (localReadd.node 0).payload := by
  refine ⟨operational_readd Reachable.initial 0 7, ?_, operational_readd local_reachable.2.1 0 7⟩
  rw [localRemove, remove_payload]
  exact fun h =>
    ((observed_remove_exact 7 7 (1, (0 : Fin 1)) (localAdd.node 0).payload).2.mp h).2 rfl

/-- Both replicas observe the old tag. Replica 0 removes it while replica 1
independently adds a new tag for the same element. -/
def old : Config ℕ 3 := add (initial ℕ 3) 0 7
def oldPacket : Snapshot ℕ 3 := (old.node 0).toSnapshot
def shared : Config ℕ 3 := receive (send old 0) 1 oldPacket
def removed : Config ℕ 3 := erase shared 0 7
def concurrent : Config ℕ 3 := add removed 1 7
def removePacket : Snapshot ℕ 3 := (concurrent.node 0).toSnapshot
def addPacket : Snapshot ℕ 3 := (concurrent.node 1).toSnapshot
def transmitted : Config ℕ 3 := send (send concurrent 0) 1
def removeFirst : Config ℕ 3 := receive (receive transmitted 2 removePacket) 2 addPacket
def addFirst : Config ℕ 3 := receive (receive transmitted 2 addPacket) 2 removePacket

theorem shared_reachable : Reachable shared :=
  reachable_receive (reachable_send (reachable_add Reachable.initial 0 7) 0) 1 oldPacket
    (by simp [send, oldPacket, old])
theorem concurrent_reachable : Reachable concurrent :=
  reachable_add (reachable_remove shared_reachable 0 7) 1 7
theorem transmitted_reachable : Reachable transmitted :=
  reachable_send (reachable_send concurrent_reachable 0) 1

theorem both_orders_reachable : Reachable removeFirst ∧ Reachable addFirst := by
  constructor
  · exact reachable_receive (reachable_receive transmitted_reachable 2 removePacket
      (by simp [transmitted, send, removePacket])) 2 addPacket
      (by simp [receive, transmitted, send, addPacket])
  · exact reachable_receive (reachable_receive transmitted_reachable 2 addPacket
      (by simp [transmitted, send, addPacket])) 2 removePacket
      (by simp [receive, transmitted, send, removePacket])

def a : Update ℕ 3 := nextUpdate removed 1 (.add 7)
def r : Update ℕ 3 := nextUpdate shared 0 (.remove 7 (observed 7 (shared.node 0).payload))

theorem reg_independent_causality : Concurrent a r := by
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hn : a.id ≠ r.id := by decide +kernel
    exact hn (congrArg Update.id he)
  · unfold HappensBefore; decide +kernel
  · unfold HappensBefore; decide +kernel

theorem reg_concurrent_orders :
    (removeFirst.node 2).payload = (addFirst.node 2).payload ∧
    (7, (1, (1 : Fin 3))) ∈ (removeFirst.node 2).payload.added ∧
    (7, (1, (1 : Fin 3))) ∉ (removeFirst.node 2).payload.removed := by
  constructor
  · apply ORSetState.ext <;> decide +kernel
  · decide +kernel

theorem reg_add_wins : contains 7 (removeFirst.node 2).payload ∧
    contains 7 (addFirst.node 2).payload := by
  refine ⟨⟨(1, 1), reg_concurrent_orders.2⟩, ?_⟩
  rw [← reg_concurrent_orders.1]
  exact ⟨(1, 1), reg_concurrent_orders.2⟩

theorem reg_partial_remove :
    (7, (1, (0 : Fin 3))) ∈ (removeFirst.node 2).payload.removed ∧
    (7, (1, (1 : Fin 3))) ∉ (removeFirst.node 2).payload.removed := by decide +kernel

theorem reg_duplicate :
    ((receive removeFirst 2 removePacket).node 2).payload = (removeFirst.node 2).payload := by
  apply ORSetState.ext <;> decide +kernel

theorem reg_late_snapshot :
    ((receive removeFirst 2 oldPacket).node 2).payload = (removeFirst.node 2).payload := by
  apply ORSetState.ext <;> decide +kernel

/-- Garbage collection here discards the removed pairs as well as their tombstones,
so resurrection occurs only when the stale pre-removal snapshot arrives. -/
def unsafeGC (S : ORSetState α n) : ORSetState α n := ⟨S.added \ S.removed, ∅⟩

def oldState : ORSetState ℕ 1 := ⟨{(7, (1, 0))}, ∅⟩
def deletedState : ORSetState ℕ 1 := remove 7 oldState

theorem counterexample_tag_reuse :
    ¬ contains 7 (addTag 7 (1, 0) deletedState) := by
  have he : addTag 7 (1, 0) deletedState = deletedState := by
    apply ORSetState.ext <;> decide +kernel
  rw [he, deletedState]
  exact fun h => ((observed_remove_exact 7 7 (1, (0 : Fin 1)) oldState).2.mp h).2 rfl

theorem gc_empty : unsafeGC deletedState = ⊥ := by decide +kernel

theorem counterexample_tombstone_gc :
    ¬ contains 7 deletedState ∧ ¬ contains 7 (unsafeGC deletedState) ∧
    contains 7 (unsafeGC deletedState ⊔ oldState) ∧
    ¬ contains 7 (deletedState ⊔ oldState) := by
  have hd : ¬ contains 7 deletedState := by
    rw [deletedState]
    exact fun h => ((observed_remove_exact 7 7 (1, (0 : Fin 1)) oldState).2.mp h).2 rfl
  refine ⟨hd, ?_, ?_, ?_⟩
  · rw [gc_empty]; exact reg_empty
  · rw [gc_empty, bot_sup_eq]
    exact ⟨(1, 0), by decide +kernel, by decide +kernel⟩
  · have he : deletedState ⊔ oldState = deletedState := by decide +kernel
    rw [he]; exact hd

/-- Visible membership is not monotone even though both metadata components are. -/
theorem visible_not_monotone : oldState ≤ deletedState ∧ contains 7 oldState ∧
    ¬ contains 7 deletedState := by
  refine ⟨?_, ⟨(1, 0), by decide +kernel, by decide +kernel⟩, counterexample_tombstone_gc.1⟩
  constructor <;> decide +kernel

end Regression

structure DistributedCRDTORSetSuite : Prop where
  algebra : ∀ (α : Type) [DecidableEq α] n (S T U : ORSetState α n),
    merge S T = merge T S ∧ merge (merge S T) U = merge S (merge T U) ∧ merge S S = S
  invariant : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C →
    ∀ p, Invariant (C.node p).payload
  unique : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C →
    ∀ a ∈ C.issued, ∀ b ∈ C.issued, a.id = b.id → a = b
  remove_exact : ∀ (α : Type) [DecidableEq α] n (x y : α) (S : ORSetState α n),
    contains y (remove x S) ↔ contains y S ∧ y ≠ x
  add_wins : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C →
    ∀ a ∈ C.issued, ∀ b ∈ C.issued, ∀ x, a.kind = .add x → Concurrent a b →
    contains x (effect a ⊔ effect b)
  no_resurrection : ∀ (α : Type) [DecidableEq α] n (S T : ORSetState α n) x t,
    (x, t) ∈ S.removed → (x, t) ∈ (S ⊔ T).removed
  readd : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C → ∀ p x,
    contains x ((add C p x).node p).payload
  payload : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C → ∀ p,
    (C.node p).payload = summarize (C.node p).history
  convergence : ∀ (α : Type) [DecidableEq α] n (C D : Config α n),
    Reachable C → Reachable D → ∀ p q,
    (∀ a, a ∈ (C.node p).history ↔ a ∈ (D.node q).history) → (C.node p).payload = (D.node q).payload
  dissemination : ∀ (α : Type) [DecidableEq α] n (E : Execution α n), FairSend E → WeakFairness E →
    ∀ t a, a ∈ (E.state t).issued → ∀ p, ∃ u ≥ t, effect a ≤ ((E.state u).node p).payload
  stabilization : ∀ (α : Type) [DecidableEq α] n (E : Execution α n), FairSend E → WeakFairness E →
    ∀ T, NoUpdatesAfter E T →
      ∃ B ≥ T, ∀ u ≥ B, ∀ p, ((E.state u).node p).payload = summarize (E.state T).issued
  broadcast : ∀ (α : Type) [DecidableEq α] n (C : Config α n), Reachable C →
    ∀ E : BroadcastBridge.CBExecution n, DistributedCausalBroadcast.ReliableArrival E →
      DistributedCausalBroadcast.WeakFairness E → ∀ T, BroadcastBridge.CheckpointAnnounced E T →
        ∃ B, ∀ u ≥ B, ∀ p,
          BroadcastBridge.adapter E (BroadcastBridge.checkpointPacket C) u p = summarize C.issued
  guards : ¬ contains 7 (addTag 7 (1, 0) Regression.deletedState) ∧
    contains 7 (Regression.unsafeGC Regression.deletedState ⊔ Regression.oldState) ∧
    ¬ contains 7 (Regression.deletedState ⊔ Regression.oldState)
  regressions : Reachable Regression.removeFirst ∧ Reachable Regression.addFirst ∧
    Concurrent Regression.a Regression.r ∧ contains 7 (Regression.removeFirst.node 2).payload ∧
    contains 7 (Regression.addFirst.node 2).payload

theorem distributed_crdt_orset_master_suite : DistributedCRDTORSetSuite where
  algebra := fun _ _ _ S T U => ⟨merge_comm S T, merge_assoc S T U, merge_idem S⟩
  invariant := fun _ _ _ _ hc => reachable_metadata_invariant hc
  unique := fun _ _ _ _ hc _ ha _ hb he => tag_uniqueness hc ha hb he
  remove_exact := fun _ _ _ x y S => by
    simp only [contains, remove, Finset.mem_union, observed, Finset.mem_filter]
    constructor
    · rintro ⟨t, ha, hn⟩
      exact ⟨⟨t, ha, fun h => hn (Or.inl h)⟩,
        fun he => hn (Or.inr ⟨ha, he, fun h => hn (Or.inl h)⟩)⟩
    · rintro ⟨⟨t, ha, hn⟩, hne⟩
      exact ⟨t, ha, fun h => h.elim hn (fun h => hne h.2.1)⟩
  add_wins := fun _ _ _ _ hc _ ha _ hb _ hk hcon => concurrent_add_wins hc ha hb hk hcon
  no_resurrection := fun _ _ _ _ T _ _ h => removed_tag_never_resurrects h T
  readd := fun _ _ _ _ hc => operational_readd hc
  payload := fun _ _ _ _ hc => state_is_join_history hc
  convergence := fun _ _ _ _ _ hc hd => sec_strong_convergence hc hd
  dissemination := fun _ _ _ E sending fair _ _ ha p => eventual_dissemination E sending fair ha p
  stabilization := fun _ _ _ => eventual_stabilization
  broadcast := fun _ _ _ _ hc => BroadcastBridge.causal_broadcast_bridge hc
  guards := ⟨Regression.counterexample_tag_reuse, Regression.counterexample_tombstone_gc.2.2⟩
  regressions := ⟨Regression.both_orders_reachable.1, Regression.both_orders_reachable.2,
    Regression.reg_independent_causality, Regression.reg_add_wins⟩

end DistributedCRDTORSet
