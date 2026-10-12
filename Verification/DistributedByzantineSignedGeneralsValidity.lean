/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedByzantineThreeGeneralsOralImpossibility
import Mathlib.Data.List.Nodup

/-!
# Synchronous signed Byzantine broadcast

Ideal signatures are governed by a derivation system backed by an operational
issuance ledger. Honest views are updated only from round-length-valid chains.
This is a round-indexed signed-chain implementation, with decisions at f + 1.
-/

namespace DistributedByzantineSignedGeneralsValidity

abbrev Order := Fin 2
abbrev Node (n : ℕ) := Fin n

structure SignedChain (n : ℕ) where
  value : Order
  path : List (Node n)
  deriving DecidableEq

def SignedChain.append (c : SignedChain n) (i : Node n) : SignedChain n :=
  ⟨c.value, c.path ++ [i]⟩

structure Parameters (n : ℕ) where
  commander : Node n
  faults : Finset (Node n)
  bound : ℕ
  fault_bound : faults.card ≤ bound
  population : bound + 2 ≤ n
  command : Order

def HonestLieutenant (P : Parameters n) (i : Node n) : Prop :=
  i ∉ P.faults ∧ i ≠ P.commander

instance (P : Parameters n) (i : Node n) : Decidable (HonestLieutenant P i) :=
  inferInstanceAs (Decidable (_ ∧ _))

def ValidChain (P : Parameters n) (c : SignedChain n) (r : ℕ) : Prop :=
  c.path.head? = some P.commander ∧ c.path.Nodup ∧ c.path.length = r

instance (P : Parameters n) (c : SignedChain n) (r : ℕ) : Decidable (ValidChain P c r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

structure Config (n : ℕ) where
  round : ℕ
  views : Node n → Finset Order
  issued : Finset (SignedChain n)
  outbound : Node n → Finset (SignedChain n)

/-- Empty public payloads can be extended with corrupted signatures freely.
An honest extension must already have been issued by the protocol. Each extension
binds the value and the entire preceding signer prefix. -/
inductive Derivable (P : Parameters n) (ledger : Finset (SignedChain n)) :
    SignedChain n → Prop where
  | empty (v) : Derivable P ledger ⟨v, []⟩
  | corrupt {c} (hc : Derivable P ledger c) (i) (hi : i ∈ P.faults) :
      Derivable P ledger (c.append i)
  | honest {c} (hc : Derivable P ledger c) (i) (hi : i ∉ P.faults)
      (issued : c.append i ∈ ledger) : Derivable P ledger (c.append i)

/-- Derivations can only mention an honest signer after a matching prefix was issued. -/
theorem derivable_honest_prefix {P : Parameters n} {ledger : Finset (SignedChain n)}
    {c : SignedChain n} (hc : Derivable P ledger c) (i : Node n)
    (hi : i ∉ P.faults) (hm : i ∈ c.path) :
    ∃ pre : SignedChain n, pre.append i ∈ ledger ∧
      pre.value = c.value ∧ (pre.append i).path.IsPrefix c.path := by
  induction hc with
  | empty v => simp at hm
  | @corrupt c hc j hj ih =>
    simp only [SignedChain.append, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · obtain ⟨p, hp, hv, hl⟩ := ih hm
      exact ⟨p, hp, hv, hl.trans (List.prefix_append _ _)⟩
    · exact (hi hj).elim
  | @honest c hc j hj hs ih =>
    simp only [SignedChain.append, List.mem_append, List.mem_singleton] at hm
    rcases hm with hm | rfl
    · obtain ⟨p, hp, hv, hl⟩ := ih hm
      exact ⟨p, hp, hv, hl.trans (List.prefix_append _ _)⟩
    · exact ⟨c, hs, rfl, ⟨[], by simp⟩⟩

def rootChain (P : Parameters n) : SignedChain n := ⟨P.command, [P.commander]⟩

def initial (P : Parameters n) : Config n where
  round := 0
  views := fun _ => ∅
  issued := if P.commander ∉ P.faults then {rootChain P} else ∅
  outbound := fun j => if P.commander ∉ P.faults ∧ j ≠ P.commander
    then {rootChain P} else ∅

def accepted (P : Parameters n) (s : Config n) (input : Node n → Finset (SignedChain n))
    (i : Node n) : Finset (SignedChain n) :=
  (input i).filter (fun c => ValidChain P c (s.round + 1))

def Signable (P : Parameters n) (s : Config n) (i : Node n) (c : SignedChain n) : Prop :=
  HonestLieutenant P i ∧ c.value ∉ s.views i ∧ i ∉ c.path ∧ s.round + 1 ≤ P.bound

instance (P : Parameters n) (s : Config n) (i : Node n) (c : SignedChain n) :
    Decidable (Signable P s i c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def newSignatures (P : Parameters n) (s : Config n)
    (input : Node n → Finset (SignedChain n)) : Finset (SignedChain n) :=
  Finset.univ.biUnion fun i => ((accepted P s input i).filter (Signable P s i)).image
    (fun c => c.append i)

def advance (P : Parameters n) (s : Config n)
    (input : Node n → Finset (SignedChain n)) : Config n where
  round := s.round + 1
  views := fun i => s.views i ∪ (accepted P s input i).image SignedChain.value
  issued := s.issued ∪ newSignatures P s input
  outbound := fun j => (newSignatures P s input).filter (fun c => j ∉ c.path)

/-- Reliable honest delivery and ideal signature availability constrain the
network, not a safety invariant or an agreement oracle. Byzantine deliveries
may otherwise be omitted, duplicated, delayed or recipient-specific. -/
structure Delivery (P : Parameters n) (s : Config n)
    (input : Node n → Finset (SignedChain n)) : Prop where
  reliable : ∀ j, HonestLieutenant P j → s.outbound j ⊆ input j
  authentic : ∀ j, HonestLieutenant P j → ∀ c ∈ input j, Derivable P s.issued c

/-- A concrete finite execution consists of actual delivery batches. -/
inductive Run (P : Parameters n) : Config n → Prop where
  | initial : Run P (initial P)
  | step {s} (past : Run P s) (input) (delivery : Delivery P s input)
      (time : s.round ≤ P.bound) : Run P (advance P s input)

@[simp] theorem mem_newSignatures {P : Parameters n} {s : Config n} {input} {d} :
    d ∈ newSignatures P s input ↔ ∃ i c, c ∈ accepted P s input i ∧
      Signable P s i c ∧ c.append i = d := by
  simp [newSignatures, and_assoc]

theorem valid_append {P : Parameters n} {c : SignedChain n} {r : ℕ}
    (hc : ValidChain P c r) (i : Node n) (hi : i ∉ c.path) :
    ValidChain P (c.append i) (r + 1) := by
  obtain ⟨head, nd, len⟩ := hc
  constructor
  · cases hp : c.path with
    | nil => simp [hp] at head
    | cons a l => simpa [SignedChain.append, hp] using head
  · exact ⟨by simpa [SignedChain.append] using nd.concat hi,
      by simp [SignedChain.append, len]⟩

theorem views_monotone_step (P : Parameters n) (s : Config n) (input) (i : Node n) :
    s.views i ⊆ (advance P s input).views i := Finset.subset_union_left

theorem accepted_in_next {P : Parameters n} {s : Config n} {input} {i} {c}
    (hc : c ∈ accepted P s input i) : c.value ∈ (advance P s input).views i := by
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨c, hc, rfl⟩)

/-- Every issued value has already reached each honest lieutenant, or is in
that lieutenant's reliable next-round mailbox. This invariant is proved below. -/
structure Invariant (P : Parameters n) (s : Config n) : Prop where
  pending_valid : ∀ j c, c ∈ s.outbound j → ValidChain P c (s.round + 1)
  issued_spread : ∀ c ∈ s.issued, ∀ j, HonestLieutenant P j →
    c.value ∈ s.views j ∨ ∃ d ∈ s.outbound j, d.value = c.value
  issued_valid : ∀ c ∈ s.issued, c.path.head? = some P.commander
  honest_command : P.commander ∉ P.faults → ∀ c ∈ s.issued, c.value = P.command

theorem initial_invariant (P : Parameters n) : Invariant P (initial P) := by
  constructor
  · intro j c hc
    by_cases hC : P.commander ∉ P.faults
    · by_cases hj : j ≠ P.commander
      · have he : c = rootChain P := by simpa [initial, hC, hj] using hc
        subst c
        simp [initial, ValidChain, rootChain]
      · simp [initial, hj] at hc
    · simp [initial, hC] at hc
  · intro c hc j hj
    by_cases hC : P.commander ∉ P.faults
    · have he : c = rootChain P := by simpa [initial, hC] using hc
      subst c
      exact Or.inr ⟨rootChain P, by simp [initial, hC, hj.2], rfl⟩
    · simp [initial, hC] at hc
  · intro c hc
    by_cases hC : P.commander ∉ P.faults
    · have he : c = rootChain P := by simpa [initial, hC] using hc
      subst c
      rfl
    · simp [initial, hC] at hc
  · intro hC c hc
    have he : c = rootChain P := by simpa [initial, hC] using hc
    subst c
    rfl

theorem issued_reaches_next {P : Parameters n} {s : Config n} (hs : Invariant P s)
    {input} (hd : Delivery P s input) {c} (hc : c ∈ s.issued)
    {j} (hj : HonestLieutenant P j) : c.value ∈ (advance P s input).views j := by
  rcases hs.issued_spread c hc j hj with h | ⟨d, hm, he⟩
  · exact views_monotone_step P s input j h
  · rw [← he]
    exact accepted_in_next (Finset.mem_filter.mpr
      ⟨hd.reliable j hj hm, hs.pending_valid j d hm⟩)

theorem honest_on_chain_reaches_next {P : Parameters n} {s : Config n}
    (hs : Invariant P s) {input} (hd : Delivery P s input)
    {i c} (hi : HonestLieutenant P i) (hc : c ∈ accepted P s input i)
    {k} (hk : k ∉ P.faults) (hm : k ∈ c.path)
    {j} (hj : HonestLieutenant P j) : c.value ∈ (advance P s input).views j := by
  have auth := hd.authentic i hi c (Finset.mem_filter.mp hc).1
  obtain ⟨pre, hp, hv, _⟩ := derivable_honest_prefix auth k hk hm
  have h := issued_reaches_next hs hd hp hj
  simpa only [SignedChain.append, hv] using h

theorem advance_invariant {P : Parameters n} {s : Config n} (hs : Invariant P s)
    {input} (hd : Delivery P s input) : Invariant P (advance P s input) := by
  constructor
  · intro j d hd'
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hd'
    obtain ⟨i, c, hc, hsign, rfl⟩ := mem_newSignatures.mp hm
    exact valid_append (Finset.mem_filter.mp hc).2 i hsign.2.2.1
  · intro d hd' j hj
    rcases Finset.mem_union.mp hd' with hold | hnew
    · exact Or.inl (issued_reaches_next hs hd hold hj)
    · obtain ⟨i, c, hc, hsign, rfl⟩ := mem_newSignatures.mp hnew
      by_cases he : j = i
      · subst j
        exact Or.inl (by simpa only [SignedChain.append] using accepted_in_next hc)
      · by_cases hm : j ∈ c.path
        · exact Or.inl (honest_on_chain_reaches_next hs hd hsign.1 hc hj.1 hm hj)
        · right
          refine ⟨c.append i, ?_, rfl⟩
          apply Finset.mem_filter.mpr
          exact ⟨mem_newSignatures.mpr ⟨i, c, hc, hsign, rfl⟩,
            by simpa [SignedChain.append] using And.intro hm he⟩
  · intro d hd'
    rcases Finset.mem_union.mp hd' with hold | hnew
    · exact hs.issued_valid d hold
    · obtain ⟨i, c, hc, hsign, rfl⟩ := mem_newSignatures.mp hnew
      exact (valid_append (Finset.mem_filter.mp hc).2 i hsign.2.2.1).1
  · intro hC d hd'
    rcases Finset.mem_union.mp hd' with hold | hnew
    · exact hs.honest_command hC d hold
    · obtain ⟨i, c, hc, hsign, rfl⟩ := mem_newSignatures.mp hnew
      have head := (Finset.mem_filter.mp hc).2.1
      have hm : P.commander ∈ c.path := List.mem_of_mem_head? (by rw [head]; rfl)
      obtain ⟨pre, hp, hv, _⟩ := derivable_honest_prefix
        (hd.authentic i hsign.1 c (Finset.mem_filter.mp hc).1) P.commander hC hm
      exact hv.symm.trans (hs.honest_command hC (pre.append P.commander) hp)

theorem reachable_invariant {P : Parameters n} {s : Config n} (hr : Run P s) :
    Invariant P s := by
  induction hr with
  | initial => exact initial_invariant P
  | step past input hd time ih => exact advance_invariant ih hd

theorem chain_pigeonhole_honest_signer (P : Parameters n) (path : List (Node n))
    (hd : path.Nodup) (hl : path.length = P.bound + 1) :
    ∃ i ∈ path, i ∉ P.faults := by
  by_contra h
  push Not at h
  have sub : path.toFinset ⊆ P.faults := by
    intro i hi
    exact h i (List.mem_toFinset.mp hi)
  have card := Finset.card_le_card sub
  rw [List.toFinset_card_of_nodup hd, hl] at card
  have := P.fault_bound
  omega


/-- A full-length chain must contain an honest signer, whose issued prefix
already propagates this order through the reliable next-round delivery. -/
theorem order_propagation_final {P : Parameters n} {s : Config n} (hr : Run P s)
    {input} (hd : Delivery P s input) (ht : s.round = P.bound)
    {i c} (hi : HonestLieutenant P i) (hc : c ∈ accepted P s input i)
    {j} (hj : HonestLieutenant P j) : c.value ∈ (advance P s input).views j := by
  have valid := (Finset.mem_filter.mp hc).2
  obtain ⟨k, hk, hf⟩ := chain_pigeonhole_honest_signer P c.path valid.2.1
    (by simpa [ht] using valid.2.2)
  exact honest_on_chain_reaches_next (reachable_invariant hr) hd hi hc hf hk hj

def ViewInvariant (P : Parameters n) (s : Config n) : Prop :=
  ∀ i, HonestLieutenant P i → ∀ v ∈ s.views i, ∀ j, HonestLieutenant P j →
    v ∈ s.views j ∨ ∃ c ∈ s.outbound j, c.value = v

theorem advance_view_invariant {P : Parameters n} {s : Config n} (hr : Run P s)
    (hv : ViewInvariant P s) {input} (hd : Delivery P s input)
    (ht : s.round ≤ P.bound) : ViewInvariant P (advance P s input) := by
  intro i hi v hm j hj
  rcases Finset.mem_union.mp hm with hold | hnew
  · rcases hv i hi v hold j hj with h | ⟨c, hc, he⟩
    · exact Or.inl (views_monotone_step P s input j h)
    · left
      rw [← he]
      exact accepted_in_next (Finset.mem_filter.mpr
        ⟨hd.reliable j hj hc, (reachable_invariant hr).pending_valid j c hc⟩)
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hnew
    by_cases old : c.value ∈ s.views i
    · rcases hv i hi c.value old j hj with h | ⟨d, hm, he⟩
      · exact Or.inl (views_monotone_step P s input j h)
      · left
        rw [← he]
        exact accepted_in_next (Finset.mem_filter.mpr
          ⟨hd.reliable j hj hm, (reachable_invariant hr).pending_valid j d hm⟩)
    · by_cases last : s.round = P.bound
      · exact Or.inl (order_propagation_final hr hd last hi hc hj)
      · by_cases own : i ∈ c.path
        · exact Or.inl (honest_on_chain_reaches_next (reachable_invariant hr)
            hd hi hc hi.1 own hj)
        · have sign : Signable P s i c := ⟨hi, old, own, by omega⟩
          by_cases eq : j = i
          · subst j
            exact Or.inl (accepted_in_next hc)
          · by_cases onpath : j ∈ c.path
            · exact Or.inl (honest_on_chain_reaches_next (reachable_invariant hr)
                hd hi hc hj.1 onpath hj)
            · right
              refine ⟨c.append i, ?_, rfl⟩
              exact Finset.mem_filter.mpr
                ⟨mem_newSignatures.mpr ⟨i, c, hc, sign, rfl⟩,
                  by simpa [SignedChain.append] using And.intro onpath eq⟩

theorem reachable_view_invariant {P : Parameters n} {s : Config n} (hr : Run P s) :
    ViewInvariant P s := by
  induction hr with
  | initial => intro i hi v hm; simp [initial] at hm
  | step past input hd time ih => exact advance_view_invariant past ih hd time

/-- Known orders reach every honest lieutenant by the end of the next round.
Some recipients already know the order and need not receive a fresh chain. -/
theorem order_propagation_step {P : Parameters n} {s : Config n} (hr : Run P s)
    {input} (hd : Delivery P s input) {i v} (hi : HonestLieutenant P i)
    (hv : v ∈ s.views i) {j} (hj : HonestLieutenant P j) :
    v ∈ (advance P s input).views j := by
  rcases reachable_view_invariant hr i hi v hv j hj with h | ⟨c, hc, he⟩
  · exact views_monotone_step P s input j h
  · rw [← he]
    exact accepted_in_next (Finset.mem_filter.mpr
      ⟨hd.reliable j hj hc, (reachable_invariant hr).pending_valid j c hc⟩)

theorem outbound_before_deadline {P : Parameters n} {s : Config n} (hr : Run P s)
    {j c} (hc : c ∈ s.outbound j) : s.round ≤ P.bound := by
  cases hr with
  | initial => exact Nat.zero_le _
  | step past input hd time =>
    obtain ⟨hm, _⟩ := Finset.mem_filter.mp hc
    obtain ⟨i, parent, _, hsign, _⟩ := mem_newSignatures.mp hm
    exact hsign.2.2.2

theorem honest_views_identical {P : Parameters n} {s : Config n} (hr : Run P s)
    (ht : s.round = P.bound + 1) {i j} (hi : HonestLieutenant P i)
    (hj : HonestLieutenant P j) : s.views i = s.views j := by
  have sub : ∀ a b, HonestLieutenant P a → HonestLieutenant P b →
      s.views a ⊆ s.views b := by
    intro a b ha hb v hv
    rcases reachable_view_invariant hr a ha v hv b hb with h | ⟨c, hc, _⟩
    · exact h
    · have := outbound_before_deadline hr hc
      omega
  exact Finset.Subset.antisymm (sub i j hi hj) (sub j i hj hi)

def decide (view : Finset Order) : Order := if view = {1} then 1 else 0

@[simp] theorem decide_singleton (v : Order) : decide {v} = v := by
  fin_cases v <;> decide

theorem byzantine_signed_agreement {P : Parameters n} {s : Config n} (hr : Run P s)
    (ht : s.round = P.bound + 1) {i j} (hi : HonestLieutenant P i)
    (hj : HonestLieutenant P j) : decide (s.views i) = decide (s.views j) := by
  rw [honest_views_identical hr ht hi hj]

theorem honest_commander_only {P : Parameters n} {s : Config n} (hr : Run P s)
    (hC : P.commander ∉ P.faults) {j} (hj : HonestLieutenant P j) :
    ∀ v ∈ s.views j, v = P.command := by
  induction hr with
  | initial => intro v hv; simp [initial] at hv
  | @step s past input hd time ih =>
    intro v hv
    rcases Finset.mem_union.mp hv with hold | hnew
    · exact ih v hold
    · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hnew
      have head := (Finset.mem_filter.mp hc).2.1
      have hm : P.commander ∈ c.path := List.mem_of_mem_head? (by rw [head]; rfl)
      obtain ⟨pre, hp, hv, _⟩ := derivable_honest_prefix
        (hd.authentic j hj c (Finset.mem_filter.mp hc).1) P.commander hC hm
      exact hv.symm.trans ((reachable_invariant past).honest_command hC
        (pre.append P.commander) hp)

theorem round_zero_initial {P : Parameters n} {s : Config n} (hr : Run P s)
    (h : s.round = 0) : s = initial P := by
  cases hr with
  | initial => rfl
  | step past input hd time => simp [advance] at h

theorem honest_commander_received {P : Parameters n} {s : Config n} (hr : Run P s)
    (hC : P.commander ∉ P.faults) {j} (hj : HonestLieutenant P j)
    (ht : 0 < s.round) : P.command ∈ s.views j := by
  induction hr with
  | initial => simp [initial] at ht
  | @step s past input hd time ih =>
    by_cases hz : s.round = 0
    · have he := round_zero_initial past hz
      subst s
      have pending : rootChain P ∈ (initial P).outbound j := by simp [initial, hC, hj.2]
      exact accepted_in_next (Finset.mem_filter.mpr
        ⟨hd.reliable j hj pending, (initial_invariant P).pending_valid j _ pending⟩)
    · exact views_monotone_step P s input j (ih (Nat.pos_of_ne_zero hz))

theorem byzantine_signed_commander_validity {P : Parameters n} {s : Config n}
    (hr : Run P s) (ht : s.round = P.bound + 1) (hC : P.commander ∉ P.faults)
    {j} (hj : HonestLieutenant P j) :
    s.views j = {P.command} ∧ decide (s.views j) = P.command := by
  have he : s.views j = {P.command} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨honest_commander_received hr hC hj (by omega), honest_commander_only hr hC hj⟩
  exact ⟨he, by rw [he, decide_singleton]⟩


/-- Operational continuations retain the actual delivery/issuance rules. -/
inductive Continues (P : Parameters n) (start : Config n) : Config n → Prop where
  | refl : Continues P start start
  | step {s} (past : Continues P start s) (input) (hd : Delivery P s input)
      (ht : s.round ≤ P.bound) : Continues P start (advance P s input)

/-- An issuance witness includes the accepted parent, its signer, and a valid
execution continuation to the current configuration. The commander is the
explicit initial-signing exception: it need not receive its own order. -/
def OperationalOrigin (P : Parameters n) (s : Config n) (i : Node n)
    (c : SignedChain n) : Prop :=
  (i = P.commander ∧ P.commander ∉ P.faults ∧ c = rootChain P) ∨
  ∃ before input parent, Run P before ∧ Delivery P before input ∧
    before.round ≤ P.bound ∧ parent ∈ accepted P before input i ∧
    Signable P before i parent ∧ c = parent.append i ∧
    Continues P (advance P before input) s

theorem issued_operational_origin {P : Parameters n} {s : Config n} (hr : Run P s) :
    ∀ c ∈ s.issued, ∃ i, OperationalOrigin P s i c := by
  induction hr with
  | initial =>
    intro c hc
    by_cases hC : P.commander ∉ P.faults
    · have he : c = rootChain P := by simpa [initial, hC] using hc
      exact ⟨P.commander, Or.inl ⟨rfl, hC, he⟩⟩
    · simp [initial, hC] at hc
  | @step s past input hd ht ih =>
    intro c hc
    rcases Finset.mem_union.mp hc with hold | hnew
    · obtain ⟨i, ho⟩ := ih c hold
      refine ⟨i, ?_⟩
      rcases ho with hroot | ⟨before, batch, parent, hb, hd', ht', ha, hs, he, cont⟩
      · exact Or.inl hroot
      · exact Or.inr ⟨before, batch, parent, hb, hd', ht', ha, hs, he,
          Continues.step cont input hd ht⟩
    · obtain ⟨i, parent, ha, hs, he⟩ := mem_newSignatures.mp hnew
      exact ⟨i, Or.inr ⟨s, input, parent, past, hd, ht, ha, hs, he.symm,
        Continues.refl⟩⟩

theorem origin_last_signer {P : Parameters n} {s : Config n} {i c}
    (ho : OperationalOrigin P s i c) : c.path.getLast? = some i := by
  rcases ho with ⟨rfl, _, rfl⟩ | ⟨_, _, parent, _, _, _, _, _, rfl, _⟩
  · rfl
  · simp [SignedChain.append]

/-- Honest occurrences in any admissible message come from operational issuance,
including an actual accepted prefix for each honest non-commander signer. -/
theorem honest_signature_origin {P : Parameters n} {s : Config n} (hr : Run P s)
    {c} (hc : Derivable P s.issued c) {i} (hi : i ∉ P.faults) (hm : i ∈ c.path) :
    ∃ pre : SignedChain n, pre.value = c.value ∧
      (pre.append i).path.IsPrefix c.path ∧ OperationalOrigin P s i (pre.append i) := by
  obtain ⟨pre, hp, hv, hpre⟩ := derivable_honest_prefix hc i hi hm
  obtain ⟨j, ho⟩ := issued_operational_origin hr _ hp
  have hj : i = j := by simpa [SignedChain.append] using origin_last_signer ho
  subst j
  exact ⟨pre, hv, hpre, ho⟩

theorem Derivable.mono {P : Parameters n} {a b : Finset (SignedChain n)}
    (hab : a ⊆ b) {c} (hc : Derivable P a c) : Derivable P b c := by
  induction hc with
  | empty v => exact .empty v
  | corrupt h i hi ih => exact .corrupt ih i hi
  | honest h i hi hs ih => exact .honest ih i hi (hab hs)

theorem issued_derivable {P : Parameters n} {s : Config n} (hr : Run P s) :
    ∀ c ∈ s.issued, Derivable P s.issued c := by
  induction hr with
  | initial =>
    intro c hc
    by_cases hC : P.commander ∉ P.faults
    · have he : c = rootChain P := by simpa [initial, hC] using hc
      subst c
      exact .honest (.empty P.command) P.commander hC hc
    · simp [initial, hC] at hc
  | @step s past input hd ht ih =>
    intro c hc
    rcases Finset.mem_union.mp hc with hold | hnew
    · exact (ih c hold).mono Finset.subset_union_left
    · obtain ⟨i, parent, ha, hs, rfl⟩ := mem_newSignatures.mp hnew
      apply Derivable.honest
        ((hd.authentic i hs.1 parent (Finset.mem_filter.mp ha).1).mono
          Finset.subset_union_left) i hs.1.1
      exact Finset.mem_union_right _ (mem_newSignatures.mpr ⟨i, parent, ha, hs, rfl⟩)

theorem outbound_issued {P : Parameters n} {s : Config n} (hr : Run P s)
    {j c} (hc : c ∈ s.outbound j) : c ∈ s.issued := by
  cases hr with
  | initial =>
    by_cases hC : P.commander ∉ P.faults
    · by_cases hj : j ≠ P.commander
      · simpa [initial, hC, hj] using hc
      · simp [initial, hj] at hc
    · simp [initial, hC] at hc
  | step past input hd ht => exact Finset.mem_union_right _ (Finset.mem_filter.mp hc).1

theorem reliable_only_delivery {P : Parameters n} {s : Config n} (hr : Run P s) :
    Delivery P s s.outbound := by
  constructor
  · intro j hj; exact Finset.Subset.refl _
  · intro j hj c hc
    exact issued_derivable hr c (outbound_issued hr hc)

/-- No reachable nonterminal state is stuck; a silent Byzantine adversary is
always admissible. Honest transmissions suffice to complete the execution. -/
theorem run_extend (P : Parameters n) {s : Config n} (hr : Run P s)
    (ht : s.round ≤ P.bound) : ∃ next, Run P next ∧ next.round = s.round + 1 :=
  ⟨advance P s s.outbound, Run.step hr _ (reliable_only_delivery hr) ht, rfl⟩

theorem termination (P : Parameters n) (r : ℕ) (ht : r ≤ P.bound + 1) :
    ∃ s, Run P s ∧ s.round = r := by
  induction r with
  | zero => exact ⟨initial P, Run.initial, rfl⟩
  | succ r ih =>
    obtain ⟨s, hs, he⟩ := ih (by omega)
    obtain ⟨next, hn, hround⟩ := run_extend P hs (by omega)
    exact ⟨next, hn, by omega⟩

theorem run_horizon {P : Parameters n} {s : Config n} (hr : Run P s) :
    s.round ≤ P.bound + 1 := by
  cases hr with
  | initial => exact Nat.zero_le _
  | step past input hd ht => exact Nat.succ_le_succ ht

theorem honest_commander_wrong_root_rejected {P : Parameters n} {s : Config n}
    (hr : Run P s) (hC : P.commander ∉ P.faults) (v : Order) (hv : v ≠ P.command) :
    ¬ Derivable P s.issued ⟨v, [P.commander]⟩ := by
  intro h
  obtain ⟨pre, hp, he, _⟩ := derivable_honest_prefix h P.commander hC (by simp)
  have hh := (reachable_invariant hr).honest_command hC (pre.append P.commander) hp
  exact hv (he.symm.trans hh)


def BroadcastCorrect (P : Parameters n) : Prop :=
  (∃ s, Run P s ∧ s.round = P.bound + 1) ∧
  ∀ s, Run P s → s.round = P.bound + 1 →
    (∀ i j, HonestLieutenant P i → HonestLieutenant P j →
      decide (s.views i) = decide (s.views j)) ∧
    (P.commander ∉ P.faults → ∀ j, HonestLieutenant P j →
      s.views j = {P.command} ∧ decide (s.views j) = P.command)

theorem signed_broadcast_correct (P : Parameters n) : BroadcastCorrect P := by
  refine ⟨termination P (P.bound + 1) le_rfl, ?_⟩
  intro s hr ht
  exact ⟨fun _ _ hi hj => byzantine_signed_agreement hr ht hi hj,
    fun hC _ hj => byzantine_signed_commander_validity hr ht hC hj⟩

def threeParameters (F : Finset (Node 3)) (hf : F.card ≤ 1) (v : Order) : Parameters 3 :=
  ⟨0, F, 1, hf, by decide, v⟩

def toOralNode (i : Node 3) : DistributedByzantineThreeGeneralsOralImpossibility.Node :=
  if i = 0 then .commander else if i = 1 then .lieutenant1 else .lieutenant2

theorem topology_bijection : Function.Bijective toOralNode := by
  constructor
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [toOralNode]
  · intro p
    cases p with
    | commander => exact ⟨0, rfl⟩
    | lieutenant1 => exact ⟨1, rfl⟩
    | lieutenant2 => exact ⟨2, rfl⟩

/-- Same three roles and broadcast objectives, but different admissible network
transitions. No embedding of signed protocols into the unrestricted OM model
is claimed. The preceding rejection theorem isolates the signature restriction. -/
theorem bridge_to_oral_impossibility :
    (∀ T, ¬ ∃ (Msg State : Type)
      (P : DistributedByzantineThreeGeneralsOralImpossibility.Protocol T Msg State),
      DistributedByzantineThreeGeneralsOralImpossibility.Agreement P ∧
      DistributedByzantineThreeGeneralsOralImpossibility.CommanderValidity P) ∧
    (∀ (F : Finset (Node 3)) (hf : F.card ≤ 1) v,
      BroadcastCorrect (threeParameters F hf v)) :=
  ⟨DistributedByzantineThreeGeneralsOralImpossibility.no_correct_protocol,
    fun F hf v => signed_broadcast_correct (threeParameters F hf v)⟩

def faultyCommander : Parameters 3 := threeParameters {0} (by decide) 0

def signedRoot (v : Order) : SignedChain 3 := ⟨v, [0]⟩

def splitOrders (j : Node 3) : Finset (SignedChain 3) :=
  if j = 1 then {signedRoot 0} else if j = 2 then {signedRoot 1} else ∅

theorem faulty_root_derivable (s : Config 3) (v : Order) :
    Derivable faultyCommander s.issued (signedRoot v) :=
  Derivable.corrupt (Derivable.empty v) 0 (by decide)

theorem split_orders_delivery : Delivery faultyCommander (initial faultyCommander) splitOrders := by
  constructor
  · intro j hj
    simp [initial, faultyCommander, threeParameters]
  · intro j hj c hc
    by_cases h1 : j = 1
    · have he : c = signedRoot 0 := by simpa [splitOrders, h1] using hc
      subst c
      exact faulty_root_derivable _ _
    · by_cases h2 : j = 2
      · have he : c = signedRoot 1 := by simpa [splitOrders, h1, h2] using hc
        subst c
        exact faulty_root_derivable _ _
      · simp [splitOrders, h1, h2] at hc

def splitRoundOne : Config 3 := advance faultyCommander (initial faultyCommander) splitOrders

theorem split_round_one_reachable : Run faultyCommander splitRoundOne :=
  Run.step Run.initial splitOrders split_orders_delivery (by decide)

def splitRoundTwo : Config 3 := advance faultyCommander splitRoundOne splitRoundOne.outbound

theorem split_round_two_reachable : Run faultyCommander splitRoundTwo :=
  Run.step split_round_one_reachable _ (reliable_only_delivery split_round_one_reachable)
    (by decide)

theorem conflicting_orders_regression :
    splitRoundTwo.round = 2 ∧ splitRoundTwo.views 1 = {0, 1} ∧
    splitRoundTwo.views 2 = {0, 1} ∧ decide (splitRoundTwo.views 1) = 0 ∧
    decide (splitRoundTwo.views 2) = 0 := by decide

def emptyInput : Node n → Finset (SignedChain n) := fun _ => ∅

theorem silent_first_delivery :
    Delivery faultyCommander (initial faultyCommander) emptyInput := by
  constructor
  · intro j hj; simp [initial, faultyCommander, threeParameters]
  · intro j hj c hc; simp [emptyInput] at hc

def silentRoundOne : Config 3 := advance faultyCommander (initial faultyCommander) emptyInput

theorem silent_round_one_reachable : Run faultyCommander silentRoundOne :=
  Run.step Run.initial _ silent_first_delivery (by decide)

def silentRoundTwo : Config 3 := advance faultyCommander silentRoundOne silentRoundOne.outbound

theorem silent_round_two_reachable : Run faultyCommander silentRoundTwo :=
  Run.step silent_round_one_reachable _ (reliable_only_delivery silent_round_one_reachable)
    (by decide)

theorem silent_commander_regression :
    silentRoundTwo.views 1 = ∅ ∧ silentRoundTwo.views 2 = ∅ ∧
    decide (silentRoundTwo.views 1) = 0 ∧ decide (silentRoundTwo.views 2) = 0 := by decide

def lateOrder (j : Node 3) : Finset (SignedChain 3) :=
  if j = 1 then {signedRoot 1} else ∅

theorem late_order_delivery : Delivery faultyCommander silentRoundOne lateOrder := by
  constructor
  · intro j hj
    have empty : silentRoundOne.outbound j = ∅ := by fin_cases j <;> decide
    simp [empty]
  · intro j hj c hc
    by_cases h : j = 1
    · have he : c = signedRoot 1 := by simpa [lateOrder, h] using hc
      subst c
      exact faulty_root_derivable _ _
    · simp [lateOrder, h] at hc

/-- Relax only the final-round receipt filter: keep shape and distinct signers,
but accept chains of any length. No forwarding occurs after this last round. -/
def finalWithoutRoundFilter (P : Parameters n) (s : Config n)
    (input : Node n → Finset (SignedChain n)) : Config n :=
  { advance P s input with
    views := fun i => s.views i ∪ ((input i).filter (fun c =>
      c.path.head? = some P.commander ∧ c.path.Nodup)).image SignedChain.value }

theorem counterexample_without_round_filter :
    Run faultyCommander silentRoundOne ∧ silentRoundOne.round = faultyCommander.bound ∧
    Delivery faultyCommander silentRoundOne lateOrder ∧
    decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 1) = 1 ∧
    decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 2) = 0 ∧
    decide ((advance faultyCommander silentRoundOne lateOrder).views 1) = 0 ∧
    decide ((advance faultyCommander silentRoundOne lateOrder).views 2) = 0 := by
  exact ⟨silent_round_one_reachable, by decide, late_order_delivery,
    by decide, by decide, by decide, by decide⟩

theorem malformed_chains_rejected :
    ¬ ValidChain faultyCommander ⟨1, []⟩ 1 ∧
    ¬ ValidChain faultyCommander ⟨1, [0, 0]⟩ 2 ∧
    ¬ ValidChain faultyCommander ⟨1, [1]⟩ 1 ∧
    ¬ ValidChain faultyCommander (signedRoot 1) 2 := by decide

theorem repeated_packets_idempotent (P : Parameters n) (s : Config n)
    (input : Node n → Finset (SignedChain n)) :
    advance P s (fun i => input i ∪ input i) = advance P s input := by simp

def honestExample : Parameters 3 := threeParameters {2} (by decide) 1

def honestRoundOne : Config 3 := advance honestExample (initial honestExample)
  (initial honestExample).outbound

theorem honest_round_one_reachable : Run honestExample honestRoundOne :=
  Run.step Run.initial _ (reliable_only_delivery Run.initial) (by decide)

def honestRoundTwo : Config 3 := advance honestExample honestRoundOne honestRoundOne.outbound

theorem honest_round_two_reachable : Run honestExample honestRoundTwo :=
  Run.step honest_round_one_reachable _ (reliable_only_delivery honest_round_one_reachable)
    (by decide)

theorem honest_commander_regression :
    honestRoundTwo.views 1 = {1} ∧ decide (honestRoundTwo.views 1) = 1 := by decide

/-- A raw list of identities cannot create an honest signature in an empty ledger. -/
theorem no_honest_signature_without_issuance {P : Parameters n} {c : SignedChain n}
    {i : Node n} (hi : i ∉ P.faults) (hm : i ∈ c.path) : ¬ Derivable P ∅ c := by
  intro hc
  obtain ⟨pre, hp, _, _⟩ := derivable_honest_prefix hc i hi hm
  simp at hp

/-- The honest non-commander signed exactly a previously accepted prefix at its
length-indexed round. The continuation places that event before the current state. -/
theorem honest_signature_receipt {P : Parameters n} {s : Config n} (hr : Run P s)
    {c : SignedChain n} (hc : Derivable P s.issued c) {i : Node n}
    (hi : HonestLieutenant P i) (hm : i ∈ c.path) :
    ∃ pre before input, pre.value = c.value ∧ (pre.append i).path.IsPrefix c.path ∧
      Run P before ∧ Delivery P before input ∧
      pre ∈ accepted P before input i ∧ Signable P before i pre ∧
      before.round + 1 = pre.path.length ∧ Continues P (advance P before input) s := by
  obtain ⟨pre, hv, hpre, ho⟩ := honest_signature_origin hr hc hi.1 hm
  rcases ho with ⟨he, _, _⟩ | ⟨before, input, parent, hb, hd, _, ha, hs, he, cont⟩
  · exact (hi.2 he).elim
  · have eq : pre = parent := by
      cases pre
      cases parent
      simpa [SignedChain.append] using he
    subst parent
    exact ⟨pre, before, input, hv, hpre, hb, hd, ha, hs,
      (Finset.mem_filter.mp ha).2.2.2.symm, cont⟩

structure DistributedByzantineSignedGeneralsValiditySuite : Prop where
  origin : ∀ n (P : Parameters n) s, Run P s → ∀ c, Derivable P s.issued c →
    ∀ i, i ∉ P.faults → i ∈ c.path → ∃ pre : SignedChain n,
      pre.value = c.value ∧ (pre.append i).path.IsPrefix c.path ∧
      OperationalOrigin P s i (pre.append i)
  pigeonhole : ∀ n (P : Parameters n) (path : List (Node n)),
    path.Nodup → path.length = P.bound + 1 →
    ∃ i ∈ path, i ∉ P.faults
  correctness : ∀ n (P : Parameters n), BroadcastCorrect P
  views : ∀ n (P : Parameters n) s, Run P s → s.round = P.bound + 1 →
    ∀ i j, HonestLieutenant P i → HonestLieutenant P j → s.views i = s.views j
  progress : ∀ n (P : Parameters n) s, Run P s → s.round ≤ P.bound →
    ∃ next, Run P next ∧ next.round = s.round + 1
  equivocation : splitRoundTwo.views 1 = {0, 1} ∧ splitRoundTwo.views 2 = {0, 1}
  late_counterexample :
    decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 1) ≠
      decide ((finalWithoutRoundFilter faultyCommander silentRoundOne lateOrder).views 2)

theorem byzantine_signed_generals_master_suite :
    DistributedByzantineSignedGeneralsValiditySuite where
  origin := fun _ _ _ hr _ hc _ hi hm => honest_signature_origin hr hc hi hm
  pigeonhole := fun _ => chain_pigeonhole_honest_signer
  correctness := fun _ => signed_broadcast_correct
  views := fun _ _ _ hr ht _ _ hi hj => honest_views_identical hr ht hi hj
  progress := fun _ P _ hr ht => run_extend P hr ht
  equivocation := ⟨conflicting_orders_regression.2.1, conflicting_orders_regression.2.2.1⟩
  late_counterexample := by decide

end DistributedByzantineSignedGeneralsValidity
