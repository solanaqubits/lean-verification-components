/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedPaxos
import Verification.DistributedPaxosConsensus
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Operational Multi-Paxos with historical votes, immutable phase-one certificates,
and write-once proposals. Safety is derived from transitions, not a transition guard. -/
namespace DistributedMultiPaxosConsensus

abbrev NodeId (n : ℕ) := Fin n
abbrev Slot := ℕ

@[ext] structure Ballot (n : ℕ) where
  counter : ℕ
  leader : Fin n
  deriving DecidableEq, Repr

def Ballot.rank (b : Ballot n) : ℕ := b.counter * n + b.leader.val

theorem Ballot.rank_injective : Function.Injective (Ballot.rank (n := n)) := by
  intro a b h
  have ha := a.leader.isLt
  have hb := b.leader.isLt
  have hc : a.counter = b.counter := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hl
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hl)
      dsimp [Ballot.rank] at h
      nlinarith
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hl)
      dsimp [Ballot.rank] at h
      nlinarith
  apply Ballot.ext hc
  apply Fin.ext
  dsimp [Ballot.rank] at h
  rw [hc] at h
  omega

instance : LinearOrder (Ballot n) := LinearOrder.lift' Ballot.rank Ballot.rank_injective

theorem ballot_lt_iff (a b : Ballot n) :
    a < b ↔ a.counter < b.counter ∨ (a.counter = b.counter ∧ a.leader < b.leader) := by
  change a.rank < b.rank ↔ _
  have ha := a.leader.isLt
  have hb := b.leader.isLt
  dsimp [Ballot.rank]
  constructor
  · intro h
    rcases lt_trichotomy a.counter b.counter with hl | he | hg
    · exact Or.inl hl
    · exact Or.inr ⟨he, by change a.leader.val < b.leader.val; rw [he] at h; omega⟩
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hg)
      nlinarith
  · rintro (hl | ⟨he, hl⟩)
    · have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hl)
      nlinarith
    · change a.leader.val < b.leader.val at hl
      rw [he]
      omega

variable {α : Type} {n : ℕ}

abbrev Snapshot (α : Type) (n : ℕ) := Finset (Slot × Ballot n × α)
abbrev Certificate (α : Type) (n : ℕ) := Finset (Fin n) × (Fin n → Snapshot α n)

inductive PaxosMessage (α : Type) (n : ℕ) where
  | prepare (b : Ballot n)
  | promise (b : Ballot n) (fromNode : Fin n) (snapshot : Snapshot α n)
  | accept (b : Ballot n) (s : Slot) (v : α)
  | accepted (b : Ballot n) (s : Slot) (v : α) (fromNode : Fin n)
  deriving DecidableEq

open PaxosMessage

structure AcceptorState (α : Type) (n : ℕ) where
  promised : Option (Ballot n)
  accepted : Slot → Option (Ballot n × α)

def Majority (Q : Finset (Fin n)) : Prop := n < 2 * Q.card

instance (Q : Finset (Fin n)) : Decidable (Majority Q) :=
  inferInstanceAs (Decidable (n < 2 * Q.card))

theorem quorum_intersection {Q R : Finset (Fin n)} (hQ : Majority Q) (hR : Majority R) :
    ∃ p, p ∈ Q ∧ p ∈ R := by
  have h := Finset.inter_nonempty_of_card_lt_card_add_card
    (Finset.subset_univ Q) (Finset.subset_univ R)
  have hc : (Finset.univ : Finset (Fin n)).card < Q.card + R.card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    dsimp [Majority] at *
    omega
  obtain ⟨p, hp⟩ := h hc
  exact ⟨p, Finset.mem_inter.mp hp⟩

/-- Snapshot serialization is exact, including every occupied slot. -/
def ExactSnapshot (a : AcceptorState α n) (sn : Snapshot α n) : Prop :=
  ∀ s b v, (s, b, v) ∈ sn ↔ a.accepted s = some (b, v)

/-- Maximum is taken over all responses, separately for the requested slot. -/
def Select (C : Certificate α n) (s : Slot) (v : α) : Prop :=
  (∀ p ∈ C.1, ∀ b w, (s, b, w) ∉ C.2 p) ∨
  ∃ p ∈ C.1, ∃ b, (s, b, v) ∈ C.2 p ∧
    ∀ q ∈ C.1, ∀ c w, (s, c, w) ∈ C.2 q → c ≤ b

structure Config (α : Type) (n : ℕ) where
  nodes : Fin n → AcceptorState α n
  active : Ballot n → Option (Certificate α n)
  proposed : Ballot n → Slot → Option α
  history : List (PaxosMessage α n)

/-- The core keeps a sent-message archive. The explicit transport below refines it. -/
def initial : Config α n :=
  ⟨fun _ => ⟨none, fun _ => none⟩, fun _ => none, fun _ _ => none, []⟩

def emit (c : Config α n) (m : PaxosMessage α n) : Config α n :=
  { c with history := m :: c.history }

def promiseStep (c : Config α n) (p : Fin n) (b : Ballot n) (sn : Snapshot α n) : Config α n :=
  { c with nodes := Function.update c.nodes p { c.nodes p with promised := some b }
           history := promise b p sn :: c.history }

def activateStep (c : Config α n) (b : Ballot n) (C : Certificate α n) : Config α n :=
  { c with active := Function.update c.active b (some C) }

def proposeStep (c : Config α n) (b : Ballot n) (s : Slot) (v : α) : Config α n :=
  { c with proposed := Function.update c.proposed b (Function.update (c.proposed b) s (some v))
           history := accept b s v :: c.history }

def acceptStep (c : Config α n) (p : Fin n) (b : Ballot n) (s : Slot) (v : α) : Config α n :=
  { c with
    nodes := Function.update c.nodes p
      { promised := some b
        accepted := Function.update (c.nodes p).accepted s (some (b, v)) }
    history := accepted b s v p :: c.history }

inductive Step : Config α n → Config α n → Prop where
  | prepare (c) (b) : Step c (emit c (prepare b))
  | promise (c) (p) (b) (sn)
      (sent : prepare b ∈ c.history)
      (higher : ∀ old, (c.nodes p).promised = some old → old < b)
      (snapshot : ExactSnapshot (c.nodes p) sn) : Step c (promiseStep c p b sn)
  | activate (c) (b) (C)
      (fresh : c.active b = none) (quorum : Majority C.1)
      (responses : ∀ p ∈ C.1, promise b p (C.2 p) ∈ c.history) :
      Step c (activateStep c b C)
  | propose (c) (b) (s) (v) (C)
      (activated : c.active b = some C) (fresh : c.proposed b s = none)
      (selection : Select C s v) : Step c (proposeStep c b s v)
  | accept (c) (p) (b) (s) (v)
      (sent : accept b s v ∈ c.history)
      (eligible : ∀ old, (c.nodes p).promised = some old → old ≤ b) :
      Step c (acceptStep c p b s v)

inductive Reachable : Config α n → Prop where
  | initial : Reachable initial
  | next {c d} : Reachable c → Step c d → Reachable d

def Voted (c : Config α n) (p : Fin n) (b : Ballot n) (s : Slot) (v : α) : Prop :=
  accepted b s v p ∈ c.history

def Proposed (c : Config α n) (b : Ballot n) (s : Slot) (v : α) : Prop :=
  accept b s v ∈ c.history

/-- Historical acceptance, retained after later ballots overwrite a current entry. -/
def Chosen (c : Config α n) (s : Slot) (b : Ballot n) (v : α) : Prop :=
  ∃ Q, Majority Q ∧ ∀ p ∈ Q, Voted c p b s v

structure Invariants (c : Config α n) : Prop where
  bound : ∀ p s b v, (c.nodes p).accepted s = some (b, v) →
    ∃ d, (c.nodes p).promised = some d ∧ b ≤ d
  current : ∀ p s b v, (c.nodes p).accepted s = some (b, v) → Voted c p b s v
  latest : ∀ p b s v, Voted c p b s v →
    ∃ d w, (c.nodes p).accepted s = some (d, w) ∧ b ≤ d
  voted : ∀ p b s v, Voted c p b s v → Proposed c b s v
  stored : ∀ b s v, Proposed c b s v → c.proposed b s = some v
  promised : ∀ b p sn, promise b p sn ∈ c.history →
    ∃ d, (c.nodes p).promised = some d ∧ b ≤ d
  snapshotOrigin : ∀ b p sn, promise b p sn ∈ c.history →
    ∀ s d v, (s, d, v) ∈ sn → d < b ∧ Voted c p d s v
  snapshotCovers : ∀ b p sn, promise b p sn ∈ c.history →
    ∀ s d v, Voted c p d s v → d < b →
      ∃ e w, (s, e, w) ∈ sn ∧ d ≤ e
  certificate : ∀ b C, c.active b = some C →
    Majority C.1 ∧ ∀ p ∈ C.1, promise b p (C.2 p) ∈ c.history
  proposal : ∀ b s v, Proposed c b s v →
    ∃ C, Majority C.1 ∧ (∀ p ∈ C.1, promise b p (C.2 p) ∈ c.history) ∧ Select C s v

theorem history_monotonicity {c d : Config α n} (h : Step c d) :
    ∀ m ∈ c.history, m ∈ d.history := by
  cases h <;> intro m hm <;>
    simp_all [emit, promiseStep, activateStep, proposeStep, acceptStep]

theorem promise_monotonicity {c d : Config α n} (h : Step c d) (p : Fin n)
    (b : Ballot n) (hb : (c.nodes p).promised = some b) :
    ∃ e, (d.nodes p).promised = some e ∧ b ≤ e := by
  cases h with
  | prepare => exact ⟨b, hb, le_refl _⟩
  | activate => exact ⟨b, hb, le_refl _⟩
  | propose => exact ⟨b, hb, le_refl _⟩
  | promise q e sn sent higher snapshot =>
    by_cases hp : p = q
    · subst p
      exact ⟨e, by simp [promiseStep], le_of_lt (higher b hb)⟩
    · exact ⟨b, by simpa [promiseStep, hp] using hb, le_refl _⟩
  | accept q e s v sent eligible =>
    by_cases hp : p = q
    · subst p
      exact ⟨e, by simp [acceptStep], eligible b hb⟩
    · exact ⟨b, by simpa [acceptStep, hp] using hb, le_refl _⟩

theorem invariants_initial : Invariants (initial : Config α n) := by
  constructor <;> simp [initial, Voted, Proposed]

theorem invariants_step {c d : Config α n} (I : Invariants c) (h : Step c d) :
    Invariants d := by
  have hm := history_monotonicity h
  have hp := promise_monotonicity h
  cases h with
  | prepare b =>
    constructor
    · exact I.bound
    · simpa [Voted, emit] using I.current
    · simpa [Voted, emit] using I.latest
    · simpa [Voted, Proposed, emit] using I.voted
    · simpa [Proposed, emit] using I.stored
    · simpa [emit] using I.promised
    · simpa [Voted, emit] using I.snapshotOrigin
    · simpa [Voted, emit] using I.snapshotCovers
    · simpa [emit] using I.certificate
    · simpa [Proposed, emit] using I.proposal
  | activate b C fresh quorum responses =>
    constructor
    · exact I.bound
    · exact I.current
    · exact I.latest
    · exact I.voted
    · exact I.stored
    · exact I.promised
    · exact I.snapshotOrigin
    · exact I.snapshotCovers
    · intro e D he
      by_cases hb : e = b
      · subst e
        have : C = D := by simpa [activateStep] using he
        subst D
        exact ⟨quorum, responses⟩
      · exact I.certificate e D (by simpa [activateStep, hb] using he)
    · exact I.proposal
  | propose b s v C activated fresh selection =>
    have hc := I.certificate b C activated
    constructor
    · exact I.bound
    · simpa [Voted, proposeStep] using I.current
    · simpa [Voted, proposeStep] using I.latest
    · intro p e t w hv
      exact hm _ (I.voted p e t w (by simpa [Voted, proposeStep] using hv))
    · intro e t w hv
      have hv' : (e = b ∧ t = s ∧ w = v) ∨ Proposed c e t w := by
        simpa [Proposed, proposeStep, eq_comm, and_assoc] using hv
      rcases hv' with ⟨rfl, rfl, rfl⟩ | hv'
      · simp [proposeStep]
      · have hs := I.stored e t w hv'
        by_cases he : e = b
        · subst e
          by_cases ht : t = s
          · subst t
            rw [fresh] at hs
            contradiction
          · simpa [proposeStep, ht] using hs
        · simpa [proposeStep, he] using hs
    · simpa [proposeStep] using I.promised
    · simpa [Voted, proposeStep] using I.snapshotOrigin
    · simpa [Voted, proposeStep] using I.snapshotCovers
    · intro e D he
      obtain ⟨hQ, hr⟩ := I.certificate e D he
      exact ⟨hQ, fun p hmem => hm _ (hr p hmem)⟩
    · intro e t w hv
      have hv' : (e = b ∧ t = s ∧ w = v) ∨ Proposed c e t w := by
        simpa [Proposed, proposeStep, eq_comm, and_assoc] using hv
      rcases hv' with ⟨rfl, rfl, rfl⟩ | hv'
      · exact ⟨C, hc.1, fun p hmem => hm _ (hc.2 p hmem), selection⟩
      · obtain ⟨D, hQ, hr, hsel⟩ := I.proposal e t w hv'
        exact ⟨D, hQ, fun p hmem => hm _ (hr p hmem), hsel⟩
  | promise p b sn sent higher snapshot =>
    constructor
    · intro q s e v he
      have he' : (c.nodes q).accepted s = some (e, v) := by
        by_cases hq : q = p <;> simp_all [promiseStep]
      obtain ⟨f, hf, hef⟩ := I.bound q s e v he'
      obtain ⟨g, hg, hfg⟩ := hp q f hf
      exact ⟨g, hg, hef.trans hfg⟩
    · intro q s e v he
      apply hm
      apply I.current q s e v
      by_cases hq : q = p <;> simp_all [promiseStep]
    · intro q e s v hv
      have hv' : Voted c q e s v := by simpa [Voted, promiseStep] using hv
      obtain ⟨f, w, hf, hef⟩ := I.latest q e s v hv'
      refine ⟨f, w, ?_, hef⟩
      by_cases hq : q = p <;> simp_all [promiseStep]
    · simpa [Voted, Proposed, promiseStep] using I.voted
    · simpa [Proposed, promiseStep] using I.stored
    · intro e q ss hh
      have hh' : (e = b ∧ q = p ∧ ss = sn) ∨ promise e q ss ∈ c.history := by
        simpa [promiseStep, eq_comm, and_assoc] using hh
      rcases hh' with ⟨rfl, rfl, rfl⟩ | hh'
      · exact ⟨e, by simp [promiseStep], le_refl _⟩
      · obtain ⟨f, hf, hef⟩ := I.promised e q ss hh'
        obtain ⟨g, hg, hfg⟩ := hp q f hf
        exact ⟨g, hg, hef.trans hfg⟩
    · intro e q ss hh s f v hv
      have hh' : (e = b ∧ q = p ∧ ss = sn) ∨ promise e q ss ∈ c.history := by
        simpa [promiseStep, eq_comm, and_assoc] using hh
      rcases hh' with ⟨rfl, rfl, rfl⟩ | hh'
      · have he := (snapshot s f v).1 hv
        obtain ⟨g, hg, hfg⟩ := I.bound q s f v he
        exact ⟨lt_of_le_of_lt hfg (higher g hg), hm _ (I.current q s f v he)⟩
      · obtain ⟨hfe, hv'⟩ := I.snapshotOrigin e q ss hh' s f v hv
        exact ⟨hfe, hm _ hv'⟩
    · intro e q ss hh s f v hv hfe
      have hv' : Voted c q f s v := by simpa [Voted, promiseStep] using hv
      have hh' : (e = b ∧ q = p ∧ ss = sn) ∨ promise e q ss ∈ c.history := by
        simpa [promiseStep, eq_comm, and_assoc] using hh
      rcases hh' with ⟨rfl, rfl, rfl⟩ | hh'
      · obtain ⟨g, w, hg, hfg⟩ := I.latest q f s v hv'
        exact ⟨g, w, (snapshot s g w).2 hg, hfg⟩
      · exact I.snapshotCovers e q ss hh' s f v hv' hfe
    · intro e D he
      obtain ⟨hQ, hr⟩ := I.certificate e D he
      exact ⟨hQ, fun q hq => hm _ (hr q hq)⟩
    · intro e s v hv
      have hv' : Proposed c e s v := by simpa [Proposed, promiseStep] using hv
      obtain ⟨D, hQ, hr, hs⟩ := I.proposal e s v hv'
      exact ⟨D, hQ, fun q hq => hm _ (hr q hq), hs⟩
  | accept p b s v sent eligible =>
    constructor
    · intro q t e w he
      by_cases hq : q = p
      · subst q
        by_cases ht : t = s
        · subst t
          have he' : b = e ∧ v = w := by simpa [acceptStep] using he
          rcases he' with ⟨rfl, rfl⟩
          exact ⟨b, by simp [acceptStep], le_refl _⟩
        · have he' : (c.nodes p).accepted t = some (e, w) := by
            simpa [acceptStep, ht] using he
          obtain ⟨f, hf, hef⟩ := I.bound p t e w he'
          exact ⟨b, by simp [acceptStep], hef.trans (eligible f hf)⟩
      · obtain ⟨f, hf, hef⟩ := I.bound q t e w (by simpa [acceptStep, hq] using he)
        exact ⟨f, by simpa [acceptStep, hq] using hf, hef⟩
    · intro q t e w he
      by_cases hq : q = p
      · subst q
        by_cases ht : t = s
        · subst t
          have he' : b = e ∧ v = w := by simpa [acceptStep] using he
          rcases he' with ⟨rfl, rfl⟩
          simp [Voted, acceptStep]
        · exact hm _ (I.current p t e w (by simpa [acceptStep, ht] using he))
      · exact hm _ (I.current q t e w (by simpa [acceptStep, hq] using he))
    · intro q e t w hv
      have hv' : (e = b ∧ t = s ∧ w = v ∧ q = p) ∨ Voted c q e t w := by
        simpa [Voted, acceptStep, eq_comm, and_assoc] using hv
      rcases hv' with ⟨rfl, rfl, rfl, rfl⟩ | hv'
      · exact ⟨e, w, by simp [acceptStep], le_refl _⟩
      · obtain ⟨f, z, hf, hef⟩ := I.latest q e t w hv'
        by_cases hq : q = p
        · subst q
          by_cases ht : t = s
          · subst t
            obtain ⟨g, hg, hfg⟩ := I.bound p s f z hf
            exact ⟨b, v, by simp [acceptStep], hef.trans (hfg.trans (eligible g hg))⟩
          · exact ⟨f, z, by simpa [acceptStep, ht] using hf, hef⟩
        · exact ⟨f, z, by simpa [acceptStep, hq] using hf, hef⟩
    · intro q e t w hv
      have hv' : (e = b ∧ t = s ∧ w = v ∧ q = p) ∨ Voted c q e t w := by
        simpa [Voted, acceptStep, eq_comm, and_assoc] using hv
      rcases hv' with ⟨rfl, rfl, rfl, rfl⟩ | hv'
      · exact hm _ sent
      · exact hm _ (I.voted q e t w hv')
    · simpa [Proposed, acceptStep] using I.stored
    · intro e q ss hh
      have hh' : promise e q ss ∈ c.history := by simpa [acceptStep] using hh
      obtain ⟨f, hf, hef⟩ := I.promised e q ss hh'
      obtain ⟨g, hg, hfg⟩ := hp q f hf
      exact ⟨g, hg, hef.trans hfg⟩
    · intro e q ss hh t f w hw
      have hh' : promise e q ss ∈ c.history := by simpa [acceptStep] using hh
      obtain ⟨hfe, hv⟩ := I.snapshotOrigin e q ss hh' t f w hw
      exact ⟨hfe, hm _ hv⟩
    · intro e q ss hh t f w hv hfe
      have hh' : promise e q ss ∈ c.history := by simpa [acceptStep] using hh
      have hv' : (f = b ∧ t = s ∧ w = v ∧ q = p) ∨ Voted c q f t w := by
        simpa [Voted, acceptStep, eq_comm, and_assoc] using hv
      rcases hv' with ⟨rfl, rfl, rfl, rfl⟩ | hv'
      · obtain ⟨g, hg, heg⟩ := I.promised e q ss hh'
        exact (not_lt_of_ge (heg.trans (eligible g hg)) hfe).elim
      · exact I.snapshotCovers e q ss hh' t f w hv' hfe
    · intro e D he
      obtain ⟨hQ, hr⟩ := I.certificate e D he
      exact ⟨hQ, fun q hq => hm _ (hr q hq)⟩
    · intro e t w hv
      have hv' : Proposed c e t w := by simpa [Proposed, acceptStep] using hv
      obtain ⟨D, hQ, hr, hs⟩ := I.proposal e t w hv'
      exact ⟨D, hQ, fun q hq => hm _ (hr q hq), hs⟩

theorem reachable_invariants {c : Config α n} (h : Reachable c) : Invariants c := by
  induction h with
  | initial => exact invariants_initial
  | next _ step ih => exact invariants_step ih step

theorem proposal_uniqueness {c : Config α n} (h : Reachable c)
    {b : Ballot n} {s : Slot} {v w : α} (hv : Proposed c b s v) (hw : Proposed c b s w) :
    v = w := by
  have I := reachable_invariants h
  exact Option.some.inj ((I.stored b s v hv).symm.trans (I.stored b s w hw))

theorem chosen_proposed {c : Config α n} (h : Reachable c)
    {s b v} (hc : Chosen c s b v) : Proposed c b s v := by
  obtain ⟨Q, hQ, hv⟩ := hc
  obtain ⟨p, hp, _⟩ := quorum_intersection hQ hQ
  exact (reachable_invariants h).voted p b s v (hv p hp)

/-- Strong induction on ballot rank; Promise snapshots cover even later historical votes. -/
theorem inter_ballot_value_preservation {c : Config α n} (h : Reachable c)
    {s : Slot} {b : Ballot n} {v : α} (hc : Chosen c s b v)
    {b' : Ballot n} {w : α} (hlt : b < b') (hw : Proposed c b' s w) : v = w := by
  have I := reachable_invariants h
  have main : ∀ k, ∀ d : Ballot n, d.rank = k →
      ∀ z, b < d → Proposed c d s z → v = z := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd z hbd hz
      obtain ⟨C, hC, hr, hs⟩ := I.proposal d s z hz
      obtain ⟨Q, hQ, hvotes⟩ := hc
      obtain ⟨p, hpQ, hpC⟩ := quorum_intersection hQ hC
      obtain ⟨e, u, he, hbe⟩ := I.snapshotCovers d p (C.2 p) (hr p hpC)
        s b v (hvotes p hpQ) hbd
      rcases hs with empty | ⟨q, hq, f, hf, hmax⟩
      · exact (empty p hpC e u he).elim
      · have hef := hmax p hpC e u he
        have hbf : b ≤ f := hbe.trans hef
        obtain ⟨hfd, hvote⟩ := I.snapshotOrigin d q (C.2 q) (hr q hq) s f z hf
        have hz' := I.voted q f s z hvote
        rcases eq_or_lt_of_le hbf with heq | hlt'
        · subst f
          exact proposal_uniqueness h (chosen_proposed h ⟨Q, hQ, hvotes⟩) hz'
        · have hk : f.rank < k := by change f.rank < d.rank at hfd; omega
          exact ih f.rank hk f rfl z hlt' hz'
  exact main b'.rank b' rfl w hlt hw

theorem multi_paxos_slot_agreement {c : Config α n} (h : Reachable c)
    {s b₁ b₂ v₁ v₂} (h₁ : Chosen c s b₁ v₁) (h₂ : Chosen c s b₂ v₂) : v₁ = v₂ := by
  rcases lt_trichotomy b₁ b₂ with hb | hb | hb
  · exact inter_ballot_value_preservation h h₁ hb (chosen_proposed h h₂)
  · subst b₂
    exact proposal_uniqueness h (chosen_proposed h h₁) (chosen_proposed h h₂)
  · exact (inter_ballot_value_preservation h h₂ hb (chosen_proposed h h₁)).symm

theorem chosen_persistent {c d : Config α n} (h : Step c d) {s b v}
    (hc : Chosen c s b v) : Chosen d s b v := by
  obtain ⟨Q, hQ, hv⟩ := hc
  exact ⟨Q, hQ, fun p hp => history_monotonicity h _ (hv p hp)⟩

/-- Current simultaneous acceptance implies historical choice, but not conversely. -/
theorem chosen_of_current_quorum {c : Config α n} (h : Reachable c)
    {Q : Finset (Fin n)} (hQ : Majority Q) {s b v}
    (hv : ∀ p ∈ Q, (c.nodes p).accepted s = some (b, v)) : Chosen c s b v :=
  ⟨Q, hQ, fun p hp => (reachable_invariants h).current p s b v (hv p hp)⟩

/-- A replica's executed list represents slots 0 through length-1, without holes. -/
def Executed (c : Config α n) (L : List α) : Prop :=
  ∀ i (hi : i < L.length), ∃ b, Chosen c i b L[i]

theorem executed_prefix {c : Config α n} (h : Reachable c) {L R : List α}
    (hL : Executed c L) (hR : Executed c R) (hlen : L.length ≤ R.length) :
    L.IsPrefix R := by
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem
  · simp [Nat.min_eq_left hlen]
  · intro i hi hj
    have hiR : i < R.length := lt_of_lt_of_le hi hlen
    obtain ⟨b, hb⟩ := hL i hi
    obtain ⟨d, hd⟩ := hR i hiR
    simpa using multi_paxos_slot_agreement h hb hd

theorem executable_log_prefix_consistency {c : Config α n} (h : Reachable c)
    {L R : List α} (hL : Executed c L) (hR : Executed c R) :
    L.IsPrefix R ∨ R.IsPrefix L := by
  rcases le_total L.length R.length with hl | hl
  · exact Or.inl (executed_prefix h hL hR hl)
  · exact Or.inr (executed_prefix h hR hL hl)

theorem state_machine_convergence {σ : Type} {c : Config α n} (h : Reachable c)
    {L R : List α} (hL : Executed c L) (hR : Executed c R) (hlen : L.length = R.length)
    (transition : σ → α → σ) (start : σ) :
    L.foldl transition start = R.foldl transition start := by
  have he : L = R := List.Sublist.antisymm
    (executed_prefix h hL hR hlen.le).sublist (executed_prefix h hR hL hlen.ge).sublist
  rw [he]

/-- A learner needs actual acknowledgement messages from a majority. -/
def Learnable (c : Config α n) (s : Slot) (v : α) : Prop :=
  ∃ b Q, Majority Q ∧ ∀ p ∈ Q, accepted b s v p ∈ c.history

theorem learnable_iff_chosen (c : Config α n) (s : Slot) (v : α) :
    Learnable c s v ↔ ∃ b, Chosen c s b v := by rfl

inductive ExecuteStep (c : Config α n) : List α → List α → Prop where
  | next (L : List α) (v : α) (ready : Learnable c L.length v) :
      ExecuteStep c L (L ++ [v])

theorem execution_preserves_prefix {c : Config α n} {L R : List α}
    (hL : Executed c L) (h : ExecuteStep c L R) : Executed c R := by
  cases h with
  | next v ready =>
    intro i hi
    by_cases hil : i < L.length
    · simpa [List.getElem_append_left hil] using hL i hil
    · have hie : i = L.length := by
        simp only [List.length_append, List.length_singleton] at hi
        omega
      subst i
      simpa using (learnable_iff_chosen c L.length v).1 ready

theorem hole_blocks_execution {c : Config α n} {L : List α}
    (hole : ∀ b v, ¬ Chosen c L.length b v) : ∀ R, ¬ ExecuteStep c L R := by
  intro R hs
  cases hs with
  | next v ready =>
    obtain ⟨b, hb⟩ := (learnable_iff_chosen c L.length v).1 ready
    exact hole b v hb

/-- Finite serialization exists in every reachable configuration. -/
def voteRecords [DecidableEq α] (c : Config α n) (p : Fin n) : Snapshot α n :=
  (c.history.filterMap fun m => match m with
    | .accepted b s v q => if q = p then some (s, b, v) else none
    | _ => none).toFinset

theorem mem_voteRecords [DecidableEq α] (c : Config α n) (p : Fin n) (s b v) :
    (s, b, v) ∈ voteRecords c p ↔ Voted c p b s v := by
  simp only [voteRecords, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨m, hm, he⟩
    cases m with
    | prepare => simp at he
    | promise => simp at he
    | accept => simp at he
    | accepted e t w q =>
      dsimp only at he
      split_ifs at he with hq
      · subst q
        have he' : t = s ∧ e = b ∧ w = v := by simpa using he
        rcases he' with ⟨rfl, rfl, rfl⟩
        exact hm
  · intro hv
    exact ⟨accepted b s v p, hv, by simp⟩

def serialize [DecidableEq α] (c : Config α n) (p : Fin n) : Snapshot α n :=
  (voteRecords c p).filter fun r => (c.nodes p).accepted r.1 = some r.2

theorem serialize_exact [DecidableEq α] {c : Config α n} (h : Reachable c) (p : Fin n) :
    ExactSnapshot (c.nodes p) (serialize c p) := by
  intro s b v
  simp only [serialize, Finset.mem_filter, mem_voteRecords]
  exact ⟨And.right, fun he => ⟨(reachable_invariants h).current p s b v he, he⟩⟩

/-- Inputs must actually be available at the corresponding network step. -/
inductive Inputs : Config α n → Config α n → List (PaxosMessage α n) → Prop where
  | prepare (c b packets) : Inputs c (emit c (prepare b)) packets
  | promise (c p b sn packets) (available : prepare b ∈ packets) :
      Inputs c (promiseStep c p b sn) packets
  | activate (c b C packets) (available : ∀ p ∈ C.1, promise b p (C.2 p) ∈ packets) :
      Inputs c (activateStep c b C) packets
  | propose (c b s v packets) : Inputs c (proposeStep c b s v) packets
  | accept (c p b s v packets) (available : accept b s v ∈ packets) :
      Inputs c (acceptStep c p b s v) packets

structure Network (α : Type) (n : ℕ) where
  core : Config α n
  pending : List (PaxosMessage α n)

/-- Lists represent finite message multisets; delivery is nondeterministic, not FIFO.
Packets may be retained for retransmission, explicitly duplicated, or dropped. -/
inductive NetworkStep : Network α n → Network α n → Prop where
  | protocol {c d} (packets) (h : Step c d)
      (available : Inputs c d packets)
      (newMessages) (sent : d.history = newMessages ++ c.history) :
      NetworkStep ⟨c, packets⟩ ⟨d, newMessages ++ packets⟩
  | duplicate (c) (packets) (m) (present : m ∈ packets) :
      NetworkStep ⟨c, packets⟩ ⟨c, m :: packets⟩
  | drop (c) (before after) (m) :
      NetworkStep ⟨c, before ++ m :: after⟩ ⟨c, before ++ after⟩
  | idle (N) : NetworkStep N N

inductive NetworkReachable : Network α n → Prop where
  | initial : NetworkReachable ⟨initial, []⟩
  | next {N M} : NetworkReachable N → NetworkStep N M → NetworkReachable M

theorem network_refinement {N : Network α n} (h : NetworkReachable N) :
    Reachable N.core ∧ ∀ m ∈ N.pending, m ∈ N.core.history := by
  induction h with
  | initial => exact ⟨Reachable.initial, by simp⟩
  | next _ step ih =>
    cases step with
    | protocol packets step available newMessages sent =>
      refine ⟨Reachable.next ih.1 step, ?_⟩
      intro m hm
      rw [sent]
      rcases List.mem_append.mp hm with hn | ho
      · exact List.mem_append_left _ hn
      · exact List.mem_append_right _ (ih.2 m ho)
    | duplicate c packets m present =>
      refine ⟨ih.1, ?_⟩
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ih.2 v present
      · exact ih.2 v hv
    | drop c before after m =>
      refine ⟨ih.1, ?_⟩
      intro v hv
      apply ih.2 v
      simpa only [List.mem_append, List.mem_cons] using
        (show v ∈ before ∨ v = m ∨ v ∈ after from
          (List.mem_append.mp hv).elim Or.inl (fun h => Or.inr (Or.inr h)))
    | idle => exact ih

theorem message_authenticity {N : Network α n} (h : NetworkReachable N) :
    ∀ m ∈ N.pending, m ∈ N.core.history := (network_refinement h).2

theorem network_slot_agreement {N : Network α n} (h : NetworkReachable N)
    {s b d v w} (hv : Chosen N.core s b v) (hw : Chosen N.core s d w) : v = w :=
  multi_paxos_slot_agreement (network_refinement h).1 hv hw

theorem step_output {c d : Config α n} (h : Step c d) :
    ∃ ms, d.history = ms ++ c.history := by
  cases h
  · exact ⟨[prepare _], rfl⟩
  · exact ⟨[promise _ _ _], rfl⟩
  · exact ⟨[], rfl⟩
  · exact ⟨[accept _ _ _], rfl⟩
  · exact ⟨[accepted _ _ _ _], rfl⟩

theorem inputs_archive {c d : Config α n} (h : Step c d) : Inputs c d c.history := by
  cases h with
  | prepare => exact Inputs.prepare ..
  | promise p b sn sent higher snapshot => exact Inputs.promise _ _ _ _ _ sent
  | activate b C fresh quorum responses => exact Inputs.activate _ _ _ _ responses
  | propose => exact Inputs.propose ..
  | accept p b s v sent eligible => exact Inputs.accept _ _ _ _ _ _ sent

/-- Every core execution has a loss-free network realization; the model is nonvacuous. -/
theorem core_network_realization {c : Config α n} (h : Reachable c) :
    NetworkReachable ⟨c, c.history⟩ := by
  induction h with
  | initial => exact NetworkReachable.initial
  | next _ step ih =>
    obtain ⟨ms, hms⟩ := step_output step
    have hn := NetworkReachable.next ih
      (NetworkStep.protocol _ step (inputs_archive step) ms hms)
    simpa only [← hms] using hn

/-- Any stale ballot is excluded by the actual acceptance guard. -/
theorem reject_stale_accept {c : Config α n} (p : Fin n) (b d : Ballot n)
    (hp : (c.nodes p).promised = some d) (hlt : b < d) :
    ¬ (∀ old, (c.nodes p).promised = some old → old ≤ b) := by
  intro eligible
  exact not_le_of_gt hlt (eligible d hp)

structure System (α : Type) (n : ℕ) where
  network : Network α n
  logs : Fin n → List α

inductive SystemStep : System α n → System α n → Prop where
  | protocol {N M} (logs) (step : NetworkStep N M) :
      SystemStep ⟨N, logs⟩ ⟨M, logs⟩
  | execute (N : Network α n) (logs : Fin n → List α) (p) (v) (b) (Q)
      (quorum : Majority Q)
      (acks : ∀ q ∈ Q, accepted b (logs p).length v q ∈ N.pending) :
      SystemStep ⟨N, logs⟩ ⟨N, Function.update logs p (logs p ++ [v])⟩

inductive SystemReachable : System α n → Prop where
  | initial : SystemReachable ⟨⟨initial, []⟩, fun _ => []⟩
  | next {S T} : SystemReachable S → SystemStep S T → SystemReachable T

theorem network_history_mono {N M : Network α n} (h : NetworkStep N M) :
    ∀ m ∈ N.core.history, m ∈ M.core.history := by
  cases h with
  | protocol packets step available ms sent => exact history_monotonicity step
  | duplicate => exact fun _ h => h
  | drop => exact fun _ h => h
  | idle => exact fun _ h => h

theorem system_invariant {S : System α n} (h : SystemReachable S) :
    NetworkReachable S.network ∧ ∀ p, Executed S.network.core (S.logs p) := by
  induction h with
  | initial => exact ⟨NetworkReachable.initial, by simp [Executed]⟩
  | next _ step ih =>
    cases step with
    | protocol logs hs =>
      refine ⟨NetworkReachable.next ih.1 hs, ?_⟩
      intro p i hi
      obtain ⟨b, Q, hQ, hv⟩ := ih.2 p i hi
      exact ⟨b, Q, hQ, fun q hq => network_history_mono hs _ (hv q hq)⟩
    | execute N logs p v b Q quorum acks =>
      refine ⟨ih.1, ?_⟩
      intro q
      by_cases hq : q = p
      · subst q
        simp only [Function.update_self]
        apply execution_preserves_prefix (ih.2 p)
        exact ExecuteStep.next _ v ⟨b, Q, quorum,
          fun q hq => message_authenticity ih.1 _ (acks q hq)⟩
      · simpa [Function.update_of_ne hq] using ih.2 q

theorem reachable_replica_prefixes {S : System α n} (h : SystemReachable S) (p q : Fin n) :
    (S.logs p).IsPrefix (S.logs q) ∨ (S.logs q).IsPrefix (S.logs p) :=
  executable_log_prefix_consistency (network_refinement (system_invariant h).1).1
    ((system_invariant h).2 p) ((system_invariant h).2 q)

namespace Regression

def b0 : Ballot 3 := ⟨0, 0⟩
def b1 : Ballot 3 := ⟨1, 1⟩
@[simp] theorem b1_ne_b0 : b1 ≠ b0 := by decide
@[simp] theorem b0_ne_b1 : b0 ≠ b1 := by decide
def C0 : Certificate ℕ 3 := ({0, 1}, fun _ => ∅)
def C1 : Certificate ℕ 3 := ({1, 2}, fun p => if p = 1 then {(0, b0, 7)} else ∅)
def c0 : Config ℕ 3 := initial
def c1 := emit c0 (prepare b0)
def c2 := promiseStep c1 0 b0 ∅
def c3 := promiseStep c2 1 b0 ∅
def c4 := activateStep c3 b0 C0
def c5 := proposeStep c4 b0 0 7
def c6 := acceptStep c5 0 b0 0 7
def c7 := acceptStep c6 1 b0 0 7
def c8 := proposeStep c7 b0 1 8
def c9 := acceptStep c8 0 b0 1 8
def c10 := acceptStep c9 1 b0 1 8
def c11 := proposeStep c10 b0 2 9
def c12 := acceptStep c11 0 b0 2 9
def c13 := acceptStep c12 1 b0 2 9

def d1 := emit c7 (prepare b1)
def d2 := promiseStep d1 1 b1 {(0, b0, 7)}
def d3 := promiseStep d2 2 b1 ∅
def d4 := activateStep d3 b1 C1
def d5 := proposeStep d4 b1 0 7
def d6 := acceptStep d5 1 b1 0 7
def d7 := acceptStep d6 2 b1 0 7

macro "trace_simp" : tactic => `(tactic|
  simp [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13,
    d1, d2, d3, d4, d5, d6, d7, C0, C1, initial, emit, promiseStep, activateStep,
    proposeStep, acceptStep, ExactSnapshot, Majority, Proposed, Voted, Select])

theorem reach_c1 : Reachable c1 := Reachable.next Reachable.initial (Step.prepare c0 b0)
theorem reach_c2 : Reachable c2 := by
  apply Reachable.next reach_c1
  apply Step.promise <;> trace_simp

theorem reach_c3 : Reachable c3 := by
  apply Reachable.next reach_c2
  apply Step.promise <;> trace_simp

theorem reach_c4 : Reachable c4 := by
  apply Reachable.next reach_c3
  apply Step.activate <;> trace_simp

theorem reach_c5 : Reachable c5 := by
  apply Reachable.next reach_c4
  apply Step.propose (C := C0) <;> trace_simp

theorem reach_c6 : Reachable c6 := by
  apply Reachable.next reach_c5
  apply Step.accept <;> trace_simp

theorem reach_c7 : Reachable c7 := by
  apply Reachable.next reach_c6
  apply Step.accept <;> trace_simp

theorem reach_c8 : Reachable c8 := by
  apply Reachable.next reach_c7
  apply Step.propose (C := C0) <;> trace_simp

theorem reach_c9 : Reachable c9 := by
  apply Reachable.next reach_c8
  apply Step.accept <;> trace_simp

theorem reach_c10 : Reachable c10 := by
  apply Reachable.next reach_c9
  apply Step.accept <;> trace_simp

theorem reach_c11 : Reachable c11 := by
  apply Reachable.next reach_c10
  apply Step.propose (C := C0) <;> trace_simp

theorem reach_c12 : Reachable c12 := by
  apply Reachable.next reach_c11
  apply Step.accept <;> trace_simp

theorem reach_c13 : Reachable c13 := by
  apply Reachable.next reach_c12
  apply Step.accept <;> trace_simp

theorem chosen_c7 : Chosen c7 0 b0 7 := by
  refine ⟨{0, 1}, by decide, ?_⟩
  trace_simp

theorem three_slots_one_epoch : Reachable c13 ∧
    c13.active b0 = some C0 ∧ Chosen c13 0 b0 7 ∧
    Chosen c13 1 b0 8 ∧ Chosen c13 2 b0 9 := by
  refine ⟨reach_c13, ?_, ?_, ?_, ?_⟩
  · trace_simp
  all_goals refine ⟨{0, 1}, by decide, ?_⟩; trace_simp

theorem reach_d1 : Reachable d1 := Reachable.next reach_c7 (Step.prepare c7 b1)
theorem reach_d2 : Reachable d2 := by
  apply Reachable.next reach_d1
  apply Step.promise
  · trace_simp
  · trace_simp
    decide
  · intro s b v
    by_cases hs : s = 0
    · subst s; trace_simp; tauto
    · simp [d1, c7, c6, c5, c4, c3, c2, c1, c0, initial, emit, acceptStep, promiseStep,
        activateStep, proposeStep, hs, eq_comm]

theorem reach_d3 : Reachable d3 := by
  apply Reachable.next reach_d2
  apply Step.promise <;> trace_simp

theorem reach_d4 : Reachable d4 := by
  apply Reachable.next reach_d3
  apply Step.activate <;> trace_simp

theorem select_C1 : Select C1 0 7 := by
  right
  refine ⟨1, by simp [C1], b0, by simp [C1], ?_⟩
  intro q hq b v hv
  simp only [C1, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with rfl | rfl <;> simp_all [C1]

theorem reach_d5 : Reachable d5 := by
  apply Reachable.next reach_d4
  apply Step.propose (C := C1)
  · trace_simp
  · trace_simp
  · exact select_C1

theorem reach_d6 : Reachable d6 := by
  apply Reachable.next reach_d5
  apply Step.accept <;> trace_simp

theorem reach_d7 : Reachable d7 := by
  apply Reachable.next reach_d6
  apply Step.accept <;> trace_simp

theorem leader_change : Reachable d7 ∧ Chosen d7 0 b0 7 ∧ Chosen d7 0 b1 7 := by
  refine ⟨reach_d7, ⟨{0, 1}, by decide, ?_⟩, ⟨{1, 2}, by decide, ?_⟩⟩ <;> trace_simp

theorem old_accept_rejected :
    ¬ (∀ old, (d7.nodes 1).promised = some old → old ≤ b0) :=
  reject_stale_accept 1 b0 b1 (by trace_simp) (by decide)

theorem pipeline_executes : Executed c13 [7, 8, 9] := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 := by simp at hi; omega
  rcases this with rfl | rfl | rfl <;>
    refine ⟨b0, {0, 1}, by decide, ?_⟩ <;> trace_simp

def gap1 := proposeStep c4 b0 1 8
def gap2 := acceptStep gap1 0 b0 1 8
def gap3 := acceptStep gap2 1 b0 1 8

theorem reach_gap : Reachable gap3 := by
  have h1 : Reachable gap1 := by
    apply Reachable.next reach_c4
    apply Step.propose (C := C0) <;> trace_simp
  have h2 : Reachable gap2 := by
    apply Reachable.next h1
    apply Step.accept <;> (simp only [gap1, proposeStep]; trace_simp)
  apply Reachable.next h2
  apply Step.accept <;> (simp only [gap2, gap1, acceptStep, proposeStep]; trace_simp)

theorem gap_blocks_prefix : Chosen gap3 1 b0 8 ∧ ∀ L, ¬ ExecuteStep gap3 [] L := by
  constructor
  · refine ⟨{0, 1}, by decide, ?_⟩
    simp [gap3, gap2, gap1, acceptStep, proposeStep, Voted]
  · apply hole_blocks_execution
    intro b v hc
    have hp := chosen_proposed reach_gap hc
    simp [gap3, gap2, gap1, acceptStep, proposeStep, Proposed, c4, c3, c2, c1, c0,
      activateStep, promiseStep, emit, initial] at hp

end Regression

namespace SingleReplica

def ballot : Ballot 1 := ⟨0, 0⟩
def cert : Certificate α 1 := (Finset.univ, fun _ => ∅)
def a : Config α 1 := emit initial (prepare ballot)
def b : Config α 1 := promiseStep a 0 ballot ∅
def c : Config α 1 := activateStep b ballot cert
def d (v : α) : Config α 1 := proposeStep c ballot 0 v
def e (v : α) : Config α 1 := acceptStep (d v) 0 ballot 0 v

theorem reachable (v : α) : Reachable (e v) := by
  have ha : Reachable (a : Config α 1) := Reachable.next Reachable.initial (Step.prepare _ _)
  have hb : Reachable (b : Config α 1) := by
    apply Reachable.next ha
    apply Step.promise <;> simp [a, initial, emit, ExactSnapshot]
  have hc : Reachable (c : Config α 1) := by
    apply Reachable.next hb
    apply Step.activate
    · rfl
    · simp [cert, Majority]
    · intro p hp
      have he : p = 0 := Fin.eq_zero p
      subst p
      simp [cert, b, promiseStep]
  have hd : Reachable (d v) := by
    apply Reachable.next hc
    apply Step.propose (C := cert)
    · simp [c, activateStep]
    · rfl
    · left; simp [cert]
  apply Reachable.next hd
  apply Step.accept
  · simp [d, proposeStep]
  · simp [d, c, b, a, proposeStep, activateStep, promiseStep]

theorem chosen (v : α) : Chosen (e v) 0 ballot v := by
  refine ⟨Finset.univ, by simp [Majority], ?_⟩
  intro p hp
  have he : p = 0 := Fin.eq_zero p
  subst p
  simp [Voted, e, acceptStep]

end SingleReplica

inductive Fault where
  | ignoreMax
  | reusedBallot

/-- Explicitly faulty variants; these constructors are not part of Step. -/
inductive FaultStep : Fault → Config α n → Config α n → Prop where
  | normal {mode c d} (step : Step c d) : FaultStep mode c d
  | ignoreMax (c b s v C) (activated : c.active b = some C)
      (fresh : c.proposed b s = none) : FaultStep .ignoreMax c (proposeStep c b s v)
  | reuse (c b s v C) (actor : Fin n) (wrongOwner : actor ≠ b.leader)
      (activated : c.active b = some C) (selection : Select C s v) :
      FaultStep .reusedBallot c (proposeStep c b s v)

inductive FaultReachable (mode : Fault) : Config α n → Prop where
  | safe {c} (h : Reachable c) : FaultReachable mode c
  | next {c d} : FaultReachable mode c → FaultStep mode c d → FaultReachable mode d

namespace Regression

def wrongMax1 := proposeStep d4 b1 0 9
def wrongMax2 := acceptStep wrongMax1 1 b1 0 9
def wrongMax3 := acceptStep wrongMax2 2 b1 0 9

theorem reach_wrongMax : FaultReachable .ignoreMax wrongMax3 := by
  have h1 : FaultReachable .ignoreMax wrongMax1 := by
    apply FaultReachable.next (FaultReachable.safe reach_d4)
    apply FaultStep.ignoreMax (C := C1) <;> trace_simp
  have h2 : FaultReachable .ignoreMax wrongMax2 := by
    apply FaultReachable.next h1
    apply FaultStep.normal
    apply Step.accept
    · simp [wrongMax1, proposeStep]
    · simp only [wrongMax1, proposeStep]; trace_simp
  apply FaultReachable.next h2
  apply FaultStep.normal
  apply Step.accept
  · simp [wrongMax2, wrongMax1, acceptStep, proposeStep]
  · simp only [wrongMax2, wrongMax1, acceptStep, proposeStep]; trace_simp

def reused1 := proposeStep c7 b0 0 9
def reused2 := acceptStep reused1 0 b0 0 9
def reused3 := acceptStep reused2 1 b0 0 9

theorem reach_reused : FaultReachable .reusedBallot reused3 := by
  have h1 : FaultReachable .reusedBallot reused1 := by
    apply FaultReachable.next (FaultReachable.safe reach_c7)
    apply FaultStep.reuse (C := C0) (actor := 1)
    · decide
    · trace_simp
    · trace_simp
  have h2 : FaultReachable .reusedBallot reused2 := by
    apply FaultReachable.next h1
    apply FaultStep.normal
    apply Step.accept
    · simp [reused1, proposeStep]
    · simp only [reused1, proposeStep]; trace_simp
  apply FaultReachable.next h2
  apply FaultStep.normal
  apply Step.accept
  · simp [reused2, reused1, acceptStep, proposeStep]
  · simp only [reused2, reused1, acceptStep, proposeStep]; trace_simp

end Regression
open Regression in
/-- An operational counterexample to omitting the maximum-ballot selection rule. -/
theorem counterexample_ignore_max_ballot :
    ∃ c : Config ℕ 3, FaultReachable .ignoreMax c ∧
      Chosen c 0 b0 7 ∧ Chosen c 0 b1 9 ∧ (7 : ℕ) ≠ 9 := by
  refine ⟨wrongMax3, reach_wrongMax, ?_, ?_, by decide⟩
  · refine ⟨{0, 1}, by decide, ?_⟩
    simp only [Voted, wrongMax3, wrongMax2, wrongMax1, acceptStep, proposeStep]; trace_simp
  · refine ⟨{1, 2}, by decide, ?_⟩
    simp [Voted, wrongMax3, wrongMax2, wrongMax1, acceptStep, proposeStep]

open Regression in
/-- A second actor reuses the same key and overwrites its slot proposal. -/
theorem counterexample_reused_ballot :
    ∃ c : Config ℕ 3, FaultReachable .reusedBallot c ∧
      Chosen c 0 b0 7 ∧ Chosen c 0 b0 9 ∧ (7 : ℕ) ≠ 9 := by
  refine ⟨reused3, reach_reused, ?_, ?_, by decide⟩
  · refine ⟨{0, 1}, by decide, ?_⟩
    simp only [Voted, reused3, reused2, reused1, acceptStep, proposeStep]; trace_simp
  · refine ⟨{0, 1}, by decide, ?_⟩
    simp [Voted, reused3, reused2, reused1, acceptStep, proposeStep]

def legacyBallot (b : Ballot n) : DistributedPaxos.Ballot := ⟨b.counter, b.leader.val⟩

theorem legacyBallot_injective : Function.Injective (legacyBallot (n := n)) := by
  intro a b h
  apply Ballot.ext
  · exact congrArg DistributedPaxos.Ballot.round h
  · apply Fin.ext
    exact congrArg DistributedPaxos.Ballot.proposerId h

def legacyAccepted (hn : 0 < n) (c : Config α n) (s : Slot) (encode : α → ℕ) :
    DistributedPaxos.Accepted ⟨n, hn⟩ :=
  fun p b v => ∃ d w, legacyBallot d = b ∧ Voted c p d s w ∧ encode w = v

/-- The old module's SingleVote premise is now a consequence of execution. -/
theorem derived_single_vote (hn : 0 < n) {c : Config α n} (h : Reachable c)
    (s : Slot) (encode : α → ℕ) : DistributedPaxos.SingleVote (legacyAccepted hn c s encode) := by
  intro p b v w hv hw
  obtain ⟨d, x, hd, hx, rfl⟩ := hv
  obtain ⟨e, y, he, hy, rfl⟩ := hw
  have eq : d = e := legacyBallot_injective (hd.trans he.symm)
  subst e
  have I := reachable_invariants h
  rw [proposal_uniqueness h (I.voted p d s x hx) (I.voted p d s y hy)]

theorem single_phase_one_pipeline :
    Regression.c13.history.count (prepare Regression.b0) = 1 := by decide

theorem network_system_realization {N : Network α n} (h : NetworkReachable N) :
    SystemReachable ⟨N, fun _ => []⟩ := by
  induction h with
  | initial => exact SystemReachable.initial
  | next _ step ih => exact SystemReachable.next ih (SystemStep.protocol _ step)

theorem singleton_execution (v : α) :
    ∃ S : System α 1, SystemReachable S ∧ S.logs 0 = [v] := by
  let N : Network α 1 := ⟨SingleReplica.e v, (SingleReplica.e v).history⟩
  have hn : NetworkReachable N := core_network_realization (SingleReplica.reachable v)
  have hs := network_system_realization hn
  let logs : Fin 1 → List α := fun _ => []
  refine ⟨⟨N, Function.update logs 0 [v]⟩, ?_, by simp⟩
  apply SystemReachable.next hs
  apply SystemStep.execute (b := SingleReplica.ballot) (Q := Finset.univ)
  · simp [Majority]
  · intro p hp
    have he : p = 0 := Fin.eq_zero p
    subst p
    simp [N, SingleReplica.e, acceptStep]

structure DistributedMultiPaxosConsensusSuite : Prop where
  quorum : ∀ {n} {Q R : Finset (Fin n)}, Majority Q → Majority R → ∃ p, p ∈ Q ∧ p ∈ R
  promise : ∀ {α : Type} {n} {c d : Config α n}, Step c d →
    ∀ p b, (c.nodes p).promised = some b → ∃ e, (d.nodes p).promised = some e ∧ b ≤ e
  invariant : ∀ {α : Type} {n} {c : Config α n}, Reachable c → Invariants c
  unique : ∀ {α : Type} {n} {c : Config α n}, Reachable c →
    ∀ {b s v w}, Proposed c b s v → Proposed c b s w → v = w
  preservation : ∀ {α : Type} {n} {c : Config α n}, Reachable c →
    ∀ {s b v}, Chosen c s b v → ∀ {d w}, b < d → Proposed c d s w → v = w
  agreement : ∀ {α : Type} {n} {c : Config α n}, Reachable c →
    ∀ {s b d v w}, Chosen c s b v → Chosen c s d w → v = w
  prefixes : ∀ {α : Type} {n} {S : System α n}, SystemReachable S → ∀ p q,
    (S.logs p).IsPrefix (S.logs q) ∨ (S.logs q).IsPrefix (S.logs p)
  machine : ∀ {α σ : Type} {n} {c : Config α n}, Reachable c →
    ∀ {L R}, Executed c L → Executed c R → L.length = R.length →
      ∀ (f : σ → α → σ) start, L.foldl f start = R.foldl f start
  network : ∀ {α : Type} {n} {N : Network α n}, NetworkReachable N →
    Reachable N.core ∧ ∀ m ∈ N.pending, m ∈ N.core.history
  finite_snapshot : ∀ {α : Type} [DecidableEq α] {n} {c : Config α n}, Reachable c →
    ∀ p, ExactSnapshot (c.nodes p) (serialize c p)
  legacy : ∀ {α : Type} {n} (hn : 0 < n) {c : Config α n}, Reachable c →
    ∀ s encode, DistributedPaxos.SingleVote (legacyAccepted hn c s encode)
  pipeline : Reachable Regression.c13 ∧ Regression.c13.active Regression.b0 = some Regression.C0 ∧
    Chosen Regression.c13 0 Regression.b0 7 ∧ Chosen Regression.c13 1 Regression.b0 8 ∧
    Chosen Regression.c13 2 Regression.b0 9
  singleton : ∀ {α : Type} (v : α), ∃ S : System α 1, SystemReachable S ∧ S.logs 0 = [v]
  bad_selection : ∃ c : Config ℕ 3, FaultReachable .ignoreMax c ∧
    Chosen c 0 Regression.b0 7 ∧ Chosen c 0 Regression.b1 9 ∧ (7 : ℕ) ≠ 9
  bad_reuse : ∃ c : Config ℕ 3, FaultReachable .reusedBallot c ∧
    Chosen c 0 Regression.b0 7 ∧ Chosen c 0 Regression.b0 9 ∧ (7 : ℕ) ≠ 9

theorem distributed_multi_paxos_consensus_master_suite : DistributedMultiPaxosConsensusSuite where
  quorum := quorum_intersection
  promise := promise_monotonicity
  invariant := reachable_invariants
  unique := proposal_uniqueness
  preservation := inter_ballot_value_preservation
  agreement := multi_paxos_slot_agreement
  prefixes := reachable_replica_prefixes
  machine := state_machine_convergence
  network := network_refinement
  finite_snapshot := serialize_exact
  legacy := derived_single_vote
  pipeline := Regression.three_slots_one_epoch
  singleton := singleton_execution
  bad_selection := counterexample_ignore_max_ballot
  bad_reuse := counterexample_reused_ballot

end DistributedMultiPaxosConsensus
