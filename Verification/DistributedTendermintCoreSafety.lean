/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Verification.DistributedPBFTConsensus
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Weighted Tendermint safety at one fixed height

An authenticated, asynchronous safety abstraction. Proposal selection and timers
are nondeterministic; certificates must be delivered. No liveness is asserted.
-/

namespace DistributedTendermintCoreSafety

open Finset

variable {n : ℕ}

structure Config (n : ℕ) where
  weight : Fin n → ℕ
  byzantine : Finset (Fin n)
  height : ℕ
  deriving DecidableEq

def Config.mass (c : Config n) (s : Finset (Fin n)) : ℕ := ∑ i ∈ s, c.weight i

def Config.total (c : Config n) : ℕ := c.mass univ

def Config.quorum (c : Config n) (s : Finset (Fin n)) : Prop := 2 * c.total < 3 * c.mass s

open Config

instance (c : Config n) (s : Finset (Fin n)) : Decidable (c.quorum s) :=
  inferInstanceAs (Decidable (2 * c.total < 3 * c.mass s))

theorem mass_mono (c : Config n) {s t : Finset (Fin n)} (h : s ⊆ t) :
    c.mass s ≤ c.mass t := Finset.sum_le_sum_of_subset h

theorem mass_le_total (c : Config n) (s : Finset (Fin n)) : c.mass s ≤ c.total :=
  mass_mono c (subset_univ s)

theorem quorum_total_positive (c : Config n) {s : Finset (Fin n)} (h : c.quorum s) :
    0 < c.total := by
  have := mass_le_total c s
  dsimp [quorum] at h
  omega

/-- Strict quorums even admit the non-strict one-third fault bound. -/
theorem quorum_honest_intersection (c : Config n) {s t : Finset (Fin n)}
    (hb : 3 * c.mass c.byzantine ≤ c.total) (hs : c.quorum s) (ht : c.quorum t) :
    ∃ i ∈ s ∩ t, i ∉ c.byzantine ∧ 0 < c.weight i := by
  have hu := mass_le_total c (s ∪ t)
  have hi : c.mass (s ∪ t) + c.mass (s ∩ t) = c.mass s + c.mass t :=
    Finset.sum_union_inter
  have hd : c.mass ((s ∩ t) \ c.byzantine) + c.mass ((s ∩ t) ∩ c.byzantine) =
      c.mass (s ∩ t) := by
    simpa [mass, add_comm] using Finset.sum_inter_add_sum_sdiff (s ∩ t) c.byzantine c.weight
  have hbi := mass_mono c (inter_subset_right : (s ∩ t) ∩ c.byzantine ⊆ c.byzantine)
  have hp : 0 < c.mass ((s ∩ t) \ c.byzantine) := by
    dsimp [quorum] at hs ht
    omega
  obtain ⟨i, hi, hw⟩ := (Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)).mp hp
  exact ⟨i, (mem_sdiff.mp hi).1, (mem_sdiff.mp hi).2, hw⟩

/-- Specialization to the contract's strict fault bound. -/
theorem quorum_honest_intersection_strict (c : Config n) {s t : Finset (Fin n)}
    (hb : 3 * c.mass c.byzantine < c.total) (hs : c.quorum s) (ht : c.quorum t) :
    ∃ i ∈ s ∩ t, i ∉ c.byzantine ∧ 0 < c.weight i :=
  quorum_honest_intersection c hb.le hs ht

inductive Phase where
  | prevote | precommit
  deriving DecidableEq, Repr

structure Vote (n : ℕ) where
  sender : Fin n
  round : ℕ
  phase : Phase
  value : Option ℕ
  deriving DecidableEq, Repr

/-- Message height is supplied by the enclosing fixed-height configuration. -/
def signers (votes : Finset (Vote n)) (p : Phase) (r : ℕ) (v : Option ℕ) : Finset (Fin n) :=
  univ.filter fun i => ⟨i, r, p, v⟩ ∈ votes

def polka (c : Config n) (votes : Finset (Vote n)) (r v : ℕ) : Prop :=
  c.quorum (signers votes .prevote r (some v))

def commit (c : Config n) (votes : Finset (Vote n)) (r v : ℕ) : Prop :=
  c.quorum (signers votes .precommit r (some v))

instance (c : Config n) (votes : Finset (Vote n)) (r v : ℕ) :
    Decidable (polka c votes r v) := inferInstanceAs (Decidable (c.quorum _))
instance (c : Config n) (votes : Finset (Vote n)) (r v : ℕ) :
    Decidable (commit c votes r v) := inferInstanceAs (Decidable (c.quorum _))

theorem polka_mono (c : Config n) {s t : Finset (Vote n)} (h : s ⊆ t) {r v : ℕ}
    (hp : polka c s r v) : polka c t r v := by
  have hm : signers s .prevote r (some v) ⊆ signers t .prevote r (some v) := by
    intro i hi
    simp only [signers, mem_filter, mem_univ, true_and] at hi ⊢
    exact h hi
  have := mass_mono c hm
  dsimp [polka, quorum] at hp ⊢
  omega

/-- Protocol-local history facts, later derived from executions. No agreement field. -/
structure History (c : Config n) (votes : Finset (Vote n)) : Prop where
  unique : ∀ i, i ∉ c.byzantine → ∀ r p a b,
    ⟨i, r, p, a⟩ ∈ votes → ⟨i, r, p, b⟩ ∈ votes → a = b
  certified : ∀ i, i ∉ c.byzantine → ∀ r v,
    ⟨i, r, .precommit, some v⟩ ∈ votes → polka c votes r v
  justified : ∀ i, i ∉ c.byzantine → ∀ r₀ u r v,
    ⟨i, r₀, .precommit, some u⟩ ∈ votes →
    ⟨i, r, .prevote, some v⟩ ∈ votes → r₀ < r →
    ∃ t, r₀ ≤ t ∧ t < r ∧ polka c votes t v

theorem same_round_unique (c : Config n) {votes : Finset (Vote n)} (h : History c votes)
    (hb : 3 * c.mass c.byzantine ≤ c.total) (p : Phase) (r u v : ℕ)
    (hu : c.quorum (signers votes p r (some u)))
    (hv : c.quorum (signers votes p r (some v))) : u = v := by
  obtain ⟨i, hi, hb', _⟩ := quorum_honest_intersection c hb hu hv
  have hm := mem_inter.mp hi
  have hh := h.unique i hb' r p (some u) (some v)
    (by simpa [signers] using hm.1) (by simpa [signers] using hm.2)
  exact Option.some.inj hh

theorem commit_has_polka (c : Config n) {votes : Finset (Vote n)} (h : History c votes)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r v : ℕ}
    (hc : commit c votes r v) : polka c votes r v := by
  obtain ⟨i, hi, hn, _⟩ := quorum_honest_intersection c hb hc hc
  exact h.certified i hn r v (by simpa [signers] using (mem_inter.mp hi).1)

/-- Strong induction on the later round; a lock escape requires an earlier polka. -/
theorem later_polka_unique (c : Config n) {votes : Finset (Vote n)} (h : History c votes)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r₀ u : ℕ} (hc : commit c votes r₀ u) :
    ∀ r, r₀ ≤ r → ∀ v, polka c votes r v → u = v := by
  intro r
  induction r using Nat.strong_induction_on with
  | h r ih =>
    intro hr v hp
    by_cases he : r₀ = r
    · subst r
      exact same_round_unique c h hb .prevote r₀ u v (commit_has_polka c h hb hc) hp
    · obtain ⟨i, hi, hn, _⟩ := quorum_honest_intersection c hb hc hp
      obtain ⟨t, ht, htr, htp⟩ := h.justified i hn r₀ u r v
        (by simpa [signers] using (mem_inter.mp hi).1)
        (by simpa [signers] using (mem_inter.mp hi).2) (by omega)
      exact ih t htr ht v htp

theorem history_safety (c : Config n) {votes : Finset (Vote n)} (h : History c votes)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r r' u v : ℕ}
    (hc : commit c votes r u) (hc' : commit c votes r' v) : u = v := by
  rcases le_total r r' with hr | hr
  · exact later_polka_unique c h hb hc r' hr v (commit_has_polka c h hb hc')
  · exact (later_polka_unique c h hb hc' r hr u (commit_has_polka c h hb hc)).symm


structure Proposal where
  round : ℕ
  value : ℕ
  validRound : Option ℕ
  deriving DecidableEq, Repr

structure LocalState (n : ℕ) where
  round : ℕ := 0
  lock : Option (ℕ × ℕ) := none
  valid : Option (ℕ × ℕ) := none
  inbox : Finset (Vote n) := ∅
  proposals : Finset Proposal := ∅
  deriving DecidableEq

def LocalState.lockedRound (l : LocalState n) : Option ℕ := l.lock.map Prod.fst
def LocalState.lockedValue (l : LocalState n) : Option ℕ := l.lock.map Prod.snd
def LocalState.validRound (l : LocalState n) : Option ℕ := l.valid.map Prod.fst
def LocalState.validValue (l : LocalState n) : Option ℕ := l.valid.map Prod.snd

structure State (n : ℕ) where
  votes : Finset (Vote n)
  nodes : Fin n → LocalState n
  deriving DecidableEq

def initial : State n := ⟨∅, fun _ => {}⟩

def atNode (s : State n) (i : Fin n) (l : LocalState n) : State n :=
  { s with nodes := Function.update s.nodes i l }

/-- The proposal's round hint is checked against a delivered quorum. -/
def proposalValid (c : Config n) (l : LocalState n) (p : Proposal) : Prop :=
  p ∈ l.proposals ∧ p.round = l.round ∧
    match p.validRound with
    | none => l.lock = none ∨ ∃ t, l.lock = some (t, p.value)
    | some vr => vr < l.round ∧ polka c l.inbox vr p.value ∧
        (l.lock = none ∨ ∃ t u, l.lock = some (t, u) ∧ (t ≤ vr ∨ u = p.value))

/-- Honest phase checks; nil votes preserve a lock. -/
def mayVote (c : Config n) (s : State n) (i : Fin n) (p : Phase) (v : Option ℕ) : Prop :=
  i ∉ c.byzantine ∧
  (∀ a, (⟨i, (s.nodes i).round, p, a⟩ : Vote n) ∉ s.votes) ∧
  match p, v with
  | .prevote, none => True
  | .prevote, some v => ∃ pr ∈ (s.nodes i).proposals,
      pr.value = v ∧ proposalValid c (s.nodes i) pr
  | .precommit, v =>
      (∃ a, (⟨i, (s.nodes i).round, .prevote, a⟩ : Vote n) ∈ s.votes) ∧
      match v with
      | none => True
      | some v => polka c (s.nodes i).inbox (s.nodes i).round v

def emit (s : State n) (i : Fin n) (p : Phase) (v : Option ℕ) : State n :=
  let l := s.nodes i
  let l' := match p, v with
    | .precommit, some v => { l with lock := some (l.round, v), valid := some (l.round, v) }
    | _, _ => l
  { votes := insert ⟨i, l.round, p, v⟩ s.votes, nodes := Function.update s.nodes i l' }

/-- Arbitrary delays, duplicates and proposal order are allowed. Byzantine senders
can emit any vote under their own identity. Proposal selection is overapproximated. -/
inductive Step (c : Config n) : State n → State n → Prop where
  | advance (s i r) (hr : (s.nodes i).round < r) :
      Step c s (atNode s i { s.nodes i with round := r })
  | deliver (s i msg) (hm : msg ∈ s.votes) :
      Step c s (atNode s i { s.nodes i with inbox := insert msg (s.nodes i).inbox })
  | propose (s i pr) :
      Step c s (atNode s i { s.nodes i with proposals := insert pr (s.nodes i).proposals })
  | honest (s i p v) (h : mayVote c s i p v) : Step c s (emit s i p v)
  | faulty (s msg) (hb : msg.sender ∈ c.byzantine) :
      Step c s { s with votes := insert msg s.votes }

inductive Reachable (c : Config n) : State n → Prop where
  | init : Reachable c initial
  | step {s t} : Reachable c s → Step c s t → Reachable c t

/-- These invariants contain only vote discipline, certificates and local lock facts. -/
structure Invariant (c : Config n) (s : State n) : Prop where
  history : History c s.votes
  delivered : ∀ i, (s.nodes i).inbox ⊆ s.votes
  rounds : ∀ i, i ∉ c.byzantine → ∀ r p v,
    ⟨i, r, p, v⟩ ∈ s.votes → r ≤ (s.nodes i).round
  lock_cert : ∀ i, i ∉ c.byzantine → ∀ t u, (s.nodes i).lock = some (t, u) →
    polka c s.votes t u ∧ t ≤ (s.nodes i).round ∧
      ∃ a, (⟨i, t, .prevote, a⟩ : Vote n) ∈ s.votes
  dominates : ∀ i, i ∉ c.byzantine → ∀ r v,
    ⟨i, r, .precommit, some v⟩ ∈ s.votes →
      ∃ t u, (s.nodes i).lock = some (t, u) ∧ r ≤ t
  valid_lock : ∀ i, (s.nodes i).valid = (s.nodes i).lock

theorem initial_invariant (c : Config n) : Invariant c initial := by
  constructor
  · constructor <;> simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]
  · simp [initial]

/-- Local delivery, proposals and round advancement do not change sent votes or locks. -/
theorem invariant_local (c : Config n) {s t : State n} (h : Invariant c s)
    (hv : t.votes = s.votes)
    (hl : ∀ i, (t.nodes i).lock = (s.nodes i).lock)
    (hr : ∀ i, (s.nodes i).round ≤ (t.nodes i).round)
    (hd : ∀ i, (t.nodes i).inbox ⊆ t.votes)
    (hh : ∀ i, (t.nodes i).valid = (t.nodes i).lock) : Invariant c t := by
  refine ⟨hv.symm ▸ h.history, hd, ?_, ?_, ?_, hh⟩
  · intro i hi r p v hm
    exact (h.rounds i hi r p v (hv ▸ hm)).trans (hr i)
  · intro i hi r v he
    obtain ⟨hp, hb, a, ha⟩ := h.lock_cert i hi r v ((hl i).symm.trans he)
    exact ⟨hv.symm ▸ hp, hb.trans (hr i), a, hv.symm ▸ ha⟩
  · intro i hi r v hm
    obtain ⟨k, u, hk, hu⟩ := h.dominates i hi r v (hv ▸ hm)
    exact ⟨k, u, (hl i).trans hk, hu⟩

/-- An honest block prevote after any earlier precommit has an intervening certificate. -/
theorem prevote_justification (c : Config n) {s : State n} (h : Invariant c s)
    {i : Fin n} {v r₀ u : ℕ} (hv : mayVote c s i .prevote (some v))
    (hp : (⟨i, r₀, .precommit, some u⟩ : Vote n) ∈ s.votes) :
    ∃ t, r₀ ≤ t ∧ t < (s.nodes i).round ∧ polka c s.votes t v := by
  obtain ⟨l, a, hl, hr⟩ := h.dominates i hv.1 r₀ u hp
  obtain ⟨hc, hle, b, hb⟩ := h.lock_cert i hv.1 l a hl
  have hlt : l < (s.nodes i).round := by
    have hn := hv.2.1 b
    by_contra he
    have heq : l = (s.nodes i).round := by omega
    exact hn (heq ▸ hb)
  obtain ⟨pr, _, he, hpr⟩ := hv.2.2
  rcases hpr with ⟨_, _, hg⟩
  cases hx : pr.validRound with
  | none =>
    simp only [hx, hl, Option.some_ne_none, false_or, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨t, _, ha⟩ := hg
    exact ⟨l, hr, hlt, (ha.trans he) ▸ hc⟩
  | some vr =>
    simp only [hx, hl, Option.some_ne_none, false_or, Option.some.injEq,
      Prod.mk.injEq] at hg
    obtain ⟨hvr, hpc, t, b, ⟨ht, hb⟩, hcase⟩ := hg
    rcases hcase with hcase | hcase
    · exact ⟨vr, by omega, hvr, he ▸ polka_mono c (h.delivered i) hpc⟩
    · exact ⟨l, hr, hlt, (hb.trans (hcase.trans he)) ▸ hc⟩


theorem invariant_faulty (c : Config n) {s : State n} (h : Invariant c s)
    (msg : Vote n) (hb : msg.sender ∈ c.byzantine) :
    Invariant c { s with votes := insert msg s.votes } := by
  have hm : ∀ i, i ∉ c.byzantine → ∀ r p v,
      (⟨i, r, p, v⟩ : Vote n) ∈ insert msg s.votes ↔
      (⟨i, r, p, v⟩ : Vote n) ∈ s.votes := by
    intro i hi r p v
    have hn : (⟨i, r, p, v⟩ : Vote n) ≠ msg := by
      intro he
      have hs : i = msg.sender := congrArg Vote.sender he
      exact hi (hs.symm ▸ hb)
    simp [hn]
  have grow : s.votes ⊆ insert msg s.votes := subset_insert _ _
  constructor
  · constructor
    · intro i hi r p a b ha hb
      exact h.history.unique i hi r p a b ((hm i hi r p a).mp ha) ((hm i hi r p b).mp hb)
    · intro i hi r v hv
      exact polka_mono c grow (h.history.certified i hi r v ((hm i hi r _ _).mp hv))
    · intro i hi r₀ u r v hpc hpv hr
      obtain ⟨t, ht, hl, hp⟩ := h.history.justified i hi r₀ u r v
        ((hm i hi r₀ _ _).mp hpc) ((hm i hi r _ _).mp hpv) hr
      exact ⟨t, ht, hl, polka_mono c grow hp⟩
  · intro i
    exact (h.delivered i).trans grow
  · intro i hi r p v hv
    exact h.rounds i hi r p v ((hm i hi r p v).mp hv)
  · intro i hi r v he
    obtain ⟨hp, hr, a, ha⟩ := h.lock_cert i hi r v he
    exact ⟨polka_mono c grow hp, hr, a, grow ha⟩
  · intro i hi r v hv
    exact h.dominates i hi r v ((hm i hi r _ _).mp hv)
  · exact h.valid_lock

theorem invariant_emit (c : Config n) {s : State n} (h : Invariant c s)
    {i : Fin n} {p : Phase} {v : Option ℕ} (hv : mayVote c s i p v) :
    Invariant c (emit s i p v) := by
  have grow : s.votes ⊆ (emit s i p v).votes := subset_insert _ _
  have rounds : ∀ j, ((emit s i p v).nodes j).round = (s.nodes j).round := by
    intro j
    by_cases he : j = i
    · subst j; cases p <;> cases v <;> simp [emit]
    · cases p <;> cases v <;> simp [emit, Function.update_of_ne he]
  have inbox : ∀ j, ((emit s i p v).nodes j).inbox = (s.nodes j).inbox := by
    intro j
    by_cases he : j = i
    · subst j; cases p <;> cases v <;> simp [emit]
    · cases p <;> cases v <;> simp [emit, Function.update_of_ne he]
  have unchanged : ∀ j, j ≠ i → ((emit s i p v).nodes j).lock = (s.nodes j).lock := by
    intro j hj
    simp [emit, Function.update_of_ne hj]
  constructor
  · constructor
    · intro j hj r ph a b ha hb
      rcases mem_insert.mp ha with haNew | haOld <;> rcases mem_insert.mp hb with hbNew | hbOld
      · exact congrArg Vote.value (haNew.trans hbNew.symm)
      · simp only [Vote.mk.injEq] at haNew
        rcases haNew with ⟨rfl, rfl, rfl, rfl⟩
        exact False.elim (hv.2.1 b hbOld)
      · simp only [Vote.mk.injEq] at hbNew
        rcases hbNew with ⟨rfl, rfl, rfl, rfl⟩
        exact False.elim (hv.2.1 a haOld)
      · exact h.history.unique j hj r ph a b haOld hbOld
    · intro j hj r a ha
      rcases mem_insert.mp ha with haNew | haOld
      · simp only [Vote.mk.injEq] at haNew
        rcases haNew with ⟨rfl, rfl, rfl, rfl⟩
        exact polka_mono c ((h.delivered j).trans grow) hv.2.2.2
      · exact polka_mono c grow (h.history.certified j hj r a haOld)
    · intro j hj r₀ u r a hpc hpv hr
      rcases mem_insert.mp hpc with hpcNew | hpcOld
      · simp only [Vote.mk.injEq] at hpcNew
        rcases hpcNew with ⟨rfl, rfl, rfl, rfl⟩
        have hpvOld : (⟨j, r, .prevote, some a⟩ : Vote n) ∈ s.votes := by
          simpa [emit, Vote.mk.injEq] using hpv
        have := h.rounds j hj r .prevote (some a) hpvOld
        omega
      · rcases mem_insert.mp hpv with hpvNew | hpvOld
        · simp only [Vote.mk.injEq] at hpvNew
          rcases hpvNew with ⟨rfl, rfl, rfl, rfl⟩
          obtain ⟨t, ht, hl, hp⟩ := prevote_justification c h hv hpcOld
          exact ⟨t, ht, hl, polka_mono c grow hp⟩
        · obtain ⟨t, ht, hl, hp⟩ := h.history.justified j hj r₀ u r a hpcOld hpvOld hr
          exact ⟨t, ht, hl, polka_mono c grow hp⟩
  · intro j
    rw [inbox j]
    exact (h.delivered j).trans grow
  · intro j hj r ph a ha
    rw [rounds j]
    rcases mem_insert.mp ha with haNew | haOld
    · simp only [Vote.mk.injEq] at haNew
      rcases haNew with ⟨rfl, rfl, _, _⟩
      exact le_rfl
    · exact h.rounds j hj r ph a haOld
  · intro j hj t u hl
    by_cases he : j = i
    · subst j
      cases p with
      | prevote =>
        have hl' : (s.nodes i).lock = some (t, u) := by simpa [emit] using hl
        obtain ⟨hp, hr, a, ha⟩ := h.lock_cert i hj t u hl'
        exact ⟨polka_mono c grow hp, (rounds i).symm ▸ hr, a, grow ha⟩
      | precommit =>
        cases v with
        | none =>
          have hl' : (s.nodes i).lock = some (t, u) := by simpa [emit] using hl
          obtain ⟨hp, hr, a, ha⟩ := h.lock_cert i hj t u hl'
          exact ⟨polka_mono c grow hp, (rounds i).symm ▸ hr, a, grow ha⟩
        | some v =>
          have hl' : (s.nodes i).round = t ∧ v = u := by simpa [emit] using hl
          obtain ⟨a, ha⟩ := hv.2.2.1
          refine ⟨?_, ?_, a, ?_⟩
          · exact hl'.1 ▸ hl'.2 ▸ polka_mono c ((h.delivered i).trans grow) hv.2.2.2
          · rw [rounds i, hl'.1]
          · exact hl'.1 ▸ grow ha
    · have hl' : (s.nodes j).lock = some (t, u) := (unchanged j he).symm.trans hl
      obtain ⟨hp, hr, a, ha⟩ := h.lock_cert j hj t u hl'
      exact ⟨polka_mono c grow hp, (rounds j).symm ▸ hr, a, grow ha⟩
  · intro j hj r a ha
    rcases mem_insert.mp ha with haNew | haOld
    · simp only [Vote.mk.injEq] at haNew
      rcases haNew with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨(s.nodes j).round, a, by simp [emit], le_rfl⟩
    · obtain ⟨t, u, hl, hr⟩ := h.dominates j hj r a haOld
      by_cases he : j = i
      · subst j
        cases p with
        | prevote => exact ⟨t, u, by simpa [emit] using hl, hr⟩
        | precommit =>
          cases v with
          | none => exact ⟨t, u, by simpa [emit] using hl, hr⟩
          | some v => exact ⟨(s.nodes i).round, v, by simp [emit],
              h.rounds i hj r .precommit (some a) haOld⟩
      · exact ⟨t, u, (unchanged j he).trans hl, hr⟩
  · intro j
    by_cases he : j = i
    · subst j; cases p <;> cases v <;> simp [emit, h.valid_lock]
    · simp [emit, Function.update_of_ne he, h.valid_lock]

theorem step_invariant (c : Config n) {s t : State n} (h : Invariant c s)
    (st : Step c s t) : Invariant c t := by
  cases st with
  | honest i p v hv => exact invariant_emit c h hv
  | faulty msg hb => exact invariant_faulty c h msg hb
  | advance i r hr =>
    apply invariant_local c h (t := atNode s i { s.nodes i with round := r }) rfl
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne]
    · intro j; by_cases he : j = i
      · subst j; simpa [atNode] using hr.le
      · simp [atNode, Function.update_of_ne he]
    · intro j; by_cases he : j = i
      · subst j; simpa [atNode] using h.delivered i
      · simpa [atNode, Function.update_of_ne he] using h.delivered j
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne, h.valid_lock]
  | deliver i msg hm =>
    apply invariant_local c h
      (t := atNode s i { s.nodes i with inbox := insert msg (s.nodes i).inbox }) rfl
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne]
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne]
    · intro j; by_cases he : j = i
      · subst j; simpa [atNode] using insert_subset hm (h.delivered i)
      · simpa [atNode, Function.update_of_ne he] using h.delivered j
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne, h.valid_lock]
  | propose i pr =>
    apply invariant_local c h
      (t := atNode s i { s.nodes i with proposals := insert pr (s.nodes i).proposals }) rfl
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne]
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne]
    · intro j; by_cases he : j = i
      · subst j; simpa [atNode] using h.delivered i
      · simpa [atNode, Function.update_of_ne he] using h.delivered j
    · intro j; by_cases he : j = i <;> simp [atNode, he, Function.update_of_ne, h.valid_lock]

theorem reachable_invariant (c : Config n) {s : State n} (hs : Reachable c s) :
    Invariant c s := by
  induction hs with
  | init => exact initial_invariant c
  | step _ st ih => exact step_invariant c ih st

/-- Agreement follows from reachability, not from a condition in Step. -/
theorem tendermint_core_safety (c : Config n) {s : State n} (hs : Reachable c s)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r r' u v : ℕ}
    (hu : commit c s.votes r u) (hv : commit c s.votes r' v) : u = v :=
  history_safety c (reachable_invariant c hs).history hb hu hv

theorem same_round_polka_unique (c : Config n) {s : State n} (hs : Reachable c s)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r u v : ℕ}
    (hu : polka c s.votes r u) (hv : polka c s.votes r v) : u = v :=
  same_round_unique c (reachable_invariant c hs).history hb .prevote r u v hu hv

theorem same_round_commit_unique (c : Config n) {s : State n} (hs : Reachable c s)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r u v : ℕ}
    (hu : commit c s.votes r u) (hv : commit c s.votes r v) : u = v :=
  tendermint_core_safety c hs hb hu hv

theorem locked_quorum_preservation (c : Config n) {s : State n} (hs : Reachable c s)
    (hb : 3 * c.mass c.byzantine ≤ c.total) {r₀ v : ℕ} (hc : commit c s.votes r₀ v) :
    (∀ r, r₀ ≤ r → ∀ u, polka c s.votes r u → v = u) ∧
    (∀ i, i ∉ c.byzantine → (⟨i, r₀, .precommit, some v⟩ : Vote n) ∈ s.votes →
      ∃ t, r₀ ≤ t ∧ (s.nodes i).lock = some (t, v)) := by
  have h := reachable_invariant c hs
  have hp := later_polka_unique c h.history hb hc
  refine ⟨hp, ?_⟩
  intro i hi hm
  obtain ⟨t, u, hl, ht⟩ := h.dominates i hi r₀ v hm
  have he := hp t ht u (h.lock_cert i hi t u hl).1
  exact ⟨t, ht, he ▸ hl⟩

/-- A threshold implication, not an evidence extraction or slashing algorithm. -/
theorem accountable_safety_contrapositive (c : Config n) {s : State n}
    (hs : Reachable c s) {r r' u v : ℕ}
    (hu : commit c s.votes r u) (hv : commit c s.votes r' v) (hne : u ≠ v) :
    c.total < 3 * c.mass c.byzantine := by
  by_contra hb
  exact hne (tendermint_core_safety c hs (by omega) hu hv)


def voteValues (votes : Finset (Vote n)) (i : Fin n) (r : ℕ) (p : Phase) : Finset (Option ℕ) :=
  (votes.filter fun msg => msg.sender = i ∧ msg.round = r ∧ msg.phase = p).image Vote.value

theorem mem_voteValues (votes : Finset (Vote n)) (i : Fin n) (r : ℕ) (p : Phase) (a : Option ℕ) :
    a ∈ voteValues votes i r p ↔ (⟨i, r, p, a⟩ : Vote n) ∈ votes := by
  simp only [voteValues, mem_image, mem_filter]
  constructor
  · rintro ⟨⟨j, t, ph, b⟩, ⟨hm, hj, ht, hp⟩, hb⟩
    dsimp at hj ht hp hb
    subst j; subst t; subst ph; subst b
    exact hm
  · intro hm
    exact ⟨⟨i, r, p, a⟩, ⟨hm, rfl, rfl, rfl⟩, rfl⟩

instance (votes : Finset (Vote n)) (i : Fin n) (r : ℕ) (p : Phase) :
    Decidable (∃ a, (⟨i, r, p, a⟩ : Vote n) ∈ votes) :=
  decidable_of_iff (voteValues votes i r p).Nonempty
    (by simp only [Finset.Nonempty, mem_voteValues])

instance (votes : Finset (Vote n)) (i : Fin n) (r : ℕ) (p : Phase) :
    Decidable (∀ a, (⟨i, r, p, a⟩ : Vote n) ∉ votes) :=
  decidable_of_iff (¬ ∃ a, (⟨i, r, p, a⟩ : Vote n) ∈ votes) (by simp)

def proposalCondition (c : Config n) (l : LocalState n) (p : Proposal) : Prop :=
  p ∈ l.proposals ∧ p.round = l.round ∧
    match p.validRound, l.lock with
    | none, none => True
    | none, some (_, u) => u = p.value
    | some vr, none => vr < l.round ∧ polka c l.inbox vr p.value
    | some vr, some (t, u) =>
        vr < l.round ∧ polka c l.inbox vr p.value ∧ (t ≤ vr ∨ u = p.value)

instance (c : Config n) (l : LocalState n) (p : Proposal) :
    Decidable (proposalCondition c l p) := by
  unfold proposalCondition
  cases p.validRound <;> cases l.lock <;> infer_instance

theorem proposalCondition_iff (c : Config n) (l : LocalState n) (p : Proposal) :
    proposalCondition c l p ↔ proposalValid c l p := by
  cases hl : l.lock with
  | none => cases hp : p.validRound <;> simp [proposalCondition, proposalValid, hl, hp]
  | some pair =>
    rcases pair with ⟨t, v⟩
    cases hp : p.validRound <;> simp [proposalCondition, proposalValid, hl, hp]

instance (c : Config n) (l : LocalState n) (p : Proposal) : Decidable (proposalValid c l p) :=
  decidable_of_iff (proposalCondition c l p) (proposalCondition_iff c l p)

instance (c : Config n) (s : State n) (i : Fin n) (p : Phase) (v : Option ℕ) :
    Decidable (mayVote c s i p v) := by
  unfold mayVote
  cases p <;> cases v <;> infer_instance

inductive Action (n : ℕ) where
  | advance (i : Fin n) (round : ℕ)
  | deliver (i : Fin n) (msg : Vote n)
  | propose (i : Fin n) (pr : Proposal)
  | honest (i : Fin n) (phase : Phase) (value : Option ℕ)
  | faulty (msg : Vote n)
  deriving DecidableEq, Repr

/-- A checked, executable interpreter of the safety transition relation. -/
def execute (c : Config n) (s : State n) : Action n → Option (State n)
  | .advance i r => if (s.nodes i).round < r then
      some (atNode s i { s.nodes i with round := r }) else none
  | .deliver i msg => if msg ∈ s.votes then
      some (atNode s i { s.nodes i with inbox := insert msg (s.nodes i).inbox }) else none
  | .propose i pr =>
      some (atNode s i { s.nodes i with proposals := insert pr (s.nodes i).proposals })
  | .honest i p v => if mayVote c s i p v then some (emit s i p v) else none
  | .faulty msg => if msg.sender ∈ c.byzantine then
      some { s with votes := insert msg s.votes } else none

theorem execute_sound (c : Config n) {s t : State n} {a : Action n}
    (he : execute c s a = some t) : Step c s t := by
  cases a with
  | advance i r =>
    simp only [execute] at he
    split at he
    · cases Option.some.inj he; exact Step.advance s i r ‹_›
    · contradiction
  | deliver i msg =>
    simp only [execute] at he
    split at he
    · cases Option.some.inj he; exact Step.deliver s i msg ‹_›
    · contradiction
  | propose i pr =>
    cases Option.some.inj he; exact Step.propose s i pr
  | honest i p v =>
    simp only [execute] at he
    split at he
    · cases Option.some.inj he; exact Step.honest s i p v ‹_›
    · contradiction
  | faulty msg =>
    simp only [execute] at he
    split at he
    · cases Option.some.inj he; exact Step.faulty s msg ‹_›
    · contradiction

theorem execute_complete (c : Config n) {s t : State n} (h : Step c s t) :
    ∃ a, execute c s a = some t := by
  cases h with
  | advance i r hr => exact ⟨.advance i r, by simp [execute, hr]⟩
  | deliver i msg hm => exact ⟨.deliver i msg, by simp [execute, hm]⟩
  | propose i pr => exact ⟨.propose i pr, rfl⟩
  | honest i p v hv => exact ⟨.honest i p v, by simp [execute, hv]⟩
  | faulty msg hb => exact ⟨.faulty msg, by simp [execute, hb]⟩

def run (c : Config n) (s : State n) : List (Action n) → Option (State n)
  | [] => some s
  | a :: rest => (execute c s a).bind fun t => run c t rest

theorem run_reachable (c : Config n) (actions : List (Action n)) {s t : State n}
    (hs : Reachable c s) (he : run c s actions = some t) : Reachable c t := by
  induction actions generalizing s with
  | nil => cases Option.some.inj he; exact hs
  | cons a rest ih =>
    simp only [run] at he
    cases hx : execute c s a with
    | none => simp [hx] at he
    | some u => exact ih (Reachable.step hs (execute_sound c hx)) (by simpa [hx] using he)

def executeAtHeight (c : Config n) (height : ℕ) (s : State n) (a : Action n) : Option (State n) :=
  if height = c.height then execute c s a else none

theorem wrong_height_rejected (c : Config n) (height : ℕ) (s : State n) (a : Action n)
    (h : height ≠ c.height) : executeAtHeight c height s a = none := by
  simp [executeAtHeight, h]

theorem step_votes_mono (c : Config n) {s t : State n} (h : Step c s t) :
    s.votes ⊆ t.votes := by
  cases h <;> first | exact subset_insert _ _ | exact Subset.rfl

/-- Any delivery ordering admitted by run inherits safety; no fairness assumption. -/
theorem execution_safety (c : Config n) (actions : List (Action n)) {s : State n}
    (he : run c initial actions = some s) (hb : 3 * c.mass c.byzantine ≤ c.total)
    {r r' u v : ℕ} (hu : commit c s.votes r u) (hv : commit c s.votes r' v) : u = v :=
  tendermint_core_safety c (run_reachable c actions Reachable.init he) hb hu hv

/-- Deduplication concerns the signer's identity, not the number of network copies. -/
theorem duplicate_vote_idempotent (c : Config n) (votes : Finset (Vote n)) (msg : Vote n)
    (p : Phase) (r : ℕ) (v : Option ℕ) :
    c.mass (signers (insert msg (insert msg votes)) p r v) =
      c.mass (signers (insert msg votes) p r v) := by simp

theorem duplicate_delivery (c : Config n) (s : State n) (i : Fin n) (msg : Vote n)
    (hs : msg ∈ s.votes) (hi : msg ∈ (s.nodes i).inbox) :
    execute c s (.deliver i msg) = some s := by
  simp [execute, hs, Finset.insert_eq_of_mem hi, atNode, Function.update_eq_self]


def witnessConfig : Config 1 := ⟨fun _ => 1, ∅, 7⟩

def witnessTrace : List (Action 1) :=
  [.propose 0 ⟨0, 9, none⟩, .honest 0 .prevote (some 9),
   .deliver 0 ⟨0, 0, .prevote, some 9⟩, .honest 0 .precommit (some 9)]

def witnessState : State 1 := (run witnessConfig initial witnessTrace).getD initial

theorem witness_execution : run witnessConfig initial witnessTrace = some witnessState := by
  decide +kernel

theorem nonvacuous_commit : Reachable witnessConfig witnessState ∧
    commit witnessConfig witnessState.votes 0 9 ∧
    3 * witnessConfig.mass witnessConfig.byzantine < witnessConfig.total := by
  refine ⟨run_reachable witnessConfig witnessTrace Reachable.init witness_execution, ?_⟩
  decide +kernel

structure DistributedTendermintCoreSafetySuite : Prop where
  intersection : ∀ (n) (c : Config n) (s t), 3 * c.mass c.byzantine ≤ c.total →
    c.quorum s → c.quorum t → ∃ i ∈ s ∩ t, i ∉ c.byzantine ∧ 0 < c.weight i
  invariant : ∀ (n) (c : Config n) (s), Reachable c s → Invariant c s
  safety : ∀ (n) (c : Config n) (s), Reachable c s → 3 * c.mass c.byzantine ≤ c.total →
    ∀ r r' u v, commit c s.votes r u → commit c s.votes r' v → u = v
  execution : ∀ (n) (c : Config n) (s t a), execute c s a = some t → Step c s t
  accountability_boundary : ∀ (n) (c : Config n) (s), Reachable c s →
    ∀ r r' u v, commit c s.votes r u → commit c s.votes r' v → u ≠ v →
      c.total < 3 * c.mass c.byzantine

theorem verification_suite : DistributedTendermintCoreSafetySuite where
  intersection _ c _ _ := quorum_honest_intersection c
  invariant _ c _ := reachable_invariant c
  safety _ c _ hs hb _ _ _ _ := tendermint_core_safety c hs hb
  execution _ c _ _ _ := execute_sound c
  accountability_boundary _ c _ hs _ _ _ _ := accountable_safety_contrapositive c hs

end DistributedTendermintCoreSafety
