/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedMultiPaxosConsensus
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FinCases

/-! Exact agreement is impossible for deterministic two-process protocols with
any fixed finite round horizon and arbitrary independent message omissions.
Messages are computed from the pre-round states; delivery has no sender feedback.
Self-delivery flags are ignored. No indistinguishability axiom is assumed. -/
namespace DistributedCoordinatedAttackImpossibility

abbrev Process := Fin 2
abbrev Decision := Fin 2
abbrev DeliverySchedule (T : ℕ) := Process → Process → Fin T → Bool
abbrev Inputs := Process → Decision

def other (p : Process) : Process := if p = 0 then 1 else 0

@[simp] theorem other_other (p : Process) : other (other p) = p := by
  fin_cases p <;> decide
@[simp] theorem other_ne (p : Process) : other p ≠ p := by
  fin_cases p <;> decide

structure Protocol (T : ℕ) (Msg State : Type) where
  initial_state : Process → Decision → State
  send_msg : Process → Fin T → State → Msg
  step : Process → Fin T → State → Option Msg → State
  decide : Process → State → Decision

variable {T : ℕ} {Msg State : Type}

def execution (P : Protocol T Msg State) (x : Inputs) (D : DeliverySchedule T) :
    ℕ → Process → State
  | 0 => fun p => P.initial_state p (x p)
  | t + 1 => if h : t < T then fun p =>
      P.step p ⟨t, h⟩ (execution P x D t p)
        (if D (other p) p ⟨t, h⟩ then
          some (P.send_msg (other p) ⟨t, h⟩ (execution P x D t (other p))) else none)
    else execution P x D t

def decision (P : Protocol T Msg State) (x : Inputs) (D : DeliverySchedule T)
    (p : Process) : Decision := P.decide p (execution P x D T p)
def common_decision (P : Protocol T Msg State) (x : Inputs) (D : DeliverySchedule T) :=
  decision P x D 0

def sched_all : DeliverySchedule T := fun _ _ _ => true
def sched_empty : DeliverySchedule T := fun _ _ _ => false

def Agreement (P : Protocol T Msg State) : Prop :=
  ∀ x D, decision P x D 0 = decision P x D 1
def ValidityZero (P : Protocol T Msg State) : Prop :=
  ∀ D p, decision P (fun _ => 0) D p = 0
def ReliableSuccess (P : Protocol T Msg State) : Prop :=
  ∀ p, decision P (fun _ => 1) sched_all p = 1

def eraseDelivery (D : DeliverySchedule T) (s : Process) (r : Fin T) :
    DeliverySchedule T := fun a b t =>
  if a = s ∧ b = other s ∧ t = r then false else D a b t

/-- Only incoming flags affect a step. Histories before the changed round agree. -/
theorem execution_congr_before (P : Protocol T Msg State) (x : Inputs)
    (D E : DeliverySchedule T) (n : ℕ)
    (h : ∀ t : Fin T, t.val < n → ∀ p, D (other p) p t = E (other p) p t) :
    execution P x D n = execution P x E n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := ih (fun t ht p => h t (by omega) p)
    simp only [execution]
    split_ifs with hnT
    · funext p
      rw [hn, h ⟨n, hnT⟩ (show n < n + 1 from Nat.lt_succ_self n) p]
    · exact hn

theorem erase_before (P : Protocol T Msg State) (x : Inputs)
    (D : DeliverySchedule T) (s : Process) (r : Fin T) (n : ℕ) (hn : n ≤ r.val) :
    execution P x (eraseDelivery D s r) n = execution P x D n := by
  apply execution_congr_before
  intro t ht p
  have htr : t ≠ r := by intro he; subst t; omega
  simp [eraseDelivery, htr]

theorem local_state_independent_of_undelivered_msg (P : Protocol T Msg State)
    (x : Inputs) (D : DeliverySchedule T) (s : Process) (r : Fin T) :
    execution P x (eraseDelivery D s r) (r.val + 1) s =
      execution P x D (r.val + 1) s := by
  have he := erase_before P x D s r r.val (by omega)
  simp only [execution, dif_pos r.isLt]
  rw [he]
  simp [eraseDelivery]

/-- There are no later cross-process deliveries in the original schedule. -/
def LastDeliveryRound (D : DeliverySchedule T) (r : Fin T) : Prop :=
  ∀ t : Fin T, r.val < t.val → ∀ p, D p (other p) t = false

theorem last_delivery_removal_indistinguishability (P : Protocol T Msg State)
    (x : Inputs) (D : DeliverySchedule T) (s : Process) (r : Fin T)
    (hlast : LastDeliveryRound D r) (n : ℕ) :
    execution P x (eraseDelivery D s r) n s = execution P x D n s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hnr : n < r.val
    · exact congrFun (erase_before P x D s r (n + 1) (by omega)) s
    by_cases heq : n = r.val
    · subst n
      exact local_state_independent_of_undelivered_msg P x D s r
    have hrn : r.val < n := by omega
    simp only [execution]
    split_ifs with hnT
    · have hd := hlast ⟨n, hnT⟩ hrn (other s)
      simp only [other_other] at hd
      simp [eraseDelivery, hd, ih]
    · exact ih

theorem agreement_at (P : Protocol T Msg State) (h : Agreement P)
    (x : Inputs) (D : DeliverySchedule T) (p : Process) :
    common_decision P x D = decision P x D p := by
  fin_cases p
  · rfl
  · exact h x D

theorem last_delivery_preserves_decision (P : Protocol T Msg State) (h : Agreement P)
    (x : Inputs) (D : DeliverySchedule T) (s : Process) (r : Fin T)
    (hlast : LastDeliveryRound D r) :
    common_decision P x (eraseDelivery D s r) = common_decision P x D := by
  rw [agreement_at P h x _ s, agreement_at P h x D s]
  exact congrArg (P.decide s) (last_delivery_removal_indistinguishability P x D s r hlast T)

/-- Count actual cross-process deliveries, never unused self flags. -/
def deliveries (D : DeliverySchedule T) : Finset (Fin T × Process) :=
  Finset.univ.filter (fun e => D e.2 (other e.2) e.1 = true)

@[simp] theorem mem_deliveries (D : DeliverySchedule T) (e : Fin T × Process) :
    e ∈ deliveries D ↔ D e.2 (other e.2) e.1 = true := by
  simp [deliveries]

theorem deliveries_erase (D : DeliverySchedule T) (s : Process) (r : Fin T) :
    deliveries (eraseDelivery D s r) = (deliveries D).erase (r, s) := by
  ext ⟨t, p⟩
  simp only [mem_deliveries, Finset.mem_erase, eraseDelivery]
  by_cases hs : p = s
  · subst p
    by_cases hr : t = r
    · subst t
      simp
    · simp [hr]
  · simp [hs]

theorem exists_last_delivery (D : DeliverySchedule T) (h : (deliveries D).Nonempty) :
    ∃ (r : Fin T) (s : Process), (r, s) ∈ deliveries D ∧ LastDeliveryRound D r := by
  let rounds := (deliveries D).image Prod.fst
  have hr : rounds.Nonempty := h.image Prod.fst
  let r := rounds.max' hr
  have hm : r ∈ rounds := Finset.max'_mem rounds hr
  obtain ⟨e, he, her⟩ := Finset.mem_image.mp hm
  refine ⟨r, e.2, ?_, ?_⟩
  · simpa [← her] using he
  · intro t ht p
    cases hd : D p (other p) t with
    | false => rfl
    | true =>
      have hdmem : (t, p) ∈ deliveries D := (mem_deliveries D _).mpr hd
      have htmem : t ∈ rounds := Finset.mem_image.mpr ⟨(t, p), hdmem, rfl⟩
      have hle : t ≤ r := Finset.le_max' rounds t htmem
      have : t.val ≤ r.val := hle
      omega

theorem empty_deliveries_execution (P : Protocol T Msg State) (x : Inputs)
    (D : DeliverySchedule T) (h : deliveries D = ∅) (n : ℕ) :
    execution P x D n = execution P x sched_empty n := by
  apply execution_congr_before
  intro t _ p
  have hn : (t, other p) ∉ deliveries D := by simp [h]
  simp only [mem_deliveries, other_other] at hn
  cases hd : D (other p) p t with
  | false => rfl
  | true => exact False.elim (hn hd)

/-- Strong induction strictly decreases the number of actual deliveries. -/
theorem schedule_reduction_to_empty (P : Protocol T Msg State) (h : Agreement P)
    (x : Inputs) (D : DeliverySchedule T) :
    common_decision P x D = common_decision P x sched_empty := by
  generalize hn : (deliveries D).card = n
  induction n using Nat.strong_induction_on generalizing D with
  | h n ih =>
    by_cases he : deliveries D = ∅
    · exact congrArg (fun f => P.decide 0 (f 0)) (empty_deliveries_execution P x D he T)
    obtain ⟨r, s, hm, hl⟩ := exists_last_delivery D (Finset.nonempty_iff_ne_empty.mpr he)
    have hlt : (deliveries (eraseDelivery D s r)).card < n := by
      rw [deliveries_erase, ← hn]
      exact Finset.card_erase_lt_of_mem hm
    exact (last_delivery_preserves_decision P h x D s r hl).symm.trans
      (ih _ hlt _ rfl)

/-- In the empty schedule, a local state depends only on that process's input. -/
theorem empty_local_input (P : Protocol T Msg State) (x y : Inputs) (p : Process)
    (hp : x p = y p) (n : ℕ) :
    execution P x sched_empty n p = execution P y sched_empty n p := by
  induction n with
  | zero => simp [execution, hp]
  | succ n ih =>
    simp only [execution]
    split_ifs <;> simp [sched_empty, ih]

theorem input_flip_indistinguishability (P : Protocol T Msg State) (h : Agreement P)
    (x y : Inputs) : common_decision P x sched_empty = common_decision P y sched_empty := by
  let z : Inputs := fun p => if p = 0 then x 0 else y 1
  have h0 : decision P x sched_empty 0 = decision P z sched_empty 0 :=
    congrArg (P.decide 0) (empty_local_input P x z 0 (by simp [z]) T)
  have h1 : decision P z sched_empty 1 = decision P y sched_empty 1 :=
    congrArg (P.decide 1) (empty_local_input P z y 1 (by simp [z]) T)
  exact h0.trans ((h z sched_empty).trans (h1.trans (h y sched_empty).symm))

theorem no_delivery_forces_retreat (P : Protocol T Msg State) (ha : Agreement P)
    (hv : ValidityZero P) (x : Inputs) (p : Process) : decision P x sched_empty p = 0 := by
  rw [← agreement_at P ha]
  exact (input_flip_indistinguishability P ha x (fun _ => 0)).trans (hv sched_empty 0)

theorem all_schedules_force_retreat (P : Protocol T Msg State) (ha : Agreement P)
    (hv : ValidityZero P) (x : Inputs) (D : DeliverySchedule T) (p : Process) :
    decision P x D p = 0 := by
  rw [← agreement_at P ha]
  exact (schedule_reduction_to_empty P ha x D).trans (no_delivery_forces_retreat P ha hv x 0)

theorem coordinated_attack_impossibility (P : Protocol T Msg State) :
    ¬ (Agreement P ∧ ValidityZero P ∧ ReliableSuccess P) := by
  rintro ⟨ha, hv, hs⟩
  have hz := all_schedules_force_retreat P ha hv (fun _ => 1) sched_all 0
  have ho := hs 0
  rw [hz] at ho
  exact (by decide : (0 : Decision) ≠ 1) ho

/-- Existential version quantifies over all local-state and message types. -/
theorem no_correct_protocol (T : ℕ) :
    ¬ ∃ (Msg State : Type) (P : Protocol T Msg State),
      Agreement P ∧ ValidityZero P ∧ ReliableSuccess P := by
  rintro ⟨Msg, State, P, h⟩
  exact coordinated_attack_impossibility P h

def retreatProtocol (T : ℕ) : Protocol T Unit Unit where
  initial_state := fun _ _ => ()
  send_msg := fun _ _ _ => ()
  step := fun _ _ _ _ => ()
  decide := fun _ _ => 0

theorem trivial_retreat_protocol_satisfies_partial (T : ℕ) :
    Agreement (retreatProtocol T) ∧ ValidityZero (retreatProtocol T) ∧
      ¬ ReliableSuccess (retreatProtocol T) := by
  refine ⟨by intro x D; rfl, by intro D p; rfl, ?_⟩
  intro h
  exact (by decide : (0 : Decision) ≠ 1) (h 0)

theorem zero_horizon_impossibility (P : Protocol 0 Msg State) :
    ¬ (Agreement P ∧ ValidityZero P ∧ ReliableSuccess P) :=
  coordinated_attack_impossibility P

/-- Changing the order of two erasures produces the same schedule, without Agreement. -/
theorem erase_deliveries_commute (D : DeliverySchedule T)
    (s t : Process) (r u : Fin T) :
    eraseDelivery (eraseDelivery D s r) t u = eraseDelivery (eraseDelivery D t u) s r := by
  funext a b v
  simp only [eraseDelivery]
  split_ifs <;> rfl

theorem cancellation_order_invariance (P : Protocol T Msg State) (x : Inputs)
    (D : DeliverySchedule T) (s t : Process) (r u : Fin T) :
    common_decision P x (eraseDelivery (eraseDelivery D s r) t u) =
      common_decision P x (eraseDelivery (eraseDelivery D t u) s r) := by
  rw [erase_deliveries_commute]

theorem last_round_after_erase (D : DeliverySchedule T) (r : Fin T)
    (h : LastDeliveryRound D r) (s : Process) : LastDeliveryRound (eraseDelivery D s r) r := by
  intro t ht p
  have he : t ≠ r := by intro he; subst t; omega
  simp [eraseDelivery, he, h t ht p]

theorem independent_last_round_cancellations (P : Protocol T Msg State)
    (h : Agreement P) (x : Inputs) (D : DeliverySchedule T) (r : Fin T)
    (hl : LastDeliveryRound D r) :
    common_decision P x (eraseDelivery (eraseDelivery D 0 r) 1 r) = common_decision P x D := by
  exact (last_delivery_preserves_decision P h x _ 1 r (last_round_after_erase D r hl 0)).trans
    (last_delivery_preserves_decision P h x D 0 r hl)

/-- A request followed by an acknowledgement. This protocol is intentionally unsafe. -/
def ackProtocol : Protocol 2 Bool (Bool × Bool) where
  initial_state := fun _ x => (x == 1, false)
  send_msg := fun _ r st => if r.val = 0 then st.1 else st.1 && st.2
  step := fun p r st inbox =>
    if (p = 1 ∧ r.val = 0) ∨ (p = 0 ∧ r.val = 1) then (st.1, inbox == some true) else st
  decide := fun _ st => if st.1 && st.2 then 1 else 0

def ackSchedule : DeliverySchedule 2 := fun s t r =>
  decide ((s = 0 ∧ t = 1 ∧ r.val = 0) ∨ (s = 1 ∧ t = 0 ∧ r.val = 1))
def lostAckSchedule : DeliverySchedule 2 := eraseDelivery ackSchedule 1 1

theorem ack_reliable_success : ReliableSuccess ackProtocol := by
  intro p
  fin_cases p <;> decide

theorem ack_last_round : LastDeliveryRound ackSchedule 1 := by
  intro t ht
  have := t.isLt
  have hval : (1 : Fin 2).val = 1 := rfl
  omega

theorem ack_loss_sender_unchanged :
    execution ackProtocol (fun _ => 1) lostAckSchedule 2 1 =
      execution ackProtocol (fun _ => 1) ackSchedule 2 1 :=
  last_delivery_removal_indistinguishability ackProtocol (fun _ => 1) ackSchedule 1 1
    ack_last_round 2

theorem ack_loss_counterexample :
    decision ackProtocol (fun _ => 1) ackSchedule 0 = 1 ∧
    decision ackProtocol (fun _ => 1) ackSchedule 1 = 1 ∧
    decision ackProtocol (fun _ => 1) lostAckSchedule 0 = 0 ∧
    decision ackProtocol (fun _ => 1) lostAckSchedule 1 = 1 := by decide

theorem ack_protocol_not_agreement : ¬ Agreement ackProtocol := by
  intro h
  have he := h (fun _ => 1) lostAckSchedule
  have hz := ack_loss_counterexample.2.2.1
  have ho := ack_loss_counterexample.2.2.2
  rw [hz, ho] at he
  exact (by decide : (0 : Decision) ≠ 1) he

/-- Under the safety hypotheses, loss of the last ack permits no attack. -/
theorem two_round_ack_safe_retreat (P : Protocol 2 Msg State)
    (ha : Agreement P) (hv : ValidityZero P) (x : Inputs) (p : Process) :
    decision P x lostAckSchedule p = 0 := all_schedules_force_retreat P ha hv x _ p

structure DistributedCoordinatedAttackImpossibilitySuite : Prop where
  last_message : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State)
    x D s r, LastDeliveryRound D r → ∀ n,
      execution P x (eraseDelivery D s r) n s = execution P x D n s
  reduction : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State),
    Agreement P → ∀ x D, common_decision P x D = common_decision P x sched_empty
  input_changes : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State),
    Agreement P → ∀ x y, common_decision P x sched_empty = common_decision P y sched_empty
  no_attack : ∀ (T : ℕ) (Msg State : Type) (P : Protocol T Msg State),
    Agreement P → ValidityZero P → ∀ x D p, decision P x D p = 0
  impossible : ∀ T, ¬ ∃ (Msg State : Type) (P : Protocol T Msg State),
    Agreement P ∧ ValidityZero P ∧ ReliableSuccess P
  retreat_example : ∀ T, Agreement (retreatProtocol T) ∧ ValidityZero (retreatProtocol T) ∧
    ¬ ReliableSuccess (retreatProtocol T)
  zero_rounds : ∀ (Msg State : Type) (P : Protocol 0 Msg State),
    ¬ (Agreement P ∧ ValidityZero P ∧ ReliableSuccess P)
  erasures_commute : ∀ T (D : DeliverySchedule T) s t r u,
    eraseDelivery (eraseDelivery D s r) t u = eraseDelivery (eraseDelivery D t u) s r
  ack_counterexample : ¬ Agreement ackProtocol
  ack_sender : execution ackProtocol (fun _ => 1) lostAckSchedule 2 1 =
    execution ackProtocol (fun _ => 1) ackSchedule 2 1

theorem distributed_coordinated_attack_impossibility_master_suite :
    DistributedCoordinatedAttackImpossibilitySuite where
  last_message := fun _ _ _ => last_delivery_removal_indistinguishability
  reduction := fun _ _ _ => schedule_reduction_to_empty
  input_changes := fun _ _ _ => input_flip_indistinguishability
  no_attack := fun _ _ _ => all_schedules_force_retreat
  impossible := no_correct_protocol
  retreat_example := trivial_retreat_protocol_satisfies_partial
  zero_rounds := fun _ _ => zero_horizon_impossibility
  erasures_commute := fun _ => erase_deliveries_commute
  ack_counterexample := ack_protocol_not_agreement
  ack_sender := ack_loss_sender_unchanged

end DistributedCoordinatedAttackImpossibility
