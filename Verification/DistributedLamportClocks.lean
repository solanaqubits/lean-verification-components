import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace DistributedLamportClocks

/-- Increment the supplied natural-number counter. -/
def localTick (c : ℕ) : ℕ := c + 1

/-- Update from the supplied local and message timestamps. -/
def receiveMsg (localClock msgClock : ℕ) : ℕ := max localClock msgClock + 1

theorem local_tick_strictly_increases (c : ℕ) : c < localTick c := by
  dsimp [localTick]
  omega

theorem receive_msg_strictly_greater_than_local (localClock msgClock : ℕ) :
    localClock < receiveMsg localClock msgClock := by
  dsimp [receiveMsg]
  have := le_max_left localClock msgClock
  omega

theorem receive_msg_strictly_greater_than_msg (localClock msgClock : ℕ) :
    msgClock < receiveMsg localClock msgClock := by
  dsimp [receiveMsg]
  have := le_max_right localClock msgClock
  omega

/-- Elementary timestamp relationships; no event identities or execution trace is represented. -/
inductive HappensBeforeStep : ℕ → ℕ → Prop where
  | localEvent (c : ℕ) : HappensBeforeStep c (localTick c)
  | msgSendReceive (cL cM : ℕ) : HappensBeforeStep cM (receiveMsg cL cM)
  | localReceive (cL cM : ℕ) : HappensBeforeStep cL (receiveMsg cL cM)

theorem happens_before_step_preserves_clock_order (c1 c2 : ℕ)
    (h_step : HappensBeforeStep c1 c2) : c1 < c2 := by
  cases h_step with
  | localEvent => exact local_tick_strictly_increases _
  | msgSendReceive => exact receive_msg_strictly_greater_than_msg _ _
  | localReceive => exact receive_msg_strictly_greater_than_local _ _

/-- With only numeric endpoints, the relation admits every strictly increasing pair.
This is not a converse theorem about causal events in a distributed execution. -/
theorem happens_before_step_iff_lt (c1 c2 : ℕ) :
    HappensBeforeStep c1 c2 ↔ c1 < c2 := by
  constructor
  · exact happens_before_step_preserves_clock_order c1 c2
  · intro h
    cases c2 with
    | zero => omega
    | succ n =>
      have hmax : max n c1 = n := max_eq_left (by omega)
      simpa [receiveMsg, hmax] using HappensBeforeStep.msgSendReceive n c1

/-- Compatibility name for the local increment rule. -/
abbrev tick := localTick

/-- Compatibility name for the receive rule. -/
abbrev recvUpdate := receiveMsg

theorem tick_strictly_increases (c : ℕ) : c < tick c :=
  local_tick_strictly_increases c

theorem recv_strictly_increases_local (c_local c_msg : ℕ) :
    c_local < recvUpdate c_local c_msg :=
  receive_msg_strictly_greater_than_local c_local c_msg

theorem recv_strictly_increases_msg (c_local c_msg : ℕ) :
    c_msg < recvUpdate c_local c_msg :=
  receive_msg_strictly_greater_than_msg c_local c_msg

theorem send_recv_causality (c_send c_recv : ℕ) :
    tick c_send < recvUpdate c_recv (tick c_send) :=
  recv_strictly_increases_msg c_recv (tick c_send)

/-- Event metadata; uniqueness of timestamps within a process is not imposed by this record. -/
structure Event where
  id : ℕ
  pid : ℕ
  clock : ℕ
  deriving DecidableEq, Repr

/-- Transitive closure of supplied process and message edges, independent of clock values. -/
inductive HappensBefore (R_proc R_msg : Event → Event → Prop) : Event → Event → Prop where
  | proc {e1 e2 : Event} : R_proc e1 e2 → HappensBefore R_proc R_msg e1 e2
  | msg {e1 e2 : Event} : R_msg e1 e2 → HappensBefore R_proc R_msg e1 e2
  | trans {e1 e2 e3 : Event} :
      HappensBefore R_proc R_msg e1 e2 → HappensBefore R_proc R_msg e2 e3 →
      HappensBefore R_proc R_msg e1 e3

/-- Clock monotonicity of elementary edges implies monotonicity of their transitive closure. -/
theorem happens_before_clock_condition
    {R_proc R_msg : Event → Event → Prop}
    (h_proc : ∀ e1 e2, R_proc e1 e2 → e1.clock < e2.clock)
    (h_msg : ∀ e1 e2, R_msg e1 e2 → e1.clock < e2.clock)
    {e1 e2 : Event} (h_hb : HappensBefore R_proc R_msg e1 e2) :
    e1.clock < e2.clock := by
  induction h_hb with
  | proc hp => exact h_proc _ _ hp
  | msg hm => exact h_msg _ _ hm
  | trans _ _ ih1 ih2 => exact Nat.lt_trans ih1 ih2

theorem happens_before_irreflexive
    {R_proc R_msg : Event → Event → Prop}
    (h_proc : ∀ e1 e2, R_proc e1 e2 → e1.clock < e2.clock)
    (h_msg : ∀ e1 e2, R_msg e1 e2 → e1.clock < e2.clock) (e : Event) :
    ¬ HappensBefore R_proc R_msg e e := by
  intro h
  exact Nat.lt_irrefl e.clock (happens_before_clock_condition h_proc h_msg h)

theorem happens_before_asymmetric
    {R_proc R_msg : Event → Event → Prop}
    (h_proc : ∀ e1 e2, R_proc e1 e2 → e1.clock < e2.clock)
    (h_msg : ∀ e1 e2, R_msg e1 e2 → e1.clock < e2.clock)
    {e1 e2 : Event} (h12 : HappensBefore R_proc R_msg e1 e2)
    (h21 : HappensBefore R_proc R_msg e2 e1) : False :=
  happens_before_irreflexive h_proc h_msg e1 (HappensBefore.trans h12 h21)

/-- Lexicographic comparison of (clock, pid). Total on events only when these keys are unique. -/
def lamportTotalOrder (e1 e2 : Event) : Prop :=
  e1.clock < e2.clock ∨ (e1.clock = e2.clock ∧ e1.pid < e2.pid)

theorem lamport_total_order_irreflexive (e : Event) : ¬ lamportTotalOrder e e := by
  simp [lamportTotalOrder]

theorem lamport_total_order_transitive {e1 e2 e3 : Event}
    (h12 : lamportTotalOrder e1 e2) (h23 : lamportTotalOrder e2 e3) :
    lamportTotalOrder e1 e3 := by
  dsimp [lamportTotalOrder] at *
  omega

theorem lamport_total_order_extends_happens_before
    {R_proc R_msg : Event → Event → Prop}
    (h_proc : ∀ e1 e2, R_proc e1 e2 → e1.clock < e2.clock)
    (h_msg : ∀ e1 e2, R_msg e1 e2 → e1.clock < e2.clock)
    {e1 e2 : Event} (h_hb : HappensBefore R_proc R_msg e1 e2) :
    lamportTotalOrder e1 e2 :=
  Or.inl (happens_before_clock_condition h_proc h_msg h_hb)

/-- Distinct events are comparable if equality of their clock/PID keys implies event equality. -/
theorem lamport_total_order_trichotomy (e1 e2 : Event)
    (h_unique : e1.clock = e2.clock → e1.pid = e2.pid → e1 = e2) :
    lamportTotalOrder e1 e2 ∨ e1 = e2 ∨ lamportTotalOrder e2 e1 := by
  by_cases hc : e1.clock = e2.clock
  · by_cases hp : e1.pid = e2.pid
    · exact Or.inr (Or.inl (h_unique hc hp))
    · dsimp [lamportTotalOrder]
      omega
  · dsimp [lamportTotalOrder]
    omega

/-- Different IDs with the same clock/PID key are incomparable in the supplied relation. -/
theorem lamport_key_collision_example :
    (⟨0, 0, 0⟩ : Event) ≠ ⟨1, 0, 0⟩ ∧
    ¬ lamportTotalOrder ⟨0, 0, 0⟩ ⟨1, 0, 0⟩ ∧
    ¬ lamportTotalOrder ⟨1, 0, 0⟩ ⟨0, 0, 0⟩ := by
  simp [lamportTotalOrder, Event.mk.injEq]

/-- Increasing clocks alone do not force an edge in the event-level causal closure. -/
theorem empty_edges_no_happens_before (e1 e2 : Event) :
    ¬ HappensBefore (fun _ _ => False) (fun _ _ => False) e1 e2 := by
  intro h
  induction h with
  | proc hp => exact hp
  | msg hm => exact hm
  | trans _ _ ih1 _ => exact ih1

structure DistributedLamportFormalSuite : Prop where
  h_tick_mono : ∀ c, c < tick c
  h_recv_local : ∀ c_loc c_msg, c_loc < recvUpdate c_loc c_msg
  h_recv_msg : ∀ c_loc c_msg, c_msg < recvUpdate c_loc c_msg
  h_send_recv_caus : ∀ c_send c_recv, tick c_send < recvUpdate c_recv (tick c_send)
  h_clock_cond : ∀ {Rp Rm : Event → Event → Prop},
    (∀ a b, Rp a b → a.clock < b.clock) → (∀ a b, Rm a b → a.clock < b.clock) →
    ∀ {a b}, HappensBefore Rp Rm a b → a.clock < b.clock
  h_irrefl : ∀ {Rp Rm : Event → Event → Prop},
    (∀ a b, Rp a b → a.clock < b.clock) → (∀ a b, Rm a b → a.clock < b.clock) →
    ∀ e, ¬ HappensBefore Rp Rm e e
  h_asymm : ∀ {Rp Rm : Event → Event → Prop},
    (∀ a b, Rp a b → a.clock < b.clock) → (∀ a b, Rm a b → a.clock < b.clock) →
    ∀ {a b}, HappensBefore Rp Rm a b → HappensBefore Rp Rm b a → False
  h_total_irrefl : ∀ e, ¬ lamportTotalOrder e e
  h_total_trans : ∀ {a b c}, lamportTotalOrder a b → lamportTotalOrder b c → lamportTotalOrder a c
  h_total_extends : ∀ {Rp Rm : Event → Event → Prop},
    (∀ a b, Rp a b → a.clock < b.clock) → (∀ a b, Rm a b → a.clock < b.clock) →
    ∀ {a b}, HappensBefore Rp Rm a b → lamportTotalOrder a b
  h_trichotomy : ∀ a b, (a.clock = b.clock → a.pid = b.pid → a = b) →
    lamportTotalOrder a b ∨ a = b ∨ lamportTotalOrder b a

/-- Event-level results, conditional on monotone elementary edges and unique comparison keys. -/
theorem distributed_lamport_events_master_suite : DistributedLamportFormalSuite := {
  h_tick_mono := tick_strictly_increases
  h_recv_local := recv_strictly_increases_local
  h_recv_msg := recv_strictly_increases_msg
  h_send_recv_caus := send_recv_causality
  h_clock_cond := happens_before_clock_condition
  h_irrefl := happens_before_irreflexive
  h_asymm := happens_before_asymmetric
  h_total_irrefl := lamport_total_order_irreflexive
  h_total_trans := lamport_total_order_transitive
  h_total_extends := lamport_total_order_extends_happens_before
  h_trichotomy := lamport_total_order_trichotomy
}

structure DistributedLamportClocksFormalSuite : Prop where
  h_extended : DistributedLamportFormalSuite
  h_local_mono : ∀ (c : ℕ), c < localTick c
  h_recv_gt_local : ∀ (cL cM : ℕ), cL < receiveMsg cL cM
  h_recv_gt_msg : ∀ (cL cM : ℕ), cM < receiveMsg cL cM
  h_clock_cond : ∀ (c1 c2 : ℕ), HappensBeforeStep c1 c2 → c1 < c2

theorem distributed_lamport_clocks_master_suite : DistributedLamportClocksFormalSuite := {
  h_extended := distributed_lamport_events_master_suite
  h_local_mono := local_tick_strictly_increases
  h_recv_gt_local := receive_msg_strictly_greater_than_local
  h_recv_gt_msg := receive_msg_strictly_greater_than_msg
  h_clock_cond := happens_before_step_preserves_clock_order
}

end DistributedLamportClocks
