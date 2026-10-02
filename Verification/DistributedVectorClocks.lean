import Mathlib.Data.Nat.Basic

set_option linter.style.header false

namespace DistributedVectorClocks

/-- A pair of logical counters; no event history is attached. -/
@[ext] structure VClock2 where
  c1 : ℕ
  c2 : ℕ
  deriving DecidableEq, Repr

def le (v1 v2 : VClock2) : Prop := v1.c1 ≤ v2.c1 ∧ v1.c2 ≤ v2.c2
/-- Strict vector order; correspondence to event causality requires a separate model. -/
def lt (v1 v2 : VClock2) : Prop := le v1 v2 ∧ v1 ≠ v2
def concurrent (v1 v2 : VClock2) : Prop := ¬ le v1 v2 ∧ ¬ le v2 v1

theorem le_refl (v : VClock2) : le v v := ⟨Nat.le_refl _, Nat.le_refl _⟩

theorem le_trans (v1 v2 v3 : VClock2) (h12 : le v1 v2) (h23 : le v2 v3) : le v1 v3 :=
  ⟨Nat.le_trans h12.1 h23.1, Nat.le_trans h12.2 h23.2⟩

theorem le_antisymm (v1 v2 : VClock2) (h12 : le v1 v2) (h21 : le v2 v1) : v1 = v2 := by
  exact VClock2.ext (Nat.le_antisymm h12.1 h21.1) (Nat.le_antisymm h12.2 h21.2)

theorem lt_trans (v1 v2 v3 : VClock2) (h12 : lt v1 v2) (h23 : lt v2 v3) : lt v1 v3 := by
  refine ⟨le_trans v1 v2 v3 h12.1 h23.1, ?_⟩
  intro heq
  have h31 : le v3 v2 := heq ▸ h12.1
  exact h23.2 (le_antisymm v2 v3 h23.1 h31)

def tick1 (v : VClock2) : VClock2 := ⟨v.c1 + 1, v.c2⟩
def tick2 (v : VClock2) : VClock2 := ⟨v.c1, v.c2 + 1⟩
def merge (v1 v2 : VClock2) : VClock2 := ⟨max v1.c1 v2.c1, max v1.c2 v2.c2⟩

theorem tick1_strictly_increases (v : VClock2) : lt v (tick1 v) := by
  refine ⟨⟨Nat.le_succ _, Nat.le_refl _⟩, ?_⟩
  intro h
  have hc := congrArg VClock2.c1 h
  dsimp [tick1] at hc
  omega

theorem tick2_strictly_increases (v : VClock2) : lt v (tick2 v) := by
  refine ⟨⟨Nat.le_refl _, Nat.le_succ _⟩, ?_⟩
  intro h
  have hc := congrArg VClock2.c2 h
  dsimp [tick2] at hc
  omega

theorem merge_ge_left (v1 v2 : VClock2) : le v1 (merge v1 v2) :=
  ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem merge_ge_right (v1 v2 : VClock2) : le v2 (merge v1 v2) :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

/-- Minimality completes the least-upper-bound characterization of merge. -/
theorem merge_le (v1 v2 upper : VClock2) (h1 : le v1 upper) (h2 : le v2 upper) :
    le (merge v1 v2) upper :=
  ⟨max_le h1.1 h2.1, max_le h1.2 h2.2⟩

theorem merge_comm (v1 v2 : VClock2) : merge v1 v2 = merge v2 v1 := by
  exact VClock2.ext (Nat.max_comm _ _) (Nat.max_comm _ _)

theorem concurrent_symm (v1 v2 : VClock2) : concurrent v1 v2 ↔ concurrent v2 v1 :=
  ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

theorem concurrent_irreflexive (v : VClock2) : ¬ concurrent v v :=
  fun h => h.1 (le_refl v)

theorem concurrent_witness_exists : ∃ v1 v2 : VClock2, concurrent v1 v2 := by
  refine ⟨⟨1, 0⟩, ⟨0, 1⟩, ?_⟩
  dsimp [concurrent, le]
  omega

/-- Compatibility name for the existing two-counter type. -/
abbrev VectorClock2 := VClock2

def receive1 (u w : VectorClock2) : VectorClock2 := tick1 (merge u w)
def receive2 (u w : VectorClock2) : VectorClock2 := tick2 (merge u w)

theorem vector_le_refl (u : VectorClock2) : le u u := le_refl u

theorem vector_le_trans (u v w : VectorClock2) (huv : le u v) (hvw : le v w) : le u w :=
  le_trans u v w huv hvw

theorem vector_le_antisymm (u v : VectorClock2) (huv : le u v) (hvu : le v u) : u = v :=
  le_antisymm u v huv hvu

theorem receive1_strictly_greater_than_local (u w : VectorClock2) : lt u (receive1 u w) := by
  refine ⟨le_trans _ _ _ (merge_ge_left u w) (tick1_strictly_increases _).1, ?_⟩
  intro h
  have hc := congrArg VClock2.c1 h
  dsimp [receive1, tick1, merge] at hc
  omega

theorem receive1_dominates_message (u w : VectorClock2) : le w (receive1 u w) :=
  le_trans _ _ _ (merge_ge_right u w) (tick1_strictly_increases _).1

/-- The analogous local monotonicity guarantee for the second receiving node. -/
theorem receive2_strictly_greater_than_local (u w : VectorClock2) : lt u (receive2 u w) := by
  refine ⟨le_trans _ _ _ (merge_ge_left u w) (tick2_strictly_increases _).1, ?_⟩
  intro h
  have hc := congrArg VClock2.c2 h
  dsimp [receive2, tick2, merge] at hc
  omega

theorem receive2_dominates_message (u w : VectorClock2) : le w (receive2 u w) :=
  le_trans _ _ _ (merge_ge_right u w) (tick2_strictly_increases _).1

/-- Incomparability of two vectors, without an event-history interpretation. -/
theorem concurrent_independent_events_exist :
    concurrent (tick1 ⟨0, 0⟩) (tick2 ⟨0, 0⟩) := by
  dsimp [concurrent, le, tick1, tick2]
  omega

structure DistributedVectorClocksFormalSuite : Prop where
  h_le_refl : ∀ v, le v v
  h_le_trans : ∀ v1 v2 v3, le v1 v2 → le v2 v3 → le v1 v3
  h_le_antisymm : ∀ v1 v2, le v1 v2 → le v2 v1 → v1 = v2
  h_lt_trans : ∀ v1 v2 v3, lt v1 v2 → lt v2 v3 → lt v1 v3
  h_tick1_lt : ∀ v, lt v (tick1 v)
  h_tick2_lt : ∀ v, lt v (tick2 v)
  h_merge_left : ∀ v1 v2, le v1 (merge v1 v2)
  h_merge_right : ∀ v1 v2, le v2 (merge v1 v2)
  h_merge_le : ∀ v1 v2 upper, le v1 upper → le v2 upper → le (merge v1 v2) upper
  h_merge_comm : ∀ v1 v2, merge v1 v2 = merge v2 v1
  h_conc_symm : ∀ v1 v2, concurrent v1 v2 ↔ concurrent v2 v1
  h_conc_irref : ∀ v, ¬ concurrent v v
  h_conc_exists : ∃ v1 v2, concurrent v1 v2
  h_recv1_lt : ∀ u w, lt u (receive1 u w)
  h_recv1_dom : ∀ u w, le w (receive1 u w)
  h_recv2_lt : ∀ u w, lt u (receive2 u w)
  h_recv2_dom : ∀ u w, le w (receive2 u w)
  h_concurrency : concurrent (tick1 ⟨0, 0⟩) (tick2 ⟨0, 0⟩)

theorem distributed_vector_clocks_master_verification_suite :
    DistributedVectorClocksFormalSuite := {
  h_le_refl := le_refl
  h_le_trans := le_trans
  h_le_antisymm := le_antisymm
  h_lt_trans := lt_trans
  h_tick1_lt := tick1_strictly_increases
  h_tick2_lt := tick2_strictly_increases
  h_merge_left := merge_ge_left
  h_merge_right := merge_ge_right
  h_merge_le := merge_le
  h_merge_comm := merge_comm
  h_conc_symm := concurrent_symm
  h_conc_irref := concurrent_irreflexive
  h_conc_exists := concurrent_witness_exists
  h_recv1_lt := receive1_strictly_greater_than_local
  h_recv1_dom := receive1_dominates_message
  h_recv2_lt := receive2_strictly_greater_than_local
  h_recv2_dom := receive2_dominates_message
  h_concurrency := concurrent_independent_events_exist
}

theorem distributed_vector_clocks_master_suite : DistributedVectorClocksFormalSuite :=
  distributed_vector_clocks_master_verification_suite

#print axioms distributed_vector_clocks_master_verification_suite

end DistributedVectorClocks
