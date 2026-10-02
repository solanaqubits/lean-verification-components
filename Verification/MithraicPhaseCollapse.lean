/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Scalar interference visibility and a threshold specification

The nonnegative ordered extrema have positive sum, excluding a dark 0/0 pattern.
Zero visibility means equal extrema; it is not a theorem of quantum decoherence.
Threshold rejection is a logical specification, not an actuator or dump-port
power-routing law. No relation to an MZI phase or density matrix is assumed.
-/

namespace MithraicPhaseCollapse

noncomputable section

/-- Ordered scalar intensity extrema with a strictly positive total. -/
structure InterferencePattern where
  i_max : ℝ
  i_min : ℝ
  h_min_nonneg : 0 ≤ i_min
  h_ordered : i_min ≤ i_max
  h_pos : 0 < i_max + i_min

def visibility (p : InterferencePattern) : ℝ :=
  (p.i_max - p.i_min) / (p.i_max + p.i_min)

theorem max_intensity_pos (p : InterferencePattern) : 0 < p.i_max := by
  linarith [p.h_ordered, p.h_pos]

/-- Visibility lies in the closed unit interval under the pattern hypotheses. -/
theorem visibility_bounds (p : InterferencePattern) :
    0 ≤ visibility p ∧ visibility p ≤ 1 := by
  constructor
  · exact div_nonneg (sub_nonneg.mpr p.h_ordered) (le_of_lt p.h_pos)
  · apply (div_le_iff₀ p.h_pos).mpr
    linarith [p.h_min_nonneg]

/-- A zero minimum gives unit contrast because the maximum is positive. -/
theorem visibility_ideal (p : InterferencePattern) (h_min : p.i_min = 0) :
    visibility p = 1 := by
  dsimp [visibility]
  rw [h_min, sub_zero, add_zero, div_self (ne_of_gt (max_intensity_pos p))]

theorem visibility_ideal_iff (p : InterferencePattern) :
    visibility p = 1 ↔ p.i_min = 0 := by
  constructor
  · intro h
    have hle : 1 ≤ visibility p := le_of_eq h.symm
    have hnum := (le_div_iff₀ p.h_pos).mp hle
    linarith [p.h_min_nonneg]
  · exact visibility_ideal p

/-- Equal extrema give zero scalar contrast, without identifying a physical cause. -/
theorem visibility_collapse (p : InterferencePattern) (h_equal : p.i_max = p.i_min) :
    visibility p = 0 := by
  dsimp [visibility]
  rw [h_equal, sub_self, zero_div]

theorem visibility_collapse_iff (p : InterferencePattern) :
    visibility p = 0 ↔ p.i_max = p.i_min := by
  constructor
  · intro h
    have hnum := (div_eq_zero_iff.mp h).resolve_right (ne_of_gt p.h_pos)
    exact sub_eq_zero.mp hnum
  · exact visibility_collapse p

/-- Strict degradation when the minimum rises and the maximum stays fixed. -/
theorem visibility_strict_decay (p q : InterferencePattern)
    (h_max : p.i_max = q.i_max) (h_min : p.i_min < q.i_min) :
    visibility q < visibility p := by
  apply (div_lt_div_iff₀ q.h_pos p.h_pos).mpr
  have hprod : 0 < p.i_max * (q.i_min - p.i_min) :=
    mul_pos (max_intensity_pos p) (sub_pos.mpr h_min)
  rw [← h_max]
  have hcross :
      (p.i_max - p.i_min) * (p.i_max + q.i_min) -
        (p.i_max - q.i_min) * (p.i_max + p.i_min) =
      2 * (p.i_max * (q.i_min - p.i_min)) := by ring
  linarith

/-- Nonstrict degradation includes the case of unchanged minima. -/
theorem visibility_antitone (p q : InterferencePattern)
    (h_max : p.i_max = q.i_max) (h_min : p.i_min ≤ q.i_min) :
    visibility q ≤ visibility p := by
  rcases lt_or_eq_of_le h_min with hlt | heq
  · exact le_of_lt (visibility_strict_decay p q h_max hlt)
  · dsimp [visibility]
    rw [h_max, heq]

/-- Threshold specification only: no physical control action is defined. -/
def is_coherence_valid (p : InterferencePattern) (v_crit : ℝ) : Prop :=
  v_crit ≤ visibility p

/-- Lowering the minimum preserves an already satisfied threshold at fixed maximum. -/
theorem coherence_valid_of_lower_min (p q : InterferencePattern) (v_crit : ℝ)
    (h_max : p.i_max = q.i_max) (h_min : q.i_min ≤ p.i_min)
    (h_valid : is_coherence_valid p v_crit) : is_coherence_valid q v_crit := by
  exact le_trans h_valid (visibility_antitone q p h_max.symm h_min)

theorem below_threshold_invalid (p : InterferencePattern) (v_crit : ℝ)
    (h_below : visibility p < v_crit) : ¬ is_coherence_valid p v_crit := by
  exact not_le.mpr h_below

theorem invalid_iff_below_threshold (p : InterferencePattern) (v_crit : ℝ) :
    ¬ is_coherence_valid p v_crit ↔ visibility p < v_crit := by
  exact not_le

/-- At the threshold equality is accepted, as specified by the nonstrict predicate. -/
theorem threshold_equality_valid (p : InterferencePattern) :
    is_coherence_valid p (visibility p) := le_rfl

theorem collapsed_invalid_if_pos (p : InterferencePattern) (v_crit : ℝ)
    (h_equal : p.i_max = p.i_min) (h_crit : 0 < v_crit) :
    ¬ is_coherence_valid p v_crit := by
  apply below_threshold_invalid
  rw [visibility_collapse p h_equal]
  exact h_crit

/-- Thresholds outside [0,1] are allowed parameters, with explicit degenerate behavior. -/
theorem nonpositive_threshold_valid (p : InterferencePattern) (v_crit : ℝ)
    (h_crit : v_crit ≤ 0) : is_coherence_valid p v_crit := by
  exact le_trans h_crit (visibility_bounds p).1

theorem above_one_threshold_invalid (p : InterferencePattern) (v_crit : ℝ)
    (h_crit : 1 < v_crit) : ¬ is_coherence_valid p v_crit := by
  exact below_threshold_invalid p v_crit (lt_of_le_of_lt (visibility_bounds p).2 h_crit)

structure MithraicPhaseCollapseFormalSuite : Prop where
  h_bounds : ∀ p : InterferencePattern, 0 ≤ visibility p ∧ visibility p ≤ 1
  h_ideal : ∀ p : InterferencePattern, p.i_min = 0 → visibility p = 1
  h_ideal_iff : ∀ p : InterferencePattern, visibility p = 1 ↔ p.i_min = 0
  h_collapse : ∀ p : InterferencePattern, p.i_max = p.i_min → visibility p = 0
  h_collapse_iff : ∀ p : InterferencePattern, visibility p = 0 ↔ p.i_max = p.i_min
  h_decay : ∀ p q : InterferencePattern, p.i_max = q.i_max → p.i_min < q.i_min →
    visibility q < visibility p
  h_antitone : ∀ p q : InterferencePattern, p.i_max = q.i_max → p.i_min ≤ q.i_min →
    visibility q ≤ visibility p
  h_valid_lower_min : ∀ (p q : InterferencePattern) (v_crit : ℝ),
    p.i_max = q.i_max → q.i_min ≤ p.i_min →
    is_coherence_valid p v_crit → is_coherence_valid q v_crit
  h_rejection : ∀ (p : InterferencePattern) (v_crit : ℝ),
    ¬ is_coherence_valid p v_crit ↔ visibility p < v_crit
  h_collapsed_rejection : ∀ (p : InterferencePattern) (v_crit : ℝ),
    p.i_max = p.i_min → 0 < v_crit → ¬ is_coherence_valid p v_crit

theorem mithraic_phase_collapse_master_suite : MithraicPhaseCollapseFormalSuite := {
  h_bounds := visibility_bounds
  h_ideal := visibility_ideal
  h_ideal_iff := visibility_ideal_iff
  h_collapse := visibility_collapse
  h_collapse_iff := visibility_collapse_iff
  h_decay := visibility_strict_decay
  h_antitone := visibility_antitone
  h_valid_lower_min := coherence_valid_of_lower_min
  h_rejection := invalid_iff_below_threshold
  h_collapsed_rejection := collapsed_invalid_if_pos
}

end

end MithraicPhaseCollapse
