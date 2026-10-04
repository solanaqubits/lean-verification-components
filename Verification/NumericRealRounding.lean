/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.NumericRoundingCertificates
import Mathlib.Data.Real.Basic

/-!
# Real semantic extension of rational rounding certificates

The same finite rational grid and tagged representations are used for real inputs.
Counting crossed boundaries is a noncomputable semantic specification, not an
algorithm for comparing arbitrary real numbers. Rational certificate checking
remains executable and can establish the rounding of a real enclosed value.
-/

namespace NumericRealRounding

open NumericRoundingCertificates

noncomputable section

/-- Compare a real argument with an exact rational grid boundary. -/
def realCrossed (g : MagnitudeGrid) (x : ℝ) (j : ℕ) : Prop :=
  (boundary g j : ℝ) < x ∨ (boundary g j : ℝ) = x ∧ j % 2 = 1

/-- Finite count specification for real magnitudes; arbitrary real comparisons are classical. -/
def realMagnitudeCode (g : MagnitudeGrid) (x : ℝ) : ℕ := by
  classical
  exact ((Finset.range g.last).filter (realCrossed g x)).card

theorem realMagnitudeCode_le (g : MagnitudeGrid) (x : ℝ) :
    realMagnitudeCode g x ≤ g.last := by
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

theorem realMagnitudeCode_monotone (g : MagnitudeGrid) : Monotone (realMagnitudeCode g) := by
  classical
  intro x y hxy
  apply Finset.card_le_card
  intro j hj
  obtain ⟨hj, hc⟩ := Finset.mem_filter.mp hj
  refine Finset.mem_filter.mpr ⟨hj, ?_⟩
  rcases hc with h | ⟨h, hp⟩
  · exact Or.inl (lt_of_lt_of_le h hxy)
  · rcases lt_or_eq_of_le hxy with hxy | hxy
    · exact Or.inl (h.trans_lt hxy)
    · exact Or.inr ⟨h.trans hxy, hp⟩

/-- Real nearest-even semantics, retaining signed underflow and canonical positive exact zero. -/
def realRound (g : MagnitudeGrid) (x : ℝ) : FloatRepresentation g := by
  classical
  exact ⟨decide (x < 0), ⟨realMagnitudeCode g |x|,
    Nat.lt_succ_of_le (realMagnitudeCode_le g |x|)⟩⟩

theorem realCrossed_ratCast (g : MagnitudeGrid) (x : ℚ) (j : ℕ) :
    realCrossed g (x : ℝ) j ↔ crossed g x j := by
  simp only [realCrossed, crossed, Rat.cast_lt, Rat.cast_inj]

theorem realMagnitudeCode_ratCast (g : MagnitudeGrid) (x : ℚ) :
    realMagnitudeCode g (x : ℝ) = magnitudeCode g x := by
  classical
  simp only [realMagnitudeCode, magnitudeCode, realCrossed_ratCast]

/-- Rational-input agreement includes the sign bit, zero tags and virtual-overflow code. -/
theorem realRound_ratCast (g : MagnitudeGrid) (x : ℚ) :
    realRound g (x : ℝ) = roundNearestEven g x := by
  classical
  unfold realRound roundNearestEven
  have hsign : decide ((x : ℝ) < 0) = decide (x < 0) := by
    simp only [Rat.cast_lt_zero]
  rw [hsign]
  congr 1
  apply Fin.ext
  change realMagnitudeCode g |(x : ℝ)| = magnitudeCode g |x|
  rw [← Rat.cast_abs, realMagnitudeCode_ratCast]

/-- Real rounding fibers are convex, including signed zeros and overflow encodings. -/
theorem real_interval_rounding_soundness (g : MagnitudeGrid) (L U x : ℝ)
    (f : FloatRepresentation g) (hL : L ≤ x) (hU : x ≤ U)
    (hfL : realRound g L = f) (hfU : realRound g U = f) : realRound g x = f := by
  classical
  have he := hfL.trans hfU.symm
  have hs : decide (L < 0) = decide (U < 0) := congrArg FloatRepresentation.negative he
  have hm : realMagnitudeCode g |L| = realMagnitudeCode g |U| :=
    congrArg (fun f => f.magnitude.val) he
  have hc : realMagnitudeCode g |x| = realMagnitudeCode g |L| := by
    by_cases hLn : L < 0
    · have hUn : U < 0 := of_decide_eq_true (by simpa [hLn] using hs.symm)
      have hxn : x < 0 := lt_of_le_of_lt hU hUn
      rw [abs_of_neg hLn, abs_of_neg hUn] at hm
      rw [abs_of_neg hxn, abs_of_neg hLn]
      apply le_antisymm
      · exact realMagnitudeCode_monotone g (neg_le_neg hL)
      · rw [hm]
        exact realMagnitudeCode_monotone g (neg_le_neg hU)
    · have hLp : 0 ≤ L := le_of_not_gt hLn
      have hxp : 0 ≤ x := hLp.trans hL
      have hUp : 0 ≤ U := hxp.trans hU
      rw [abs_of_nonneg hLp, abs_of_nonneg hUp] at hm
      rw [abs_of_nonneg hxp, abs_of_nonneg hLp]
      apply le_antisymm
      · rw [hm]
        exact realMagnitudeCode_monotone g hU
      · exact realMagnitudeCode_monotone g hL
  have hsign : decide (x < 0) = decide (L < 0) := by
    by_cases hLn : L < 0
    · have hUn : U < 0 := of_decide_eq_true (by simpa [hLn] using hs.symm)
      simp [hLn, lt_of_le_of_lt hU hUn]
    · simp [hLn, not_lt.mpr ((le_of_not_gt hLn).trans hL)]
  have hxL : realRound g x = realRound g L := by
    unfold realRound
    rw [hsign]
    congr 1
    exact Fin.ext hc
  exact hxL.trans hfL

/-- Rational endpoint results determine the rounded encoding of a real enclosed argument. -/
theorem rational_bounds_real_rounding_soundness (g : MagnitudeGrid) (L U : ℚ) (x : ℝ)
    (f : FloatRepresentation g) (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ))
    (hfL : roundNearestEven g L = f) (hfU : roundNearestEven g U = f) :
    realRound g x = f := by
  apply real_interval_rounding_soundness g (L : ℝ) (U : ℝ) x f hL hU
  · exact (realRound_ratCast g L).trans hfL
  · exact (realRound_ratCast g U).trans hfU

/-- Main bridge: an executable rational interval certificate certifies an enclosed real value. -/
theorem interval_certificate_real_sound (g : MagnitudeGrid) (L U : ℚ) (x : ℝ)
    (f : FloatRepresentation g) (h : checkIntervalCertificate g L U f = .decided f)
    (hL : (L : ℝ) ≤ x) (hU : x ≤ (U : ℝ)) : realRound g x = f := by
  obtain ⟨_, hfL, hfU⟩ := (interval_certificate_decided_iff g L U f).mp h
  exact rational_bounds_real_rounding_soundness g L U x f hL hU hfL hfU

end

end NumericRealRounding
