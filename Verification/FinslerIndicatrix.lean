import Verification.FinslerPolyMetric
import Verification.FinslerMultilinear

set_option linter.style.header false

noncomputable section

namespace FinslerIndicatrix

open FinslerPolyMetric FinslerMultilinear

/-- The positive level set of the coordinate product. -/
def IndicatrixBM (x : Point4) : Prop :=
  InPositiveCone x ∧ berwaldMoorForm x = 1

def midpoint (a b : Point4) : Point4 :=
  ⟨(a.x1 + b.x1) / 2, (a.x2 + b.x2) / 2, (a.x3 + b.x3) / 2, (a.x4 + b.x4) / 2⟩

theorem midpoint_in_positive_cone (a b : Point4)
    (ha : InPositiveCone a) (hb : InPositiveCone b) :
    InPositiveCone (midpoint a b) := by
  rcases ha with ⟨ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb1, hb2, hb3, hb4⟩
  dsimp [midpoint, InPositiveCone]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A prescribed diagonal quadratic form; no Hessian identification is asserted. -/
def metricEnergy (x v : Point4) : ℝ :=
  v.x1 ^ 2 / x.x1 ^ 2 + v.x2 ^ 2 / x.x2 ^ 2 +
  v.x3 ^ 2 / x.x3 ^ 2 + v.x4 ^ 2 / x.x4 ^ 2

theorem metric_energy_nonneg (x v : Point4) : 0 ≤ metricEnergy x v := by
  unfold metricEnergy
  positivity

theorem metric_energy_pos (x v : Point4) (hx : InPositiveCone x) (hv : v ≠ 0) :
    0 < metricEnergy x v := by
  have hn := metric_energy_nonneg x v
  by_contra hp
  have he : metricEnergy x v = 0 := le_antisymm (le_of_not_gt hp) hn
  have h1 : 0 ≤ v.x1 ^ 2 / x.x1 ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h2 : 0 ≤ v.x2 ^ 2 / x.x2 ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h3 : 0 ≤ v.x3 ^ 2 / x.x3 ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  have h4 : 0 ≤ v.x4 ^ 2 / x.x4 ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  unfold metricEnergy at he
  have z1 : v.x1 = 0 := by
    have hd : v.x1 ^ 2 / x.x1 ^ 2 = 0 := by linarith
    have hxne : x.x1 ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx.1)
    have hvz : v.x1 ^ 2 = 0 := (div_eq_zero_iff).mp hd |>.resolve_right hxne
    exact (sq_eq_zero_iff).mp hvz
  have z2 : v.x2 = 0 := by
    have hd : v.x2 ^ 2 / x.x2 ^ 2 = 0 := by linarith
    have hxne : x.x2 ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx.2.1)
    have hvz : v.x2 ^ 2 = 0 := (div_eq_zero_iff).mp hd |>.resolve_right hxne
    exact (sq_eq_zero_iff).mp hvz
  have z3 : v.x3 = 0 := by
    have hd : v.x3 ^ 2 / x.x3 ^ 2 = 0 := by linarith
    have hxne : x.x3 ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx.2.2.1)
    have hvz : v.x3 ^ 2 = 0 := (div_eq_zero_iff).mp hd |>.resolve_right hxne
    exact (sq_eq_zero_iff).mp hvz
  have z4 : v.x4 = 0 := by
    have hd : v.x4 ^ 2 / x.x4 ^ 2 = 0 := by linarith
    have hxne : x.x4 ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos hx.2.2.2)
    have hvz : v.x4 ^ 2 = 0 := (div_eq_zero_iff).mp hd |>.resolve_right hxne
    exact (sq_eq_zero_iff).mp hvz
  apply hv
  cases v
  change Point4.mk _ _ _ _ = Point4.mk 0 0 0 0
  dsimp at z1 z2 z3 z4
  rw [z1, z2, z3, z4]

lemma sq_midpoint_ge_mul (a b : ℝ) : a * b ≤ ((a + b) / 2) ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- Multiplying the four coordinate AM-GM inequalities. -/
theorem berwaldMoor_midpoint_sq_ge (a b : Point4)
    (ha : InPositiveCone a) (hb : InPositiveCone b) :
    berwaldMoorForm a * berwaldMoorForm b ≤ (berwaldMoorForm (midpoint a b)) ^ 2 := by
  have h12 := mul_le_mul (sq_midpoint_ge_mul a.x1 b.x1)
    (sq_midpoint_ge_mul a.x2 b.x2) (le_of_lt (mul_pos ha.2.1 hb.2.1)) (sq_nonneg _)
  have h34 := mul_le_mul (sq_midpoint_ge_mul a.x3 b.x3)
    (sq_midpoint_ge_mul a.x4 b.x4)
    (le_of_lt (mul_pos ha.2.2.2 hb.2.2.2)) (sq_nonneg _)
  have h := mul_le_mul h12 h34
    (le_of_lt (mul_pos (mul_pos ha.2.2.1 hb.2.2.1) (mul_pos ha.2.2.2 hb.2.2.2)))
    (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  dsimp [berwaldMoorForm, midpoint]
  convert h using 1 <;> first | rfl | ring

/-- Midpoints of level-one points have product at least one.
This does not say that the level set itself is convex. -/
theorem indicatrix_midpoint_ge_one (a b : Point4)
    (ha : IndicatrixBM a) (hb : IndicatrixBM b) :
    1 ≤ berwaldMoorForm (midpoint a b) := by
  have hs := berwaldMoor_midpoint_sq_ge a b ha.1 hb.1
  rw [ha.2, hb.2] at hs
  have hp := berwald_moor_pos_in_positive_cone _ (midpoint_in_positive_cone a b ha.1 hb.1)
  nlinarith

def PositiveBoost (b : HyperbolicBoost) : Prop :=
  0 < b.lam1 ∧ 0 < b.lam2 ∧ 0 < b.lam3 ∧ 0 < b.lam4

theorem boost_preserves_positive_cone (b : HyperbolicBoost) (hb : PositiveBoost b)
    (x : Point4) (hx : InPositiveCone x) :
    InPositiveCone (applyBoost b x) :=
  ⟨mul_pos hb.1 hx.1, mul_pos hb.2.1 hx.2.1,
   mul_pos hb.2.2.1 hx.2.2.1, mul_pos hb.2.2.2 hx.2.2.2⟩

theorem boost_preserves_indicatrix (b : HyperbolicBoost) (hb : PositiveBoost b)
    (x : Point4) (hx : IndicatrixBM x) :
    IndicatrixBM (applyBoost b x) := by
  refine ⟨boost_preserves_positive_cone b hb x hx.1, ?_⟩
  rw [berwald_moor_boost_invariance, hx.2]

structure FinslerIndicatrixFormalSuite : Prop where
  h_metric_pos : ∀ x v : Point4, InPositiveCone x → v ≠ 0 → 0 < metricEnergy x v
  h_mid_sq_ge : ∀ a b : Point4, InPositiveCone a → InPositiveCone b →
    berwaldMoorForm a * berwaldMoorForm b ≤ (berwaldMoorForm (midpoint a b)) ^ 2
  h_indic_conv : ∀ a b : Point4, IndicatrixBM a → IndicatrixBM b →
    1 ≤ berwaldMoorForm (midpoint a b)
  h_boost_indic : ∀ (b : HyperbolicBoost), PositiveBoost b → ∀ x : Point4,
    IndicatrixBM x → IndicatrixBM (applyBoost b x)

theorem finsler_indicatrix_master_verification_suite : FinslerIndicatrixFormalSuite := {
  h_metric_pos := metric_energy_pos
  h_mid_sq_ge := berwaldMoor_midpoint_sq_ge
  h_indic_conv := indicatrix_midpoint_ge_one
  h_boost_indic := boost_preserves_indicatrix
}

#print axioms finsler_indicatrix_master_verification_suite

end FinslerIndicatrix
