import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

noncomputable section

namespace FinslerPolyMetric

/-- Four real coordinates with componentwise operations. -/
structure Point4 where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ

namespace Point4

def zero : Point4 := ⟨0, 0, 0, 0⟩
def add (a b : Point4) : Point4 :=
  ⟨a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4⟩
def smul (c : ℝ) (a : Point4) : Point4 :=
  ⟨c * a.x1, c * a.x2, c * a.x3, c * a.x4⟩
def hmul (a b : Point4) : Point4 :=
  ⟨a.x1 * b.x1, a.x2 * b.x2, a.x3 * b.x3, a.x4 * b.x4⟩

instance : Zero Point4 := ⟨zero⟩
instance : Add Point4 := ⟨add⟩
instance : SMul ℝ Point4 := ⟨smul⟩
instance : Mul Point4 := ⟨hmul⟩

@[simp] theorem zero_x1 : (0 : Point4).x1 = 0 := rfl

@[simp] theorem zero_x2 : (0 : Point4).x2 = 0 := rfl

@[simp] theorem zero_x3 : (0 : Point4).x3 = 0 := rfl

@[simp] theorem zero_x4 : (0 : Point4).x4 = 0 := rfl

@[simp] theorem smul_x1 (c : ℝ) (a : Point4) : (c • a).x1 = c * a.x1 := rfl

@[simp] theorem smul_x2 (c : ℝ) (a : Point4) : (c • a).x2 = c * a.x2 := rfl

@[simp] theorem smul_x3 (c : ℝ) (a : Point4) : (c • a).x3 = c * a.x3 := rfl

@[simp] theorem smul_x4 (c : ℝ) (a : Point4) : (c • a).x4 = c * a.x4 := rfl

@[simp] theorem mul_x1 (a b : Point4) : (a * b).x1 = a.x1 * b.x1 := rfl

@[simp] theorem mul_x2 (a b : Point4) : (a * b).x2 = a.x2 * b.x2 := rfl

@[simp] theorem mul_x3 (a b : Point4) : (a * b).x3 = a.x3 * b.x3 := rfl

@[simp] theorem mul_x4 (a b : Point4) : (a * b).x4 = a.x4 * b.x4 := rfl

end Point4

/-- The diagonal quartic polynomial; no four-argument multilinear form is defined here. -/
def berwaldMoorForm (x : Point4) : ℝ :=
  x.x1 * x.x2 * x.x3 * x.x4

/-- The coordinate product is homogeneous of degree four. -/
theorem berwald_moor_homogeneity_four (c : ℝ) (x : Point4) :
    berwaldMoorForm (c • x) = (c ^ 4) * berwaldMoorForm x := by
  simp only [berwaldMoorForm, Point4.smul_x1, Point4.smul_x2,
    Point4.smul_x3, Point4.smul_x4]
  ring

/-- Multiplicativity for componentwise multiplication. -/
theorem berwald_moor_multiplicative (a b : Point4) :
    berwaldMoorForm (a * b) = berwaldMoorForm a * berwaldMoorForm b := by
  simp only [berwaldMoorForm, Point4.mul_x1, Point4.mul_x2,
    Point4.mul_x3, Point4.mul_x4]
  ring

/-- The union of the four coordinate hyperplanes, including the origin. -/
def IsIsotropic (x : Point4) : Prop :=
  x.x1 = 0 ∨ x.x2 = 0 ∨ x.x3 = 0 ∨ x.x4 = 0

/-- The zero set of the quartic is exactly the isotropic locus. -/
theorem berwald_moor_zero_iff_isotropic (x : Point4) :
    berwaldMoorForm x = 0 ↔ IsIsotropic x := by
  simp [berwaldMoorForm, IsIsotropic, mul_eq_zero, or_assoc]

/-- A nonzero coordinate vector has zero quartic value. -/
theorem berwald_moor_not_positive_definite_on_entire_space :
    ∃ x : Point4, x ≠ 0 ∧ berwaldMoorForm x = 0 := by
  refine ⟨⟨1, 0, 0, 0⟩, ?_, ?_⟩
  · intro h
    have hx := congrArg Point4.x1 h
    norm_num at hx
  · norm_num [berwaldMoorForm]

/-- The strictly positive coordinate cone. -/
def InPositiveCone (x : Point4) : Prop :=
  0 < x.x1 ∧ 0 < x.x2 ∧ 0 < x.x3 ∧ 0 < x.x4

/-- The quartic is strictly positive on the positive cone. -/
theorem berwald_moor_pos_in_positive_cone (x : Point4) (hx : InPositiveCone x) :
    0 < berwaldMoorForm x := by
  rcases hx with ⟨h1, h2, h3, h4⟩
  exact mul_pos (mul_pos (mul_pos h1 h2) h3) h4

/-- Every vector in the positive cone is nonzero. -/
theorem positive_cone_vector_ne_zero (x : Point4) (hx : InPositiveCone x) :
    x ≠ 0 := by
  intro h
  have hp := hx.1
  simp [h] at hp

/-- Diagonal scaling parameters with product one; signs are unrestricted.
No group structure or preservation of the positive cone is asserted here. -/
structure HyperbolicBoost where
  lam1 : ℝ
  lam2 : ℝ
  lam3 : ℝ
  lam4 : ℝ
  h_det : lam1 * lam2 * lam3 * lam4 = 1

/-- Apply a diagonal scaling to the coordinates. -/
def applyBoost (b : HyperbolicBoost) (x : Point4) : Point4 :=
  ⟨b.lam1 * x.x1, b.lam2 * x.x2, b.lam3 * x.x3, b.lam4 * x.x4⟩

/-- Every specified diagonal scaling preserves the quartic polynomial. -/
theorem berwald_moor_boost_invariance (b : HyperbolicBoost) (x : Point4) :
    berwaldMoorForm (applyBoost b x) = berwaldMoorForm x := by
  change (b.lam1 * x.x1) * (b.lam2 * x.x2) * (b.lam3 * x.x3) * (b.lam4 * x.x4) = _
  calc
    _ = (b.lam1 * b.lam2 * b.lam3 * b.lam4) * berwaldMoorForm x := by
      dsimp [berwaldMoorForm]
      ring
    _ = berwaldMoorForm x := by rw [b.h_det, one_mul]

#print axioms berwald_moor_homogeneity_four
#print axioms berwald_moor_multiplicative
#print axioms berwald_moor_zero_iff_isotropic
#print axioms berwald_moor_not_positive_definite_on_entire_space
#print axioms berwald_moor_pos_in_positive_cone
#print axioms positive_cone_vector_ne_zero
#print axioms berwald_moor_boost_invariance

end FinslerPolyMetric
