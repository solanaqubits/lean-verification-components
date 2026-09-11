import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

noncomputable section

namespace HopfOctonions

/-- Seven real coordinates. -/
@[ext] structure Point7 where
  x1 : ℝ
  x2 : ℝ
  x3 : ℝ
  x4 : ℝ
  x5 : ℝ
  x6 : ℝ
  x7 : ℝ

namespace Point7

def zero : Point7 := ⟨0, 0, 0, 0, 0, 0, 0⟩

def add (a b : Point7) : Point7 :=
  ⟨a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3, a.x4 + b.x4, a.x5 + b.x5, a.x6 + b.x6, a.x7 + b.x7⟩

def sub (a b : Point7) : Point7 :=
  ⟨a.x1 - b.x1, a.x2 - b.x2, a.x3 - b.x3, a.x4 - b.x4, a.x5 - b.x5, a.x6 - b.x6, a.x7 - b.x7⟩

def neg (a : Point7) : Point7 :=
  ⟨-a.x1, -a.x2, -a.x3, -a.x4, -a.x5, -a.x6, -a.x7⟩

def smul (c : ℝ) (a : Point7) : Point7 :=
  ⟨c * a.x1, c * a.x2, c * a.x3, c * a.x4, c * a.x5, c * a.x6, c * a.x7⟩

instance : Zero Point7 := ⟨zero⟩

instance : Add Point7 := ⟨add⟩

instance : Sub Point7 := ⟨sub⟩

instance : Neg Point7 := ⟨neg⟩

instance : SMul ℝ Point7 := ⟨smul⟩

@[simp] theorem zero_x1 : (0 : Point7).x1 = 0 := rfl

@[simp] theorem add_x1 (a b : Point7) : (a + b).x1 = a.x1 + b.x1 := rfl

@[simp] theorem sub_x1 (a b : Point7) : (a - b).x1 = a.x1 - b.x1 := rfl

@[simp] theorem neg_x1 (a : Point7) : (-a).x1 = -a.x1 := rfl

@[simp] theorem smul_x1 (c : ℝ) (a : Point7) : (c • a).x1 = c * a.x1 := rfl

@[simp] theorem zero_x2 : (0 : Point7).x2 = 0 := rfl

@[simp] theorem add_x2 (a b : Point7) : (a + b).x2 = a.x2 + b.x2 := rfl

@[simp] theorem sub_x2 (a b : Point7) : (a - b).x2 = a.x2 - b.x2 := rfl

@[simp] theorem neg_x2 (a : Point7) : (-a).x2 = -a.x2 := rfl

@[simp] theorem smul_x2 (c : ℝ) (a : Point7) : (c • a).x2 = c * a.x2 := rfl

@[simp] theorem zero_x3 : (0 : Point7).x3 = 0 := rfl

@[simp] theorem add_x3 (a b : Point7) : (a + b).x3 = a.x3 + b.x3 := rfl

@[simp] theorem sub_x3 (a b : Point7) : (a - b).x3 = a.x3 - b.x3 := rfl

@[simp] theorem neg_x3 (a : Point7) : (-a).x3 = -a.x3 := rfl

@[simp] theorem smul_x3 (c : ℝ) (a : Point7) : (c • a).x3 = c * a.x3 := rfl

@[simp] theorem zero_x4 : (0 : Point7).x4 = 0 := rfl

@[simp] theorem add_x4 (a b : Point7) : (a + b).x4 = a.x4 + b.x4 := rfl

@[simp] theorem sub_x4 (a b : Point7) : (a - b).x4 = a.x4 - b.x4 := rfl

@[simp] theorem neg_x4 (a : Point7) : (-a).x4 = -a.x4 := rfl

@[simp] theorem smul_x4 (c : ℝ) (a : Point7) : (c • a).x4 = c * a.x4 := rfl

@[simp] theorem zero_x5 : (0 : Point7).x5 = 0 := rfl

@[simp] theorem add_x5 (a b : Point7) : (a + b).x5 = a.x5 + b.x5 := rfl

@[simp] theorem sub_x5 (a b : Point7) : (a - b).x5 = a.x5 - b.x5 := rfl

@[simp] theorem neg_x5 (a : Point7) : (-a).x5 = -a.x5 := rfl

@[simp] theorem smul_x5 (c : ℝ) (a : Point7) : (c • a).x5 = c * a.x5 := rfl

@[simp] theorem zero_x6 : (0 : Point7).x6 = 0 := rfl

@[simp] theorem add_x6 (a b : Point7) : (a + b).x6 = a.x6 + b.x6 := rfl

@[simp] theorem sub_x6 (a b : Point7) : (a - b).x6 = a.x6 - b.x6 := rfl

@[simp] theorem neg_x6 (a : Point7) : (-a).x6 = -a.x6 := rfl

@[simp] theorem smul_x6 (c : ℝ) (a : Point7) : (c • a).x6 = c * a.x6 := rfl

@[simp] theorem zero_x7 : (0 : Point7).x7 = 0 := rfl

@[simp] theorem add_x7 (a b : Point7) : (a + b).x7 = a.x7 + b.x7 := rfl

@[simp] theorem sub_x7 (a b : Point7) : (a - b).x7 = a.x7 - b.x7 := rfl

@[simp] theorem neg_x7 (a : Point7) : (-a).x7 = -a.x7 := rfl

@[simp] theorem smul_x7 (c : ℝ) (a : Point7) : (c • a).x7 = c * a.x7 := rfl

def dot (a b : Point7) : ℝ :=
  a.x1 * b.x1 + a.x2 * b.x2 + a.x3 * b.x3 + a.x4 * b.x4 +
    a.x5 * b.x5 + a.x6 * b.x6 + a.x7 * b.x7

end Point7

open Point7

/-- Coordinate product with oriented triples
(1,2,4), (2,3,5), (3,4,6), (4,5,7), (5,6,1), (6,7,2), (7,1,3).
No eight-dimensional octonion algebra is constructed here. -/
def cross7 (u v : Point7) : Point7 :=
  ⟨(u.x2 * v.x4 - u.x4 * v.x2) + (u.x3 * v.x7 - u.x7 * v.x3) +
      (u.x5 * v.x6 - u.x6 * v.x5),
   (u.x3 * v.x5 - u.x5 * v.x3) + (u.x4 * v.x1 - u.x1 * v.x4) +
      (u.x6 * v.x7 - u.x7 * v.x6),
   (u.x4 * v.x6 - u.x6 * v.x4) + (u.x5 * v.x2 - u.x2 * v.x5) +
      (u.x7 * v.x1 - u.x1 * v.x7),
   (u.x5 * v.x7 - u.x7 * v.x5) + (u.x6 * v.x3 - u.x3 * v.x6) +
      (u.x1 * v.x2 - u.x2 * v.x1),
   (u.x6 * v.x1 - u.x1 * v.x6) + (u.x7 * v.x4 - u.x4 * v.x7) +
      (u.x2 * v.x3 - u.x3 * v.x2),
   (u.x7 * v.x2 - u.x2 * v.x7) + (u.x1 * v.x5 - u.x5 * v.x1) +
      (u.x3 * v.x4 - u.x4 * v.x3),
   (u.x1 * v.x3 - u.x3 * v.x1) + (u.x2 * v.x6 - u.x6 * v.x2) +
      (u.x4 * v.x5 - u.x5 * v.x4)⟩

theorem cross7_skew (u v : Point7) : cross7 v u = -cross7 u v := by
  ext <;> simp only [cross7, neg_x1, neg_x2, neg_x3, neg_x4, neg_x5, neg_x6, neg_x7] <;> ring

theorem cross7_self (u : Point7) : cross7 u u = 0 := by
  ext <;> simp [cross7] <;> ring

theorem cross7_dot_left (u v : Point7) : dot u (cross7 u v) = 0 := by
  dsimp [dot, cross7]
  ring

theorem cross7_dot_right (u v : Point7) : dot v (cross7 u v) = 0 := by
  dsimp [dot, cross7]
  ring

theorem cross7_add_left (u v w : Point7) :
    cross7 (u + v) w = cross7 u w + cross7 v w := by
  ext <;> simp only [cross7,
    add_x1, add_x2, add_x3, add_x4, add_x5, add_x6, add_x7] <;> ring

theorem cross7_add_right (u v w : Point7) :
    cross7 u (v + w) = cross7 u v + cross7 u w := by
  ext <;> simp only [cross7,
    add_x1, add_x2, add_x3, add_x4, add_x5, add_x6, add_x7] <;> ring

theorem cross7_smul_left (c : ℝ) (u v : Point7) :
    cross7 (c • u) v = c • cross7 u v := by
  ext <;> simp only [cross7,
    smul_x1, smul_x2, smul_x3, smul_x4, smul_x5, smul_x6, smul_x7] <;> ring

theorem cross7_smul_right (c : ℝ) (u v : Point7) :
    cross7 u (c • v) = c • cross7 u v := by
  ext <;> simp only [cross7,
    smul_x1, smul_x2, smul_x3, smul_x4, smul_x5, smul_x6, smul_x7] <;> ring

/-- The repeated-argument cross-product identity. -/
theorem double_cross7 (p v : Point7) :
    cross7 p (cross7 p v) = (dot p v) • p - (dot p p) • v := by
  ext <;> simp only [cross7, sub_x1, sub_x2, sub_x3, sub_x4, sub_x5, sub_x6, sub_x7,
    smul_x1, smul_x2, smul_x3, smul_x4, smul_x5, smul_x6, smul_x7, dot] <;> ring

/-- On the orthogonal space at a unit vector, applying the product twice is negation. -/
theorem almost_complex_S6_sq (p v : Point7) (h_unit : dot p p = 1) (h_ortho : dot p v = 0) :
    cross7 p (cross7 p v) = -v := by
  rw [double_cross7, h_ortho, h_unit]
  ext <;> simp

/-- The image is orthogonal to the base point, hence stays in its orthogonal space. -/
theorem cross7_preserves_tangent (p v : Point7) : dot p (cross7 p v) = 0 :=
  cross7_dot_left p v

def e1 : Point7 := ⟨1, 0, 0, 0, 0, 0, 0⟩
def e2 : Point7 := ⟨0, 1, 0, 0, 0, 0, 0⟩
def e5 : Point7 := ⟨0, 0, 0, 0, 1, 0, 0⟩

/-- A nonassociativity witness; no claim about a Nijenhuis tensor is inferred. -/
theorem cross7_non_associative :
    cross7 (cross7 e1 e2) e5 ≠ cross7 e1 (cross7 e2 e5) := by
  intro h
  have hx := congrArg Point7.x7 h
  norm_num [cross7, e1, e2, e5] at hx

/-- Selected coordinate identities, not a smooth tangent-bundle construction. -/
structure HopfOctonionsFormalSuite : Prop where
  h_skew : ∀ u v : Point7, cross7 v u = -cross7 u v
  h_ortho_left : ∀ u v : Point7, dot u (cross7 u v) = 0
  h_ortho_right : ∀ u v : Point7, dot v (cross7 u v) = 0
  h_double_id : ∀ p v : Point7, cross7 p (cross7 p v) = (dot p v) • p - (dot p p) • v
  h_almost_cplx : ∀ p v : Point7, dot p p = 1 → dot p v = 0 → cross7 p (cross7 p v) = -v
  h_non_assoc : cross7 (cross7 e1 e2) e5 ≠ cross7 e1 (cross7 e2 e5)

theorem hopf_octonions_master_verification_suite : HopfOctonionsFormalSuite := {
  h_skew := cross7_skew
  h_ortho_left := cross7_dot_left
  h_ortho_right := cross7_dot_right
  h_double_id := double_cross7
  h_almost_cplx := almost_complex_S6_sq
  h_non_assoc := cross7_non_associative
}

#print axioms hopf_octonions_master_verification_suite

end HopfOctonions
