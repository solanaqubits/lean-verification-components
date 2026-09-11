import Verification.FinslerPolyMetric

set_option linter.style.header false

noncomputable section

namespace FinslerMultilinear

open FinslerPolyMetric

@[simp] theorem point_add_x1 (a b : Point4) : (a + b).x1 = a.x1 + b.x1 := rfl

@[simp] theorem point_add_x2 (a b : Point4) : (a + b).x2 = a.x2 + b.x2 := rfl

@[simp] theorem point_add_x3 (a b : Point4) : (a + b).x3 = a.x3 + b.x3 := rfl

@[simp] theorem point_add_x4 (a b : Point4) : (a + b).x4 = a.x4 + b.x4 := rfl

/-- Sum over the 24 assignments of distinct coordinate indices to the four arguments. -/
def sym4Sum (a b c d : Point4) : ℝ :=
  a.x1 * b.x2 * c.x3 * d.x4 +
  a.x1 * b.x2 * c.x4 * d.x3 +
  a.x1 * b.x3 * c.x2 * d.x4 +
  a.x1 * b.x3 * c.x4 * d.x2 +
  a.x1 * b.x4 * c.x2 * d.x3 +
  a.x1 * b.x4 * c.x3 * d.x2 +
  a.x2 * b.x1 * c.x3 * d.x4 +
  a.x2 * b.x1 * c.x4 * d.x3 +
  a.x2 * b.x3 * c.x1 * d.x4 +
  a.x2 * b.x3 * c.x4 * d.x1 +
  a.x2 * b.x4 * c.x1 * d.x3 +
  a.x2 * b.x4 * c.x3 * d.x1 +
  a.x3 * b.x1 * c.x2 * d.x4 +
  a.x3 * b.x1 * c.x4 * d.x2 +
  a.x3 * b.x2 * c.x1 * d.x4 +
  a.x3 * b.x2 * c.x4 * d.x1 +
  a.x3 * b.x4 * c.x1 * d.x2 +
  a.x3 * b.x4 * c.x2 * d.x1 +
  a.x4 * b.x1 * c.x2 * d.x3 +
  a.x4 * b.x1 * c.x3 * d.x2 +
  a.x4 * b.x2 * c.x1 * d.x3 +
  a.x4 * b.x2 * c.x3 * d.x1 +
  a.x4 * b.x3 * c.x1 * d.x2 +
  a.x4 * b.x3 * c.x2 * d.x1

/-- Symmetric polarization of the coordinate product. -/
def berwaldMoor4Form (a b c d : Point4) : ℝ :=
  (1 / 24 : ℝ) * sym4Sum a b c d

theorem berwald_moor_diagonal_eq (x : Point4) :
    berwaldMoor4Form x x x x = berwaldMoorForm x := by
  dsimp [berwaldMoor4Form, sym4Sum, berwaldMoorForm]
  ring

theorem berwaldMoor4Form_swap12 (a b c d : Point4) :
    berwaldMoor4Form a b c d = berwaldMoor4Form b a c d := by
  dsimp [berwaldMoor4Form, sym4Sum]
  ring

theorem berwaldMoor4Form_swap23 (a b c d : Point4) :
    berwaldMoor4Form a b c d = berwaldMoor4Form a c b d := by
  dsimp [berwaldMoor4Form, sym4Sum]
  ring

theorem berwaldMoor4Form_swap34 (a b c d : Point4) :
    berwaldMoor4Form a b c d = berwaldMoor4Form a b d c := by
  dsimp [berwaldMoor4Form, sym4Sum]
  ring

theorem berwaldMoor4Form_smul_left (k : ℝ) (a b c d : Point4) :
    berwaldMoor4Form (k • a) b c d = k * berwaldMoor4Form a b c d := by
  dsimp [berwaldMoor4Form, sym4Sum, Point4.smul]
  ring

theorem berwaldMoor4Form_add_left (a b c d e : Point4) :
    berwaldMoor4Form (a + e) b c d =
      berwaldMoor4Form a b c d + berwaldMoor4Form e b c d := by
  simp only [berwaldMoor4Form, sym4Sum, point_add_x1, point_add_x2,
    point_add_x3, point_add_x4]
  ring

theorem berwaldMoor4Form_smul_second (k : ℝ) (a b c d : Point4) :
    berwaldMoor4Form a (k • b) c d = k * berwaldMoor4Form a b c d := by
  dsimp [berwaldMoor4Form, sym4Sum, Point4.smul]
  ring

theorem berwaldMoor4Form_add_second (a b c d e : Point4) :
    berwaldMoor4Form a (b + e) c d =
      berwaldMoor4Form a b c d + berwaldMoor4Form a e c d := by
  simp only [berwaldMoor4Form, sym4Sum, point_add_x1, point_add_x2,
    point_add_x3, point_add_x4]
  ring

theorem berwaldMoor4Form_smul_third (k : ℝ) (a b c d : Point4) :
    berwaldMoor4Form a b (k • c) d = k * berwaldMoor4Form a b c d := by
  dsimp [berwaldMoor4Form, sym4Sum, Point4.smul]
  ring

theorem berwaldMoor4Form_add_third (a b c d e : Point4) :
    berwaldMoor4Form a b (c + e) d =
      berwaldMoor4Form a b c d + berwaldMoor4Form a b e d := by
  simp only [berwaldMoor4Form, sym4Sum, point_add_x1, point_add_x2,
    point_add_x3, point_add_x4]
  ring

theorem berwaldMoor4Form_smul_fourth (k : ℝ) (a b c d : Point4) :
    berwaldMoor4Form a b c (k • d) = k * berwaldMoor4Form a b c d := by
  dsimp [berwaldMoor4Form, sym4Sum, Point4.smul]
  ring

theorem berwaldMoor4Form_add_fourth (a b c d e : Point4) :
    berwaldMoor4Form a b c (d + e) =
      berwaldMoor4Form a b c d + berwaldMoor4Form a b c e := by
  simp only [berwaldMoor4Form, sym4Sum, point_add_x1, point_add_x2,
    point_add_x3, point_add_x4]
  ring

/-- Equality of boost parameters determines equality of boosts. -/
@[ext] theorem boost_ext {a b : HyperbolicBoost}
    (h1 : a.lam1 = b.lam1) (h2 : a.lam2 = b.lam2)
    (h3 : a.lam3 = b.lam3) (h4 : a.lam4 = b.lam4) : a = b := by
  cases a
  cases b
  cases h1
  cases h2
  cases h3
  cases h4
  rfl

def boostId : HyperbolicBoost := ⟨1, 1, 1, 1, by norm_num⟩

def boostMul (a b : HyperbolicBoost) : HyperbolicBoost :=
  ⟨a.lam1 * b.lam1, a.lam2 * b.lam2, a.lam3 * b.lam3, a.lam4 * b.lam4, by
    calc
      _ = (a.lam1 * a.lam2 * a.lam3 * a.lam4) *
          (b.lam1 * b.lam2 * b.lam3 * b.lam4) := by ring
      _ = 1 := by rw [a.h_det, b.h_det, one_mul]⟩

def boostInv (b : HyperbolicBoost) : HyperbolicBoost :=
  ⟨b.lam1⁻¹, b.lam2⁻¹, b.lam3⁻¹, b.lam4⁻¹, by
    rw [← mul_inv, ← mul_inv, ← mul_inv, b.h_det, inv_one]⟩

theorem boost_mul_assoc (a b c : HyperbolicBoost) :
    boostMul (boostMul a b) c = boostMul a (boostMul b c) := by
  apply boost_ext <;> dsimp [boostMul] <;> ring

theorem boost_mul_id (b : HyperbolicBoost) : boostMul boostId b = b := by
  apply boost_ext <;> dsimp [boostMul, boostId] <;> ring

theorem boost_mul_comm (a b : HyperbolicBoost) : boostMul a b = boostMul b a := by
  apply boost_ext <;> dsimp [boostMul] <;> ring

theorem boost_id_right (b : HyperbolicBoost) : boostMul b boostId = b := by
  rw [boost_mul_comm, boost_mul_id]

theorem boost_parameters_ne_zero (b : HyperbolicBoost) :
    b.lam1 ≠ 0 ∧ b.lam2 ≠ 0 ∧ b.lam3 ≠ 0 ∧ b.lam4 ≠ 0 := by
  have h : b.lam1 * b.lam2 * b.lam3 * b.lam4 ≠ 0 := by rw [b.h_det]; norm_num
  simpa only [mul_ne_zero_iff, and_assoc] using h

theorem boost_inv_mul (b : HyperbolicBoost) : boostMul (boostInv b) b = boostId := by
  rcases boost_parameters_ne_zero b with ⟨h1, h2, h3, h4⟩
  apply boost_ext <;> simp [boostMul, boostInv, boostId, h1, h2, h3, h4]

theorem boost_mul_inv (b : HyperbolicBoost) : boostMul b (boostInv b) = boostId := by
  rw [boost_mul_comm, boost_inv_mul]

/-- The diagonal form-preserving scalings form an abelian group. -/
instance : CommGroup HyperbolicBoost where
  mul := boostMul
  one := boostId
  inv := boostInv
  mul_assoc := boost_mul_assoc
  one_mul := boost_mul_id
  mul_one := boost_id_right
  inv_mul_cancel := boost_inv_mul
  mul_comm := boost_mul_comm

theorem applyBoost_id (x : Point4) : applyBoost boostId x = x := by
  cases x
  simp [applyBoost, boostId]

theorem applyBoost_mul (a b : HyperbolicBoost) (x : Point4) :
    applyBoost (boostMul a b) x = applyBoost a (applyBoost b x) := by
  simp [applyBoost, boostMul, mul_assoc]

/-- Simultaneous diagonal scaling preserves the polarized form. -/
theorem berwaldMoor4Form_boost_invariant (b : HyperbolicBoost) (a v c d : Point4) :
    berwaldMoor4Form (applyBoost b a) (applyBoost b v) (applyBoost b c) (applyBoost b d) =
      berwaldMoor4Form a v c d := by
  calc
    _ = (b.lam1 * b.lam2 * b.lam3 * b.lam4) * berwaldMoor4Form a v c d := by
      dsimp [berwaldMoor4Form, sym4Sum, applyBoost]
      ring
    _ = berwaldMoor4Form a v c d := by rw [b.h_det, one_mul]

#print axioms berwald_moor_diagonal_eq
#print axioms berwaldMoor4Form_boost_invariant
#print axioms boost_inv_mul

end FinslerMultilinear
