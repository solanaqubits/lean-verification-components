import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Abel

set_option linter.style.header false

namespace HopfAlmostComplex

/-- A real-linear operator whose square is negative identity. -/
structure AlmostComplex (V : Type*) [AddCommGroup V] [Module ℝ V] where
  J : V → V
  map_add : ∀ x y : V, J (x + y) = J x + J y
  map_smul : ∀ (c : ℝ) (x : V), J (c • x) = c • J x
  J_sq : ∀ x : V, J (J x) = -x

/-- A skew bilinear bracket. The name is retained, but no Jacobi identity is required. -/
structure LieBracket (V : Type*) [AddCommGroup V] [Module ℝ V] where
  bracket : V → V → V
  add_left : ∀ x y z : V, bracket (x + y) z = bracket x z + bracket y z
  add_right : ∀ x y z : V, bracket x (y + z) = bracket x y + bracket x z
  smul_left : ∀ (c : ℝ) (x y : V), bracket (c • x) y = c • bracket x y
  smul_right : ∀ (c : ℝ) (x y : V), bracket x (c • y) = c • bracket x y
  skew : ∀ x y : V, bracket y x = - bracket x y

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem J_neg (ac : AlmostComplex V) (x : V) : ac.J (-x) = - ac.J x := by
  simpa only [neg_one_smul] using ac.map_smul (-1) x

theorem J_sub (ac : AlmostComplex V) (x y : V) : ac.J (x - y) = ac.J x - ac.J y := by
  rw [sub_eq_add_neg, ac.map_add, J_neg, ← sub_eq_add_neg]

theorem J_inv (ac : AlmostComplex V) (x : V) : ac.J (- ac.J x) = x := by
  rw [J_neg, ac.J_sq, neg_neg]

/-- A nonzero vector cannot be an eigenvector with a real eigenvalue. -/
theorem no_real_eigenvalues (ac : AlmostComplex V) (lam : ℝ) (v : V) (hv : v ≠ 0) :
    ac.J v ≠ lam • v := by
  intro he
  have hs : ac.J (ac.J v) = (lam ^ 2) • v := by
    rw [he, ac.map_smul, he, smul_smul, sq]
  rw [ac.J_sq] at hs
  have hc : (lam ^ 2 + 1) • v = 0 := by
    rw [add_smul, one_smul, ← hs]
    exact neg_add_cancel v
  have hp : 0 < lam ^ 2 + 1 := by positivity
  have hz := congrArg (fun w : V => (lam ^ 2 + 1)⁻¹ • w) hc
  simp only [smul_smul, inv_mul_cancel₀ (ne_of_gt hp), one_smul, smul_zero] at hz
  exact hv hz

/-- The algebraic Nijenhuis expression for the specified operator and bracket. -/
def nijenhuis (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V) : V :=
  lb.bracket (ac.J X) (ac.J Y) -
  ac.J (lb.bracket (ac.J X) Y) -
  ac.J (lb.bracket X (ac.J Y)) - lb.bracket X Y

theorem bracket_neg_left (lb : LieBracket V) (x y : V) :
    lb.bracket (-x) y = - lb.bracket x y := by
  simpa only [neg_one_smul] using lb.smul_left (-1) x y

theorem bracket_neg_right (lb : LieBracket V) (x y : V) :
    lb.bracket x (-y) = - lb.bracket x y := by
  simpa only [neg_one_smul] using lb.smul_right (-1) x y

/-- Skew symmetry of the algebraic Nijenhuis expression. -/
theorem nijenhuis_skew (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V) :
    nijenhuis ac lb Y X = - nijenhuis ac lb X Y := by
  dsimp [nijenhuis]
  rw [lb.skew (ac.J X) (ac.J Y), lb.skew X (ac.J Y),
    lb.skew (ac.J X) Y, lb.skew X Y]
  simp only [J_neg]
  abel

/-- Applying J in the first argument anticommutes with the expression. -/
theorem nijenhuis_J_left (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V) :
    nijenhuis ac lb (ac.J X) Y = - ac.J (nijenhuis ac lb X Y) := by
  dsimp [nijenhuis]
  simp only [ac.J_sq, bracket_neg_left, J_neg, J_sub]
  abel

/-- Applying J in both arguments negates the expression. -/
theorem nijenhuis_J_both (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V) :
    nijenhuis ac lb (ac.J X) (ac.J Y) = - nijenhuis ac lb X Y := by
  dsimp [nijenhuis]
  simp only [ac.J_sq, bracket_neg_left, bracket_neg_right, J_neg]
  abel

#print axioms no_real_eigenvalues
#print axioms nijenhuis_skew
#print axioms nijenhuis_J_left
#print axioms nijenhuis_J_both

end HopfAlmostComplex
