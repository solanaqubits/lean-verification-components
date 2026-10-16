/- Exact kernel and executable regressions for finite-grid range interpolation. -/
import Verification.CryptoBulletproofsRangeInterpolation

open CryptoBulletproofsRangeInterpolation CryptoBulletproofsRangeReduction
open CryptoBulletproofsRangeInterpolation.Regression
open scoped BigOperators
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

-- The finite grid recovers coefficients over any field, including n=0 (vacuous coefficients).
example {F : Type} [Field F] {n : ℕ} (c y : Fin n → F) (hy : Function.Injective y)
    (h : ∀ k, ∑ i, c i * y k ^ i.val = 0) : ∀ i, c i = 0 :=
  poly_coeff_zero_of_injective_grid c y hy h
example (c : Fin 0 → F) : ∀ i, c i = 0 := by intro i; exact i.elim0
example (c₀ c₁ c₂ : F) (h : ∀ j, c₀ + gridZ j * c₁ + gridZ j ^ 2 * c₂ = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := quadratic_zero_of_three_points _ _ _ gridZ (by decide) h
example : gridY 4 0 = 0 ∧ gridZ 0 = 0 := by decide
example : 4 ≤ 101 ∧ 3 ≤ 101 := grid_card_bounds (gridY 4) gridZ (by decide) (by decide)
example {n : ℕ} (y : Fin n → ZMod 101) (hy : Function.Injective y) : n ≤ 101 :=
  (grid_card_bounds y gridZ hy (by decide)).1

example : formal_t0 a1 (rightBits a1) = formal_rhs 1 1 :=
  verify_grid_sound _ _ _ _ _ honest_one
example : formal_t0 a2 (rightBits a2) = formal_rhs 3 2 :=
  verify_grid_sound _ _ _ _ _ honest_two
example : formal_t0 a4 (rightBits a4) = formal_rhs 5 4 :=
  verify_grid_sound _ _ _ _ _ honest_four
example : (1 : ℕ) < 2 ^ 1 :=
  grid_equalities_imply_natural_range a1 (rightBits a1) 1 (by decide) (gridY 1) gridZ
    (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_one).2.2.2
example : (3 : ℕ) < 2 ^ 2 :=
  grid_equalities_imply_natural_range a2 (rightBits a2) 3 (by decide) (gridY 2) gridZ
    (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_two).2.2.2
example : (5 : ℕ) < 2 ^ 4 := honest_four_range
example : reconstructed_value a1 = 1 :=
  grid_reconstructed_value_eq a1 (rightBits a1) 1 (by decide) (gridY 1) gridZ
    (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_one).2.2.2
example : reconstructed_value a2 = 3 :=
  grid_reconstructed_value_eq a2 (rightBits a2) 3 (by decide) (gridY 2) gridZ
    (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_two).2.2.2
example : reconstructed_value a4 = 5 :=
  grid_reconstructed_value_eq a4 (rightBits a4) 5 (by decide) (gridY 4) gridZ
    (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_four).2.2.2
example : ∀ i, a4 i * (a4 i - 1) = 0 :=
  (grid_equalities_imply_field_range a4 (rightBits a4) 5 (by decide) (gridY 4) gridZ
    (by decide) (by decide) ((verify_grid_success_iff _ _ _ _ _).mp honest_four).2.2.2).2.2.1
example : ∀ i, a2 i - rightBits a2 i = 1 :=
  (grid_equalities_imply_field_range a2 (rightBits a2) 3 (by decide) (gridY 2) gridZ
    (by decide) (by decide) ((verify_grid_success_iff _ _ _ _ _).mp honest_two).2.2.2).2.1
example : ∀ i, a1 i = 0 ∨ a1 i = 1 :=
  (formal_coefficients_imply_range _ _ _ (verify_grid_sound _ _ _ _ _ honest_one)).2.1

example (y z : F) : ((residual_poly a4 (rightBits a4) 5).eval (Polynomial.C z)).eval y =
    residual_eval a4 (rightBits a4) 5 y z := residual_poly_eval _ _ _ _ _
example : (residual_poly a4 (rightBits a4) 5).natDegree ≤ 2 := residual_poly_degree_Z _ _ _
example (j : ℕ) : ((residual_poly a4 (rightBits a4) 5).coeff j).natDegree ≤ 3 :=
  residual_poly_degree_Y _ _ _ j
example (y z : F) : residual_eval ![0] ![0] (-1) y z = z ^ 2 - z := two_z_residual y z
example : formal_t0 (![0] : Fin 1 → F) ![0] ≠ formal_rhs (-1) 1 := two_z_formal_failure
example : (0 : F) - 0 ≠ 1 ∧ (0 : F) ≠ -1 := by decide
example : residual_eval (![0] : Fin 1 → F) ![0] (-1) 0 2 ≠ 0 := two_z_counterexample.2.2.1
example (y z : F) : residual_eval ![2, 0] ![0, 0] 2 y z = z * (1 - y) := repeated_y_residual y z
example : GridEqualities (![2, 0] : Fin 2 → F) ![0, 0] 2 (fun _ => 1) gridZ := repeated_y_counterexample.1
example : (2 : F) * (2 - 1) ≠ 0 := repeated_y_counterexample.2.1
example : verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) ![0, 1, 1] =
    .error .repeatedZ := repeated_z_rejected
example : verify_interpolation_grid a4 (rightBits a4) 6 (gridY 4) gridZ =
    .error .invalidEquality := corrupted_value_rejected
example : verify_interpolation_grid a4 (fun _ => 0) 5 (gridY 4) gridZ =
    .error .invalidEquality := by decide
example : verify_interpolation_grid a4 (rightBits a4) 5 ![3, 2, 1, 0] ![2, 1, 0] = .ok () := by decide
-- A noncanonical natural representative passes the field test but is not in range.
example : GridEqualities a4 (rightBits a4) (106 : F) (gridY 4) gridZ ∧ ¬ (106 : ℕ) < 16 := by decide
example : verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) ![1, -1, 2] = .ok () := by decide
-- Distinct points, not distinct squares: the IPA constraint is intentionally absent here.
example : verify_interpolation_grid (![0] : Fin 1 → F) ![0] (-1) (gridY 1) ![0, 1, 1] =
    .error .repeatedZ := repeated_z_counterexample.2

#eval verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) gridZ
#eval verify_interpolation_grid a2 (rightBits a2) 3 (gridY 2) gridZ
#eval verify_interpolation_grid a4 (rightBits a4) 5 (gridY 4) gridZ
#eval verify_interpolation_grid a4 (rightBits a4) 5 ![3, 2, 1, 0] ![2, 1, 0]
#eval verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) ![1, -1, 2]
#eval verify_interpolation_grid a4 (rightBits a4) 6 (gridY 4) gridZ
#eval verify_interpolation_grid a4 (fun _ => 0) 5 (gridY 4) gridZ
#eval verify_interpolation_grid (![2, 0] : Fin 2 → F) ![0, 0] 2 (fun _ => 1) gridZ
#eval verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) ![0, 1, 1]
#eval verify_interpolation_grid (![0] : Fin 1 → F) ![0] (-1) (gridY 1) ![0, 1, 1]
#eval verify_interpolation_grid (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
  (0 : F) (gridY 0) gridZ
#eval verify_interpolation_grid a4 (rightBits a4) (106 : F) (gridY 4) gridZ
