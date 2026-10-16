/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsRangeReduction
import Mathlib.Algebra.Polynomial.Roots

/-! Deterministic interpolation for fixed range witnesses. No transcript extractor,
commitment openings, generator independence or probabilistic sampling is assumed. -/
namespace CryptoBulletproofsRangeInterpolation
open scoped BigOperators
open Polynomial CryptoBulletproofsRangeReduction

section Interpolation
variable {F : Type} [Field F] {n : ℕ}

noncomputable def coeff_poly (c : Fin n → F) : Polynomial F :=
  ∑ i, C (c i) * X ^ i.val

@[simp] theorem coeff_poly_eval (c : Fin n → F) (y : F) :
    (coeff_poly c).eval y = ∑ i, c i * y ^ i.val := by
  simp [coeff_poly, eval_finsetSum]

@[simp] theorem coeff_poly_coeff (c : Fin n → F) (i : Fin n) :
    (coeff_poly c).coeff i.val = c i := by
  simp [coeff_poly, finsetSum_coeff, Fin.val_inj]

theorem coeff_poly_degree_bound (c : Fin n → F) :
    (coeff_poly c).natDegree ≤ n - 1 := by
  apply natDegree_sum_le_of_forall_le
  intro i _
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem poly_coeff_zero_of_injective_grid (c y : Fin n → F)
    (hy : Function.Injective y) (h : ∀ k, ∑ i, c i * y k ^ i.val = 0) :
    ∀ i, c i = 0 := by
  intro i
  have hp : coeff_poly c = 0 :=
    eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hy
      (by simpa using h) (by
        simp only [Fintype.card_fin]
        exact lt_of_le_of_lt (coeff_poly_degree_bound c) (by have := i.isLt; omega))
  simpa using congrArg (fun p : Polynomial F => p.coeff i.val) hp

theorem quadratic_zero_of_three_points (c₀ c₁ c₂ : F) (z : Fin 3 → F)
    (hz : Function.Injective z) (h : ∀ j, c₀ + z j * c₁ + z j ^ 2 * c₂ = 0) :
    c₀ = 0 ∧ c₁ = 0 ∧ c₂ = 0 := by
  have hc := poly_coeff_zero_of_injective_grid ![c₀, c₁, c₂] z hz (by
    intro j
    simpa [Fin.sum_univ_succ, mul_comm, add_assoc] using h j)
  exact ⟨hc 0, hc 1, hc 2⟩
end Interpolation

section Range
variable {q n : ℕ} [Fact (Nat.Prime q)]

def residual_eval (a b : Fin n → ZMod q) (v y z : ZMod q) : ZMod q :=
  t0 a b y z - (z ^ 2 * v + delta_fn y z n)

theorem residual_eval_expansion (a b : Fin n → ZMod q) (v y z : ZMod q) :
    residual_eval a b v y z = (∑ i, a i * b i * y ^ i.val) +
      z * (∑ i, (a i - b i - 1) * y ^ i.val) +
      z ^ 2 * ((∑ i, (2 : ZMod q) ^ i.val * a i) - v) :=
  t0_residual a b v y z

noncomputable def residual_poly (a b : Fin n → ZMod q) (v : ZMod q) : YZ (ZMod q) :=
  formal_t0 a b - formal_rhs v n

theorem residual_poly_expansion (a b : Fin n → ZMod q) (v : ZMod q) :
    residual_poly a b v = C (coeff_poly (fun i => a i * b i)) +
      C (coeff_poly (fun i => a i - b i - 1)) * X +
      C (C ((∑ i, (2 : ZMod q) ^ i.val * a i) - v)) * X ^ 2 :=
  formal_residual a b v

/-- Evaluation of the nested formal polynomial agrees with the scalar residual. -/
theorem residual_poly_eval (a b : Fin n → ZMod q) (v y z : ZMod q) :
    ((residual_poly a b v).eval (C z)).eval y = residual_eval a b v y z := by
  rw [residual_poly_expansion, residual_eval_expansion]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, coeff_poly_eval]
  ring

/-- The outer variable is Z; the inner variable is Y. -/
theorem residual_poly_degree_Z (a b : Fin n → ZMod q) (v : ZMod q) :
    (residual_poly a b v).natDegree ≤ 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro m hm
  rw [residual_poly_expansion]
  simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C]
  simp [show m ≠ 0 by omega, show m ≠ 1 by omega, show m ≠ 2 by omega]

/-- Every Z-coefficient has Y-degree at most n-1 (also valid for zero polynomials). -/
theorem residual_poly_degree_Y (a b : Fin n → ZMod q) (v : ZMod q) (j : ℕ) :
    ((residual_poly a b v).coeff j).natDegree ≤ n - 1 := by
  rw [residual_poly_expansion]
  simp only [coeff_add, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_C]
  split_ifs <;> try omega
  all_goals simp only [zero_add, add_zero, natDegree_C, natDegree_zero]
  all_goals first | exact coeff_poly_degree_bound _ | omega

/-- A single fixed witness is used on the entire rectangular grid. -/
def GridEqualities (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q) : Prop :=
  ∀ i j, t0 a b (y i) (z j) = z j ^ 2 * v + delta_fn (y i) (z j) n

theorem grid_card_bounds (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z) : n ≤ q ∧ 3 ≤ q := by
  constructor
  · simpa using Fintype.card_le_of_injective y hy
  · simpa using Fintype.card_le_of_injective z hz

theorem grid_equalities_imply_formal_identity (a b : Fin n → ZMod q) (v : ZMod q)
    (hn : 1 ≤ n) (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z) (h : GridEqualities a b v y z) :
    formal_t0 a b = formal_rhs v n := by
  have hc : ∀ k : Fin n, (∑ i, a i * b i * y k ^ i.val) = 0 ∧
      (∑ i, (a i - b i - 1) * y k ^ i.val) = 0 ∧
      (∑ i, (2 : ZMod q) ^ i.val * a i) - v = 0 := by
    intro k
    apply quadratic_zero_of_three_points _ _ _ z hz
    intro j
    rw [← residual_eval_expansion]
    exact sub_eq_zero.mpr (h k j)
  have hab := poly_coeff_zero_of_injective_grid (fun i => a i * b i) y hy (fun k => (hc k).1)
  have hdiff := poly_coeff_zero_of_injective_grid (fun i => a i - b i - 1) y hy
    (fun k => (hc k).2.1)
  have hv := (hc ⟨0, hn⟩).2.2
  apply sub_eq_zero.mp
  rw [formal_residual]
  simp [hab, hdiff, hv]

theorem grid_equalities_imply_field_range (a b : Fin n → ZMod q) (v : ZMod q)
    (hn : 1 ≤ n) (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z) (h : GridEqualities a b v y z) :
    (∀ i, a i * b i = 0) ∧ (∀ i, a i - b i = 1) ∧
      (∀ i, a i * (a i - 1) = 0) ∧ (∑ i, (2 : ZMod q) ^ i.val * a i) = v := by
  obtain ⟨hb, hbit, hv⟩ := formal_coefficients_imply_range a b v
    (grid_equalities_imply_formal_identity a b v hn y z hy hz h)
  have hp : ∀ i, a i * (a i - 1) = 0 := by
    intro i
    rcases hbit i with hi | hi <;> simp [hi]
  exact ⟨fun i => by rw [hb]; exact hp i, fun i => by rw [hb]; ring, hp, hv⟩

theorem grid_equalities_imply_natural_range (a b : Fin n → ZMod q) (v : ℕ)
    (hn : 1 ≤ n) (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z) (hv : v < q) (hq : 2 ^ n < q)
    (h : GridEqualities a b (v : ZMod q) y z) : v < 2 ^ n :=
  formal_identity_natural_range a b v hv hq
    (grid_equalities_imply_formal_identity a b (v : ZMod q) hn y z hy hz h)

/-- Canonical natural reconstruction; this is separate from field equality. -/
def reconstructed_value (a : Fin n → ZMod q) : ℕ :=
  ∑ i, 2 ^ i.val * if a i = 0 then 0 else 1

theorem grid_reconstructed_value_eq (a b : Fin n → ZMod q) (v : ℕ)
    (hn : 1 ≤ n) (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z) (hv : v < q) (hq : 2 ^ n < q)
    (h : GridEqualities a b (v : ZMod q) y z) : reconstructed_value a = v := by
  obtain ⟨_, hbit, he⟩ := formal_coefficients_imply_range a b (v : ZMod q)
    (grid_equalities_imply_formal_identity a b (v : ZMod q) hn y z hy hz h)
  let bits : Fin n → ℕ := fun i => if a i = 0 then 0 else 1
  have hb : ∀ i, bits i ≤ 1 := by intro i; simp only [bits]; split <;> omega
  have hc : ∀ i, (bits i : ZMod q) = a i := by
    intro i
    rcases hbit i with hi | hi <;> simp [bits, hi]
  have hlt := CryptoPedersenRangeProofLinear.bitValue_lt bits hb
  have heq : (CryptoPedersenRangeProofLinear.bitValue bits : ZMod q) = (v : ZMod q) := by
    rw [CryptoPedersenRangeProofLinear.bitValue_cast]
    simpa only [CryptoPedersenRangeProofLinear.weight, hc] using he
  have hnateq := congrArg ZMod.val heq
  simp only [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hlt hq), Nat.mod_eq_of_lt hv] at hnateq
  exact hnateq

instance gridEqualitiesDecidable (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q) : Decidable (GridEqualities a b v y z) :=
  inferInstanceAs (Decidable (∀ i j, t0 a b (y i) (z j) = z j ^ 2 * v + delta_fn (y i) (z j) n))

inductive GridError where
  | emptyWitness | repeatedY | repeatedZ | invalidEquality
  deriving DecidableEq, Repr

/-- Checks supplied fixed witnesses; does not extract a witness or invert a matrix. -/
def verify_interpolation_grid (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q) : Except GridError Unit :=
  if 1 ≤ n then
    if Function.Injective y then
      if Function.Injective z then
        if GridEqualities a b v y z then .ok () else .error .invalidEquality
      else .error .repeatedZ
    else .error .repeatedY
  else .error .emptyWitness

theorem verify_grid_success_iff (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q) :
    verify_interpolation_grid a b v y z = .ok () ↔
      1 ≤ n ∧ Function.Injective y ∧ Function.Injective z ∧ GridEqualities a b v y z := by
  simp only [verify_interpolation_grid]
  split_ifs <;> simp_all

theorem verify_grid_sound (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (h : verify_interpolation_grid a b v y z = .ok ()) :
    formal_t0 a b = formal_rhs v n := by
  obtain ⟨hn, hy, hz, he⟩ := (verify_grid_success_iff a b v y z).mp h
  exact grid_equalities_imply_formal_identity a b v hn y z hy hz he

theorem honest_grid_complete (a b : Fin n → ZMod q) (v : ZMod q)
    (hn : 1 ≤ n) (y : Fin n → ZMod q) (z : Fin 3 → ZMod q)
    (hy : Function.Injective y) (hz : Function.Injective z)
    (hb : ∀ i, b i = a i - 1) (hbit : ∀ i, a i * b i = 0)
    (hv : ∑ i, (2 : ZMod q) ^ i.val * a i = v) :
    verify_interpolation_grid a b v y z = .ok () := by
  apply (verify_grid_success_iff a b v y z).mpr
  exact ⟨hn, hy, hz, fun i j => t0_spec a b v (y i) (z j) hb hbit hv⟩

end Range

local instance prime101 : Fact (Nat.Prime 101) := ⟨by decide⟩

namespace Regression
abbrev F := ZMod 101

def gridY (n : ℕ) : Fin n → F := fun i => i.val

def gridZ : Fin 3 → F := ![0, 1, 2]
def a1 : Fin 1 → F := ![1]
def a2 : Fin 2 → F := ![1, 1]
def a4 : Fin 4 → F := ![1, 0, 1, 0]
def rightBits {n : ℕ} (a : Fin n → F) : Fin n → F := fun i => a i - 1

theorem honest_one :
    verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) gridZ = .ok () := by decide

theorem honest_two :
    verify_interpolation_grid a2 (rightBits a2) 3 (gridY 2) gridZ = .ok () := by decide

theorem honest_four :
    verify_interpolation_grid a4 (rightBits a4) 5 (gridY 4) gridZ = .ok () := by decide

theorem honest_four_range : (5 : ℕ) < 2 ^ 4 := by
  exact grid_equalities_imply_natural_range a4 (rightBits a4) 5 (by decide)
    (gridY 4) gridZ (by decide) (by decide) (by decide) (by decide)
    ((verify_grid_success_iff _ _ _ _ _).mp honest_four).2.2.2

theorem two_z_residual (y z : F) : residual_eval ![0] ![0] (-1) y z = z ^ 2 - z := by
  simp only [residual_eval_expansion, Fin.sum_univ_succ]
  simp
  ring

theorem two_z_counterexample :
    residual_eval (![0] : Fin 1 → F) ![0] (-1) 0 0 = 0 ∧
    residual_eval (![0] : Fin 1 → F) ![0] (-1) 0 1 = 0 ∧
    residual_eval (![0] : Fin 1 → F) ![0] (-1) 0 2 ≠ 0 ∧
    ¬ GridEqualities (![0] : Fin 1 → F) ![0] (-1) (gridY 1) gridZ := by decide

/-- All Z challenges pass at the repeated Y point, although a[0]=2 is not a bit. -/
theorem repeated_y_residual (y z : F) :
    residual_eval ![2, 0] ![0, 0] 2 y z = z * (1 - y) := by
  simp [residual_eval_expansion, Fin.sum_univ_succ, mul_sub]
  ring

theorem repeated_y_counterexample :
    GridEqualities (![2, 0] : Fin 2 → F) ![0, 0] 2 (fun _ => 1) gridZ ∧
    (2 : F) * (2 - 1) ≠ 0 ∧
    verify_interpolation_grid (![2, 0] : Fin 2 → F) ![0, 0] 2 (fun _ => 1) gridZ =
      .error .repeatedY := by decide

theorem two_z_formal_failure :
    formal_t0 (![0] : Fin 1 → F) ![0] ≠ formal_rhs (-1) 1 := by
  intro h
  have hb := (formal_coefficients_imply_range (![0] : Fin 1 → F) ![0] (-1) h).1 0
  norm_num at hb

theorem repeated_z_counterexample :
    GridEqualities (![0] : Fin 1 → F) ![0] (-1) (gridY 1) ![0, 1, 1] ∧
    verify_interpolation_grid (![0] : Fin 1 → F) ![0] (-1) (gridY 1) ![0, 1, 1] =
      .error .repeatedZ := by decide

theorem repeated_z_rejected :
    verify_interpolation_grid a1 (rightBits a1) 1 (gridY 1) ![0, 1, 1] =
      .error .repeatedZ := by decide

theorem corrupted_value_rejected :
    verify_interpolation_grid a4 (rightBits a4) 6 (gridY 4) gridZ =
      .error .invalidEquality := by decide

theorem empty_witness_rejected :
    verify_interpolation_grid (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => i.elim0)
      (0 : F) (gridY 0) gridZ = .error .emptyWitness := by decide

end Regression

structure CryptoBulletproofsRangeInterpolationSuite : Prop where
  grid_identity : ∀ {q n : ℕ} [Fact (Nat.Prime q)] (a b : Fin n → ZMod q) (v : ZMod q),
    1 ≤ n → ∀ (y : Fin n → ZMod q) (z : Fin 3 → ZMod q),
      Function.Injective y → Function.Injective z → GridEqualities a b v y z →
        formal_t0 a b = formal_rhs v n
  field_range : ∀ {q n : ℕ} [Fact (Nat.Prime q)] (a b : Fin n → ZMod q) (v : ZMod q),
    1 ≤ n → ∀ (y : Fin n → ZMod q) (z : Fin 3 → ZMod q),
      Function.Injective y → Function.Injective z → GridEqualities a b v y z →
        (∀ i, a i * b i = 0) ∧ (∀ i, a i - b i = 1) ∧
          (∀ i, a i * (a i - 1) = 0) ∧ (∑ i, (2 : ZMod q) ^ i.val * a i) = v
  natural_range : ∀ {q n : ℕ} [Fact (Nat.Prime q)] (a b : Fin n → ZMod q) (v : ℕ),
    1 ≤ n → ∀ (y : Fin n → ZMod q) (z : Fin 3 → ZMod q),
      Function.Injective y → Function.Injective z → v < q → 2 ^ n < q →
        GridEqualities a b (v : ZMod q) y z → v < 2 ^ n
  checked_soundness : ∀ {q n : ℕ} [Fact (Nat.Prime q)] (a b : Fin n → ZMod q) (v : ZMod q)
    (y : Fin n → ZMod q) (z : Fin 3 → ZMod q),
      verify_interpolation_grid a b v y z = .ok () → formal_t0 a b = formal_rhs v n
  nonvacuous : verify_interpolation_grid Regression.a4 (Regression.rightBits Regression.a4)
    5 (Regression.gridY 4) Regression.gridZ = .ok ()
  repeated_y_failure : verify_interpolation_grid (![2, 0] : Fin 2 → ZMod 101) ![0, 0] 2
    (fun _ => 1) Regression.gridZ = .error .repeatedY

theorem verification_suite : CryptoBulletproofsRangeInterpolationSuite where
  grid_identity := grid_equalities_imply_formal_identity
  field_range := grid_equalities_imply_field_range
  natural_range := grid_equalities_imply_natural_range
  checked_soundness := verify_grid_sound
  nonvacuous := Regression.honest_four
  repeated_y_failure := Regression.repeated_y_counterexample.2.2

end CryptoBulletproofsRangeInterpolation
