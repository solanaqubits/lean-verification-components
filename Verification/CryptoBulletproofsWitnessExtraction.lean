/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsInnerProduct
import Verification.CryptoBulletproofsRangeReduction
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Local algebraic extraction. Folded witnesses are inputs, not inferred from
recursive verifier acceptance. No independence assumption on generators is used. -/
namespace CryptoBulletproofsWitnessExtraction
open scoped BigOperators
open CryptoBulletproofsInnerProduct

section Interpolation
variable {F : Type} [Field F]

def lagrange (x₀ x₁ x₂ t : F) : F :=
  (t - x₁) * (t - x₂) / ((x₀ - x₁) * (x₀ - x₂))

theorem quadratic_interpolation (x₀ x₁ x₂ t a b c : F)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    lagrange x₀ x₁ x₂ t * (a + b * x₀ + c * x₀ ^ 2) + lagrange x₁ x₀ x₂ t * (a + b * x₁ + c *
    x₁ ^ 2) + lagrange x₂ x₀ x₁ t * (a + b * x₂ + c * x₂ ^ 2) = a + b * t + c * t ^ 2 := by
  unfold lagrange
  field_simp
  ring

def vandermonde_matrix (x : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F := Matrix.vandermonde x

theorem vandermonde_det_nonzero (x : Fin 3 → F) (h : Function.Injective x) :
    (vandermonde_matrix x).det ≠ 0 := by
  exact Matrix.det_vandermonde_ne_zero_iff.mpr h


theorem vandermonde_inverse (x : Fin 3 → F) (h : Function.Injective x) :
    vandermonde_matrix x * (vandermonde_matrix x)⁻¹ = 1 ∧
    (vandermonde_matrix x)⁻¹ * vandermonde_matrix x = 1 := by
  exact ⟨Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (vandermonde_det_nonzero x h)),
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (vandermonde_det_nonzero x h))⟩

/-- Executable Lagrange coefficient formula, in ascending degree order. -/
def interpolate_quad (x y : Fin 3 → F) : Fin 3 → F :=
  let d := fun i : Fin 3 => y i / ((x i - x (i + 1)) * (x i - x (i + 2)))
  ![∑ i, d i * x (i + 1) * x (i + 2),
    ∑ i, -(d i * (x (i + 1) + x (i + 2))), ∑ i, d i]

theorem polynomial_interpolation_quad (x : Fin 3 → F) (a b c : F)
    (h : Function.Injective x) :
    interpolate_quad x (fun i => a + b * x i + c * x i ^ 2) = ![a, b, c] := by
  have h01 := h.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := h.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := h.ne (show (1 : Fin 3) ≠ 2 by decide)
  ext i
  fin_cases i <;> simp [interpolate_quad, Fin.sum_univ_succ]
  all_goals field_simp; ring


/-- Explicit determinant, including its sign for ascending powers in rows. -/
theorem vandermonde_three_det (x : Fin 3 → F) :
    (vandermonde_matrix x).det = (x 1 - x 0) * (x 2 - x 0) * (x 2 - x 1) := by
  simp [vandermonde_matrix, Matrix.det_fin_three, Matrix.vandermonde]
  ring

theorem interpolate_quad_evaluates (x y : Fin 3 → F) (h : Function.Injective x) (i : Fin 3) :
    interpolate_quad x y 0 + interpolate_quad x y 1 * x i + interpolate_quad x y 2 * (x i) ^ 2
    = y i := by
  have h01 := h.ne (show (0 : Fin 3) ≠ 1 by decide)
  have h02 := h.ne (show (0 : Fin 3) ≠ 2 by decide)
  have h12 := h.ne (show (1 : Fin 3) ≠ 2 by decide)
  fin_cases i <;> simp [interpolate_quad, Fin.sum_univ_succ]
  all_goals field_simp; ring

/-- Agreement between the executable coefficient formula and matrix inversion. -/
theorem interpolate_eq_inverse (x y : Fin 3 → F) (h : Function.Injective x) :
    interpolate_quad x y = (vandermonde_matrix x)⁻¹.mulVec y := by
  have hv : (vandermonde_matrix x).mulVec (interpolate_quad x y) = y := by
    funext i
    simpa [vandermonde_matrix, Matrix.mulVec, dotProduct, Matrix.vandermonde,
      Fin.sum_univ_succ, mul_comm, add_assoc] using interpolate_quad_evaluates x y h i
  calc
    interpolate_quad x y = ((vandermonde_matrix x)⁻¹ * vandermonde_matrix x).mulVec
      (interpolate_quad x y) := by rw [(vandermonde_inverse x h).2, Matrix.one_mulVec]
    _ = (vandermonde_matrix x)⁻¹.mulVec y := by rw [← Matrix.mulVec_mulVec, hv]


variable {A : Type} [AddCommGroup A] [Module F A]

theorem quadratic_module_interpolation (x₀ x₁ x₂ t : F) (a b c : A)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂) :
    lagrange x₀ x₁ x₂ t • (a + x₀ • b + x₀ ^ 2 • c) + lagrange x₁ x₀ x₂ t • (a + x₁ • b + x₁ ^
    2 • c) + lagrange x₂ x₀ x₁ t • (a + x₂ • b + x₂ ^ 2 • c) = a + t • b + t ^ 2 • c := by
  have h0 := quadratic_interpolation x₀ x₁ x₂ t 1 0 0 h01 h02 h12
  have h1 := quadratic_interpolation x₀ x₁ x₂ t 0 1 0 h01 h02 h12
  have h2 := quadratic_interpolation x₀ x₁ x₂ t 0 0 1 h01 h02 h12
  simp at h0 h1 h2
  match_scalars <;> simp only [mul_one] <;> assumption

/-- The coefficient of degree one recovered from three group - valued evaluations. -/
theorem quadratic_module_linear_coeff (x₀ x₁ x₂ : F) (a b c : A)
    (h01 : x₀ ≠ x₁) (h02 : x₀ ≠ x₂) (h12 : x₁ ≠ x₂)
    (h0 : a + x₀ • b + x₀ ^ 2 • c = 0)
    (h1 : a + x₁ • b + x₁ ^ 2 • c = 0)
    (h2 : a + x₂ • b + x₂ ^ 2 • c = 0) : b = 0 := by
  have ident :
      (-(x₁ + x₂)/((x₀ - x₁) * (x₀ - x₂))) • (a + x₀ • b + x₀ ^ 2 • c) + (-(x₀ + x₂)/((x₁ - x₀)
    * (x₁ - x₂))) • (a + x₁ • b + x₁ ^ 2 • c) + (-(x₀ + x₁)/((x₂ - x₀) * (x₂ - x₁))) • (a + x₂
    • b + x₂ ^ 2 • c) = b := by
    match_scalars <;> field_simp <;> ring
  simpa only [h0, h1, h2, smul_zero, add_zero] using ident.symm
end Interpolation

section Extraction
variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]
variable {k : ℕ}

abbrev Coeff (q k : ℕ) := Vec (k + 1) (ZMod q) × Vec (k + 1) (ZMod q) × ZMod q

def evaluate (U : A) (G H : Vec (k + 1) A) (c : Coeff q k) : A :=
  multiscalar_mul c.1 G + multiscalar_mul c.2.1 H + c.2.2 • U

theorem evaluate_add (U : A) (G H : Vec (k + 1) A) (c d : Coeff q k) :
    evaluate U G H (c + d) = evaluate U G H c + evaluate U G H d := by
  simp [evaluate, multiscalar_mul, add_smul, Finset.sum_add_distrib]
  abel

theorem evaluate_smul (U : A) (G H : Vec (k + 1) A) (t : ZMod q) (c : Coeff q k) :
    evaluate U G H (t • c) = t • evaluate U G H c := by
  simp [evaluate, multiscalar_mul, smul_add, Finset.smul_sum, smul_smul]

@[simp] theorem evaluate_zero (U : A) (G H : Vec (k + 1) A) :
    evaluate U G H (0 : Coeff q k) = 0 := by simp [evaluate, multiscalar_mul]

def fold_coeff (u : (ZMod q)ˣ) (a b : Vec k (ZMod q)) : Coeff q k :=
  (join (fun i => a i * (u : ZMod q)⁻¹) (fun i => a i * u),
   join (fun i => b i * u) (fun i => b i * (u : ZMod q)⁻¹), dot_product a b)

theorem evaluate_fold (U : A) (G H : Vec (k + 1) A) (u : (ZMod q)ˣ)
    (a b : Vec k (ZMod q)) :
    evaluate U G H (fold_coeff u a b) =
      ipa_target U (fold_generators_G u G) (fold_generators_H u H) a b := by
  unfold evaluate fold_coeff
  dsimp only
  rw [multiscalar_join, multiscalar_join]
  simp only [ipa_target, multiscalar_mul,
    fold_generators_G, fold_generators_H, smul_add, smul_smul, Finset.sum_add_distrib,
    Units.val_inv_eq_inv_val]

def reconstruct_a (u v : (ZMod q)ˣ) (a b : Vec k (ZMod q)) : Vec (k + 1) (ZMod q) :=
  let l := fun i => ((u : ZMod q) * a i - (v : ZMod q) * b i) / ((u : ZMod q) ^ 2 - (v : ZMod
    q) ^ 2)
  join l (fun i => (u : ZMod q) * a i - (u : ZMod q) ^ 2 * l i)

def reconstruct_b (u v : (ZMod q)ˣ) (a b : Vec k (ZMod q)) : Vec (k + 1) (ZMod q) :=
  let r := fun i => ((u : ZMod q) * a i - (v : ZMod q) * b i) / ((u : ZMod q) ^ 2 - (v : ZMod
    q) ^ 2)
  join (fun i => (u : ZMod q) * a i - (u : ZMod q) ^ 2 * r i) r

theorem reconstruct_fold (u v : (ZMod q)ˣ) (a b c d : Vec k (ZMod q))
    (h : (u : ZMod q) ^ 2 ≠ (v : ZMod q) ^ 2) :
    fold_vector_a u (reconstruct_a u v a b) = a ∧
    fold_vector_a v (reconstruct_a u v a b) = b ∧
    fold_vector_b u (reconstruct_b u v c d) = c ∧
    fold_vector_b v (reconstruct_b u v c d) = d := by
  have hu := Units.ne_zero u
  have hv := Units.ne_zero v
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i
  all_goals
    simp only [reconstruct_a, reconstruct_b, fold_vector_a, fold_vector_b,
      split_lo_join, split_hi_join, Units.val_inv_eq_inv_val]
    field_simp
    ring


omit [Fact q.Prime] in
@[simp] theorem join_lo (l h : Vec k (ZMod q)) (j : Fin (2 ^ k)) : join l h (loIndex j) = l j :=
  congrFun (split_lo_join l h) j

omit [Fact q.Prime] in
@[simp] theorem join_hi (l h : Vec k (ZMod q)) (j : Fin (2 ^ k)) : join l h (hiIndex j) = h j :=
  congrFun (split_hi_join l h) j

/-- A statement and the two prover messages fixed before the challenge. -/
structure Prefix (q : ℕ) (A : Type) (k : ℕ) where
  U : A
  G : Vec (k + 1) A
  H : Vec (k + 1) A
  P : A
  messages : RoundMessages A
  deriving DecidableEq

/-- A local folded witness, not just an unexamined recursive transcript. -/
structure IPAExtractionTranscript (q : ℕ) (A : Type) (k : ℕ) where
  common : Prefix q A k
  challenge : ZMod q
  a : Vec k (ZMod q)
  b : Vec k (ZMod q)

def Accepts (p : Prefix q A k) (u : (ZMod q)ˣ) (a b : Vec k (ZMod q)) : Prop :=
  update_target u p.messages p.P =
    ipa_target p.U (fold_generators_G u p.G) (fold_generators_H u p.H) a b

instance [DecidableEq A] (p : Prefix q A k) (u : (ZMod q)ˣ) (a b : Vec k (ZMod q)) :
    Decidable (Accepts p u a b) := inferInstanceAs (Decidable (_ = _))

def residual (u : (ZMod q)ˣ) (a b : Vec k (ZMod q))
    (wa wb : Vec (k + 1) (ZMod q)) : Coeff q k :=
  fold_coeff u a b - fold_coeff u (fold_vector_a u wa) (fold_vector_b u wb)

theorem evaluate_sub (U : A) (G H : Vec (k + 1) A) (c d : Coeff q k) :
    evaluate U G H (c - d) = evaluate U G H c - evaluate U G H d := by
  simp [evaluate, multiscalar_mul, sub_smul, Finset.sum_sub_distrib]
  abel

theorem residual_evaluation (p : Prefix q A k) (u : (ZMod q)ˣ)
    (a b : Vec k (ZMod q)) (wa wb : Vec (k + 1) (ZMod q)) (h : Accepts p u a b) :
    (u : ZMod q) ^ 2 • evaluate p.U p.G p.H (residual u a b wa wb) =
      (p.messages.R - (round_messages p.U p.G p.H wa wb).R) + (u : ZMod q) ^ 2 • (p.P -
    ipa_target p.U p.G p.H wa wb) + ((u : ZMod q) ^ 2) ^ 2 • (p.messages.L - (round_messages
    p.U p.G p.H wa wb).L) := by
  rw [residual, evaluate_sub, evaluate_fold, evaluate_fold, ← h, ← ipa_round_invariant]
  have hu := Units.ne_zero u
  simp only [update_target, Units.val_inv_eq_inv_val]
  match_scalars <;> field_simp

/-- A null combination of four evaluations of a quadratic. -/
def relation_coeff (u : Fin 4 → (ZMod q)ˣ) (a b : Fin 4 → Vec k (ZMod q)) : Coeff q k :=
  let wa := reconstruct_a (u 0) (u 1) (a 0) (a 1)
  let wb := reconstruct_b (u 0) (u 1) (b 0) (b 1)
  let s := fun i => (u i : ZMod q) ^ 2
  (lagrange (s 2) (s 0) (s 1) (s 3) * s 2) • residual (u 2) (a 2) (b 2) wa wb -
    s 3 • residual (u 3) (a 3) (b 3) wa wb

theorem relation_annihilates (p : Prefix q A k) (u : Fin 4 → (ZMod q)ˣ)
    (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (ha : ∀ i, Accepts p (u i) (a i) (b i)) :
    evaluate p.U p.G p.H (relation_coeff u a b) = 0 := by
  have h01 := hd.ne (show (0 : Fin 4) ≠ 1 by decide)
  have h02 := hd.ne (show (0 : Fin 4) ≠ 2 by decide)
  have h12 := hd.ne (show (1 : Fin 4) ≠ 2 by decide)
  let wa := reconstruct_a (u 0) (u 1) (a 0) (a 1)
  let wb := reconstruct_b (u 0) (u 1) (b 0) (b 1)
  obtain ⟨e0, e1, f0, f1⟩ := reconstruct_fold (u 0) (u 1) (a 0) (a 1) (b 0) (b 1) h01
  have r0 : residual (u 0) (a 0) (b 0) wa wb = 0 := by simp [residual, wa, wb, e0, f0]
  have r1 : residual (u 1) (a 1) (b 1) wa wb = 0 := by simp [residual, wa, wb, e1, f1]
  have hi := quadratic_module_interpolation
    ((u 0 : ZMod q) ^ 2) ((u 1 : ZMod q) ^ 2) ((u 2 : ZMod q) ^ 2) ((u 3 : ZMod q) ^ 2)
    (p.messages.R - (round_messages p.U p.G p.H wa wb).R)
    (p.P - ipa_target p.U p.G p.H wa wb)
    (p.messages.L - (round_messages p.U p.G p.H wa wb).L) h01 h02 h12
  rw [← residual_evaluation p (u 0) (a 0) (b 0) wa wb (ha 0),
    ← residual_evaluation p (u 1) (a 1) (b 1) wa wb (ha 1),
    ← residual_evaluation p (u 2) (a 2) (b 2) wa wb (ha 2),
    ← residual_evaluation p (u 3) (a 3) (b 3) wa wb (ha 3), r0, r1] at hi
  simp only [evaluate_zero, smul_zero, zero_add, smul_smul] at hi
  unfold relation_coeff
  rw [evaluate_sub, evaluate_smul, evaluate_smul]
  exact sub_eq_zero.mpr hi

private theorem pair_recovery (u v : (ZMod q)ˣ) (c d a b : ZMod q)
    (hc : c ≠ 0) (hd : d ≠ 0) (h : (u : ZMod q) ^ 2 ≠ (v : ZMod q) ^ 2)
    (e : c * (a * (u : ZMod q)⁻¹) - d * (b * (v : ZMod q)⁻¹) = 0)
    (f : c * (a * (u : ZMod q)) - d * (b * (v : ZMod q)) = 0) : a = 0 ∧ b = 0 := by
  have hu := Units.ne_zero u
  have hv := Units.ne_zero v
  have e' : c * a * (v : ZMod q) - d * b * (u : ZMod q) = 0 := by
    have := congrArg (fun z => z * (u : ZMod q) * (v : ZMod q)) e
    field_simp at this
    linear_combination this
  have hb : d * b * ((u : ZMod q) ^ 2 - (v : ZMod q) ^ 2) = 0 := by
    linear_combination (v : ZMod q) * f - (u : ZMod q) * e'
  have bz : b = 0 := (mul_eq_zero.mp ((mul_eq_zero.mp hb).resolve_right (sub_ne_zero.mpr
    h))).resolve_left hd
  refine ⟨?_, bz⟩
  rw [bz] at f
  simp only [zero_mul, mul_zero, sub_zero] at f
  exact (mul_eq_zero.mp ((mul_eq_zero.mp f).resolve_left hc)).resolve_right hu

/-- Zero relation coefficients force the remaining responses to match the candidate. -/
theorem zero_relation_recovers (u : Fin 4 → (ZMod q)ˣ) (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (hz : relation_coeff u a b = 0) :
    ∀ i, fold_vector_a (u i) (reconstruct_a (u 0) (u 1) (a 0) (a 1)) = a i ∧
      fold_vector_b (u i) (reconstruct_b (u 0) (u 1) (b 0) (b 1)) = b i := by
  let wa := reconstruct_a (u 0) (u 1) (a 0) (a 1)
  let wb := reconstruct_b (u 0) (u 1) (b 0) (b 1)
  let s := fun i => (u i : ZMod q) ^ 2
  let c := lagrange (s 2) (s 0) (s 1) (s 3) * s 2
  let d := s 3
  have h01 := hd.ne (show (0 : Fin 4) ≠ 1 by decide)
  have h23 := hd.ne (show (2 : Fin 4) ≠ 3 by decide)
  have hc : c ≠ 0 := by
    apply mul_ne_zero
    · apply div_ne_zero
      · exact mul_ne_zero (sub_ne_zero.mpr (hd.ne (by decide))) (sub_ne_zero.mpr (hd.ne (by
    decide)))
      · exact mul_ne_zero (sub_ne_zero.mpr (hd.ne (by decide))) (sub_ne_zero.mpr (hd.ne (by
    decide)))
    · exact pow_ne_zero _ (Units.ne_zero (u 2))
  have hdd : d ≠ 0 := pow_ne_zero _ (Units.ne_zero (u 3))
  have eqs (j : Fin (2 ^ k)) :
      a 2 j - fold_vector_a (u 2) wa j = 0 ∧ a 3 j - fold_vector_a (u 3) wa j = 0 ∧
      b 2 j - fold_vector_b (u 2) wb j = 0 ∧ b 3 j - fold_vector_b (u 3) wb j = 0 := by
    have g0 := congrArg (fun z : Coeff q k => split_lo z.1 j) hz
    have g1 := congrArg (fun z : Coeff q k => split_hi z.1 j) hz
    have h0 := congrArg (fun z : Coeff q k => split_lo z.2.1 j) hz
    have h1 := congrArg (fun z : Coeff q k => split_hi z.2.1 j) hz
    simp only [relation_coeff, residual, fold_coeff, Prod.fst_sub, Prod.snd_sub,
      Prod.smul_fst, Prod.smul_snd, split_lo, split_hi, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, join_lo, join_hi] at g0 g1 h0 h1
    change c * ((a 2 j) * (u 2 : ZMod q)⁻¹ - fold_vector_a (u 2) wa j * (u 2 : ZMod q)⁻¹) -
      d * ((a 3 j) * (u 3 : ZMod q)⁻¹ - fold_vector_a (u 3) wa j * (u 3 : ZMod q)⁻¹) = 0 at g0
    change c * ((a 2 j) * (u 2 : ZMod q) - fold_vector_a (u 2) wa j * (u 2 : ZMod q)) -
      d * ((a 3 j) * (u 3 : ZMod q) - fold_vector_a (u 3) wa j * (u 3 : ZMod q)) = 0 at g1
    change c * ((b 2 j) * (u 2 : ZMod q) - fold_vector_b (u 2) wb j * (u 2 : ZMod q)) -
      d * ((b 3 j) * (u 3 : ZMod q) - fold_vector_b (u 3) wb j * (u 3 : ZMod q)) = 0 at h0
    change c * ((b 2 j) * (u 2 : ZMod q)⁻¹ - fold_vector_b (u 2) wb j * (u 2 : ZMod q)⁻¹) -
      d * ((b 3 j) * (u 3 : ZMod q)⁻¹ - fold_vector_b (u 3) wb j * (u 3 : ZMod q)⁻¹) = 0 at h1
    simp only [← sub_mul] at g0 g1 h0 h1
    obtain ⟨ag, ah⟩ := pair_recovery (u 2) (u 3) c d _ _ hc hdd h23 g0 g1
    obtain ⟨bg, bh⟩ := pair_recovery (u 2) (u 3) c d _ _ hc hdd h23 h1 h0
    exact ⟨ag, ah, bg, bh⟩
  obtain ⟨e0, e1, f0, f1⟩ := reconstruct_fold (u 0) (u 1) (a 0) (a 1) (b 0) (b 1) h01
  intro i
  fin_cases i
  · exact ⟨e0, f0⟩
  · exact ⟨e1, f1⟩
  · exact ⟨funext (fun j => (sub_eq_zero.mp (eqs j).1).symm),
      funext (fun j => (sub_eq_zero.mp (eqs j).2.2.1).symm)⟩
  · exact ⟨funext (fun j => (sub_eq_zero.mp (eqs j).2.1).symm),
      funext (fun j => (sub_eq_zero.mp (eqs j).2.2.2).symm)⟩

theorem zero_relation_witness (p : Prefix q A k) (u : Fin 4 → (ZMod q)ˣ)
    (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (ha : ∀ i, Accepts p (u i) (a i) (b i)) (hz : relation_coeff u a b = 0) :
    p.P = ipa_target p.U p.G p.H (reconstruct_a (u 0) (u 1) (a 0) (a 1))
      (reconstruct_b (u 0) (u 1) (b 0) (b 1)) := by
  let wa := reconstruct_a (u 0) (u 1) (a 0) (a 1)
  let wb := reconstruct_b (u 0) (u 1) (b 0) (b 1)
  have hf := zero_relation_recovers u a b hd hz
  have he (i : Fin 4) := residual_evaluation p (u i) (a i) (b i) wa wb (ha i)
  have hr (i : Fin 4) : residual (u i) (a i) (b i) wa wb = 0 := by
    simp [residual, wa, wb, (hf i).1, (hf i).2]
  simp only [hr, evaluate_zero, smul_zero] at he
  exact sub_eq_zero.mp (quadratic_module_linear_coeff _ _ _ _ _ _
    (hd.ne (by decide : (0 : Fin 4) ≠ 1)) (hd.ne (by decide : (0 : Fin 4) ≠ 2))
    (hd.ne (by decide : (1 : Fin 4) ≠ 2)) (he 0).symm (he 1).symm (he 2).symm)

/-- Constructive local dichotomy; the relation mentions only original G, H, U. -/
theorem ipa_extraction_dichotomy (p : Prefix q A k) (u : Fin 4 → (ZMod q)ˣ)
    (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (ha : ∀ i, Accepts p (u i) (a i) (b i)) :
    p.P = ipa_target p.U p.G p.H (reconstruct_a (u 0) (u 1) (a 0) (a 1))
      (reconstruct_b (u 0) (u 1) (b 0) (b 1)) ∨
    (relation_coeff u a b ≠ 0 ∧ evaluate p.U p.G p.H (relation_coeff u a b) = 0) := by
  by_cases hz : relation_coeff u a b = 0
  · exact Or.inl (zero_relation_witness p u a b hd ha hz)
  · exact Or.inr ⟨hz, relation_annihilates p u a b hd ha⟩


inductive ExtractionResult (q k : ℕ) where
  | witness (a b : Vec (k + 1) (ZMod q))
  | relation (coefficients : Coeff q k)
  deriving DecidableEq

inductive ExtractionError where
  | prefixMismatch | zeroChallenge | repeatedSquare | invalidResponse
  deriving DecidableEq, Repr

def extract_local (u : Fin 4 → (ZMod q)ˣ) (a b : Fin 4 → Vec k (ZMod q)) : ExtractionResult q k :=
  if relation_coeff u a b = 0 then
    .witness (reconstruct_a (u 0) (u 1) (a 0) (a 1)) (reconstruct_b (u 0) (u 1) (b 0) (b 1))
  else .relation (relation_coeff u a b)

def ResultValid (p : Prefix q A k) : ExtractionResult q k → Prop
  | .witness a b => p.P = ipa_target p.U p.G p.H a b
  | .relation c => c ≠ 0 ∧ evaluate p.U p.G p.H c = 0

theorem extract_local_correct (p : Prefix q A k) (u : Fin 4 → (ZMod q)ˣ)
    (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (ha : ∀ i, Accepts p (u i) (a i) (b i)) : ResultValid p (extract_local u a b) := by
  unfold extract_local
  split_ifs with hz
  · exact zero_relation_witness p u a b hd ha hz
  · exact ⟨hz, relation_annihilates p u a b hd ha⟩

/-- The expected prefix is provided separately from the four untrusted inputs. -/
def extract_ipa_witness [DecidableEq A] (expected : Prefix q A k)
    (t : Fin 4 → IPAExtractionTranscript q A k) : Except ExtractionError (ExtractionResult q k) :=
  if ∀ i, (t i).common = expected then
    if hn : ∀ i, (t i).challenge ≠ 0 then
      let u := fun i => Units.mk0 (t i).challenge (hn i)
      if Function.Injective (fun i => (t i).challenge ^ 2) then
        if ∀ i, Accepts expected (u i) (t i).a (t i).b then
          .ok (extract_local u (fun i => (t i).a) (fun i => (t i).b))
        else .error .invalidResponse
      else .error .repeatedSquare
    else .error .zeroChallenge
  else .error .prefixMismatch

theorem extract_unit_transcripts [DecidableEq A] (p : Prefix q A k)
    (u : Fin 4 → (ZMod q)ˣ) (a b : Fin 4 → Vec k (ZMod q))
    (hd : Function.Injective (fun i => (u i : ZMod q) ^ 2))
    (ha : ∀ i, Accepts p (u i) (a i) (b i)) :
    extract_ipa_witness p (fun i => ⟨p, u i, a i, b i⟩) = .ok (extract_local u a b) := by
  have hn : ∀ i, (u i : ZMod q) ≠ 0 := fun i => Units.ne_zero (u i)
  simp [extract_ipa_witness, hn, Units.mk0_val, hd, ha]

theorem extract_ipa_witness_sound [DecidableEq A] (p : Prefix q A k)
    (t : Fin 4 → IPAExtractionTranscript q A k) (r : ExtractionResult q k)
    (h : extract_ipa_witness p t = .ok r) : ResultValid p r := by
  unfold extract_ipa_witness at h
  split at h
  · split at h
    · dsimp only at h
      split at h
      · split at h
        · cases h
          apply extract_local_correct p
          all_goals assumption
        · contradiction
      · contradiction
    · contradiction
  · contradiction

theorem extraction_failure_on_symmetric_challenges [DecidableEq A] (p : Prefix q A k)
    (t : Fin 4 → IPAExtractionTranscript q A k)
    (hp : ∀ i, (t i).common = p) (hn : ∀ i, (t i).challenge ≠ 0)
    (hs : (t 1).challenge = -(t 0).challenge) :
    extract_ipa_witness p t = .error .repeatedSquare := by
  have hd : ¬Function.Injective (fun i => (t i).challenge ^ 2) := by
    intro hh
    have e : (t 0).challenge ^ 2 = (t 1).challenge ^ 2 := by rw [hs, neg_sq]
    exact (by decide : (0 : Fin 4) ≠ 1) (hh e)
  simp [extract_ipa_witness, hp, hn, hd]

/-- Scalar coefficient recovery for module 159's actual l/r curves. -/
theorem range_polynomial_interpolation {n : ℕ} (a b s t : Fin n → ZMod q)
    (y z : ZMod q) (xs : Fin 3 → ZMod q) (h : Function.Injective xs) :
    interpolate_quad xs (fun i => CryptoBulletproofsRangeReduction.dot
      (CryptoBulletproofsRangeReduction.l_poly a s z (xs i))
      (CryptoBulletproofsRangeReduction.r_poly b t y z (xs i))) =
    ![CryptoBulletproofsRangeReduction.t0 a b y z,
      CryptoBulletproofsRangeReduction.t1 a b s t y z,
      CryptoBulletproofsRangeReduction.t2 s t y] := by
  simp only [CryptoBulletproofsRangeReduction.poly_inner_product_eq]
  exact polynomial_interpolation_quad xs _ _ _ h



theorem reconstruct_honest_join (u v : (ZMod q)ˣ) (al ar bl br : Vec k (ZMod q))
    (hd : (u : ZMod q) ^ 2 ≠ (v : ZMod q) ^ 2) :
    reconstruct_a u v (fold_vector_a u (join al ar)) (fold_vector_a v (join al ar)) = join al ar ∧
    reconstruct_b u v (fold_vector_b u (join bl br)) (fold_vector_b v (join bl br)) = join bl
    br := by
  have hu := Units.ne_zero u
  have hv := Units.ne_zero v
  simp only [reconstruct_a, reconstruct_b, fold_vector_a, fold_vector_b,
    split_lo_join, split_hi_join, Units.val_inv_eq_inv_val]
  constructor
  all_goals
    congr 1 <;> funext i <;> field_simp <;> ring

theorem extract_local_honest (u : Fin 4 → (ZMod q)ˣ)
    (al ar bl br : Vec k (ZMod q)) (hd : (u 0 : ZMod q) ^ 2 ≠ (u 1 : ZMod q) ^ 2) :
    extract_local u (fun i => fold_vector_a (u i) (join al ar))
      (fun i => fold_vector_b (u i) (join bl br)) = .witness (join al ar) (join bl br) := by
  obtain ⟨ha, hb⟩ := reconstruct_honest_join (u 0) (u 1) al ar bl br hd
  have hz : relation_coeff u (fun i => fold_vector_a (u i) (join al ar))
      (fun i => fold_vector_b (u i) (join bl br)) = 0 := by
    simp [relation_coeff, ha, hb, residual]
  simp [extract_local, hz, ha, hb]

/-- In the last recursion step, the folded witness check is the actual IPA verifier. -/
theorem accepts_last_step_iff_verifier [DecidableEq A] (p : Prefix q A 0)
    (u : (ZMod q)ˣ) (a b : Vec 0 (ZMod q)) :
    Accepts p u a b ↔ verifier p.U p.G p.H p.P (fun _ => u)
      (⟨fun _ => p.messages, a 0, b 0⟩ : IPATranscript q A 1) = true := by
  change Accepts p u a b ↔ decide (update_target u p.messages p.P =
    a 0 • fold_generators_G u p.G 0 + b 0 • fold_generators_H u p.H 0 + (a 0 * b 0) • p.U) = true
  rw [decide_eq_true_eq]
  simp [Accepts, ipa_target, multiscalar_mul, dot_product]


end Extraction

namespace Examples
instance : Fact (Nat.Prime 101) := ⟨by decide⟩
def a : Vec 1 (ZMod 101) := join (fun _ => 2) (fun _ => 5)
def b : Vec 1 (ZMod 101) := join (fun _ => 7) (fun _ => 9)
def p : Prefix 101 (ZMod 101) 0 :=
  ⟨11, ![2, 3], ![5, 7], ipa_target 11 ![2, 3] ![5, 7] a b,
    round_messages 11 ![2, 3] ![5, 7] a b⟩
def units : Fin 4 → (ZMod 101)ˣ :=
  ![Units.mk0 1 (by decide), Units.mk0 2 (by decide),
    Units.mk0 3 (by decide), Units.mk0 4 (by decide)]
def honest : Fin 4 → IPAExtractionTranscript 101 (ZMod 101) 0 :=
  fun i => ⟨p, units i, fold_vector_a (units i) a, fold_vector_b (units i) b⟩
def inconsistent : Fin 4 → IPAExtractionTranscript 101 (ZMod 101) 0 :=
  fun i => ⟨p, units i, fun _ => 1, fun _ => (![72, 37, 60, 26] : Fin 4 → ZMod 101) i⟩

theorem non_vacuous_extraction_success :
    extract_ipa_witness p honest = .ok (.witness a b) := by
  rw [show honest = (fun i => ⟨p, units i, fold_vector_a (units i) a,
    fold_vector_b (units i) b⟩) from rfl]
  rw [extract_unit_transcripts p units _ _ (by decide)]
  · congr 1
    exact extract_local_honest units (fun _ => 2) (fun _ => 5) (fun _ => 7) (fun _ => 9) (by decide)
  · intro i
    unfold Accepts
    dsimp only [p]
    exact ipa_round_invariant (q := 101) (A := ZMod 101) (k := 0)
      11 ![2, 3] ![5, 7] a b (units i)


set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000 in
-- Kernel reduction of four concrete group equations and their relation coefficients.
theorem non_vacuous_relation :
    ∃ c, extract_ipa_witness p inconsistent = .ok (.relation c) ∧ c ≠ 0 ∧
      evaluate p.U p.G p.H c = 0 := by
  let c : Coeff 101 0 := relation_coeff units (fun _ _ => 1) (fun i _ => (![72, 37, 60, 26] :
    Fin 4 → ZMod 101) i)
  refine ⟨c, ?_, ?_, ?_⟩ <;> decide +kernel
end Examples

structure CryptoBulletproofsWitnessExtractionSuite : Prop where
  determinant : ∀ (q : ℕ) [Fact q.Prime] (x : Fin 3 → ZMod q), Function.Injective x →
    (vandermonde_matrix x).det ≠ 0
  interpolation : ∀ (q : ℕ) [Fact q.Prime] (x : Fin 3 → ZMod q) (a b c : ZMod q),
    Function.Injective x → interpolate_quad x (fun i => a + b * x i + c * (x i) ^ 2) = ![a, b, c]
  local_extraction : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    (k : ℕ) (p : Prefix q A k) (u : Fin 4 → (ZMod q)ˣ) (a b : Fin 4 → Vec k (ZMod q)),
    Function.Injective (fun i => (u i : ZMod q) ^ 2) → (∀ i, Accepts p (u i) (a i) (b i)) →
    ResultValid p (extract_local u a b)
  checked_sound : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A] [Module (ZMod q) A]
    [DecidableEq A] (k : ℕ) (p : Prefix q A k) (t : Fin 4 → IPAExtractionTranscript q A k)
    (r : ExtractionResult q k), extract_ipa_witness p t = .ok r → ResultValid p r
  honest_example : extract_ipa_witness Examples.p Examples.honest =
    .ok (.witness Examples.a Examples.b)
  relation_example : ∃ c, extract_ipa_witness Examples.p Examples.inconsistent = .ok (.relation c) ∧
    c ≠ 0 ∧ evaluate Examples.p.U Examples.p.G Examples.p.H c = 0

theorem verification_suite : CryptoBulletproofsWitnessExtractionSuite where
  determinant := fun _ _ => vandermonde_det_nonzero
  interpolation := fun _ _ => polynomial_interpolation_quad
  local_extraction := fun _ _ _ _ _ _ => extract_local_correct
  checked_sound := fun _ _ _ _ _ _ _ => extract_ipa_witness_sound
  honest_example := Examples.non_vacuous_extraction_success
  relation_example := Examples.non_vacuous_relation

end CryptoBulletproofsWitnessExtraction

