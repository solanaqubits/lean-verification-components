/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMNaimarkDilation
import Verification.QuantumPOVMInformationallyComplete
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Complex.Hadamard
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Finite POVM entropic uncertainty, in bits

The general pure-state inequality follows from a finite exponential family and
Hadamard's three-lines theorem. A Naimark compression controls the phase boundary;
Cauchy--Schwarz and the maximum square-root overlap control the other boundary.
Mixed states follow from spectral decomposition and finite concavity.
The overlap is the operator norm, not its square. No informational-completeness
or noncommutativity assumption is used. Exact real analysis is noncomputable.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation
namespace QuantumPOVMInformationEntropy

/-- The nonnegative-domain extension used by the entropy API. -/
def xlogx (x : ℝ) : ℝ := if x ≤ 0 then 0 else x * Real.log x

theorem xlogx_of_nonneg {x : ℝ} (hx : 0 ≤ x) : xlogx x = x * Real.log x := by
  by_cases h : x ≤ 0
  · have : x = 0 := le_antisymm h hx
    simp [this, xlogx]
  · simp [xlogx, h]

@[simp] theorem xlogx_zero : xlogx 0 = 0 := by simp [xlogx]

def shannon_entropy_bits {ι : Type*} [Fintype ι] (p : ι → ℝ) : ℝ :=
  -(∑ i, xlogx (p i)) / Real.log 2

def IsDistribution {ι : Type*} [Fintype ι] (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

theorem entropy_eq_negMulLog {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    shannon_entropy_bits p = (∑ i, Real.negMulLog (p i)) / Real.log 2 := by
  simp only [shannon_entropy_bits, xlogx_of_nonneg (hp _), Real.negMulLog, neg_mul,
    Finset.sum_neg_distrib]

theorem shannon_entropy_nonneg {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : IsDistribution p) : 0 ≤ shannon_entropy_bits p := by
  rw [entropy_eq_negMulLog p hp.1]
  apply div_nonneg _ (le_of_lt (Real.log_pos (by norm_num)))
  apply Finset.sum_nonneg
  intro i _
  apply Real.negMulLog_nonneg (hp.1 i)
  calc p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => hp.1 j) (Finset.mem_univ i)
       _ = 1 := hp.2

theorem shannon_entropy_concave {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * shannon_entropy_bits p + b * shannon_entropy_bits q ≤
      shannon_entropy_bits (fun i => a * p i + b * q i) := by
  rw [entropy_eq_negMulLog p hp, entropy_eq_negMulLog q hq,
    entropy_eq_negMulLog _ (fun i => add_nonneg (mul_nonneg ha (hp i)) (mul_nonneg hb (hq i)))]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Real.concaveOn_negMulLog.2 (hp i) (hq i) ha hb hab

/-- Bits, rather than natural logarithm units. -/
def uncertainty_bound (c : ℝ) : ℝ := -2 * (Real.log c / Real.log 2)

theorem bound_strictly_positive {c : ℝ} (hc : 0 < c) (h1 : c < 1) :
    0 < uncertainty_bound c := by
  have hlog : Real.log c < 0 := Real.log_neg hc h1
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  exact mul_pos_of_neg_of_neg (by norm_num) (div_neg_of_neg_of_pos hlog htwo)

theorem bound_monotone_in_c {c₁ c₂ : ℝ} (h1 : 0 < c₁) (h12 : c₁ ≤ c₂) :
    uncertainty_bound c₂ ≤ uncertainty_bound c₁ := by
  apply mul_le_mul_of_nonpos_left _ (by norm_num : (-2 : ℝ) ≤ 0)
  exact div_le_div_of_nonneg_right (Real.log_le_log h1 h12)
    (le_of_lt (Real.log_pos (by norm_num)))

/-- Squared-overlap convention used in the review. -/
theorem squared_overlap_convention (c : ℝ) :
    -(Real.log (c ^ 2) / Real.log 2) = uncertainty_bound c := by
  rw [Real.log_pow]
  unfold uncertainty_bound
  ring

def prob_dist {d m : ℕ} (E : FinitePOVM d m) (ρ : Q d) (j : Fin m) : ℝ :=
  (Matrix.trace (ρ * E.effects j)).re

theorem prob_dist_isDistribution {d m : ℕ} (E : FinitePOVM d m) (ρ : Q d)
    (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) : IsDistribution (prob_dist E ρ) := by
  refine ⟨fun j => QuantumPOVMInformationallyComplete.density_probability_nonneg E ρ hρ.1 j, ?_⟩
  simp only [prob_dist, ← Complex.re_sum, ← Matrix.trace_sum, ← Finset.mul_sum,
    E.completeness, Matrix.mul_one, hρ.2, Complex.one_re]

/-- The CLM acts on EuclideanSpace, so its norm is the singular-value operator norm. -/
def matrix_op_norm {d : ℕ} (A : Q d) : ℝ := ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) A‖

def c_overlap {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n) : ℝ :=
  (((Finset.univ : Finset (Fin m × Fin n)).sup
    (fun jk => (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (sqrt_effects E jk.1 * sqrt_effects
          F jk.2)‖₊ : NNReal)) : NNReal) : ℝ)

open scoped Matrix.Norms.L2Operator

theorem matrix_op_norm_eq {d : ℕ} (A : Q d) : matrix_op_norm A = ‖A‖ := rfl

theorem effect_le_one {d m : ℕ} (E : FinitePOVM d m) (j : Fin m) : E.effects j ≤ 1 := by
  rw [← E.completeness]
  exact Finset.single_le_sum (fun i _ => (E.pos_semidef i).nonneg) (Finset.mem_univ j)

theorem sqrt_effect_norm_le_one {d m : ℕ} (E : FinitePOVM d m) (j : Fin m) :
    ‖sqrt_effects E j‖ ≤ 1 := by
  have h := (CStarAlgebra.norm_le_one_iff_of_nonneg (E.effects j)
    (E.pos_semidef j).nonneg).mpr (effect_le_one E j)
  have hs := Matrix.l2_opNorm_conjTranspose_mul_self (sqrt_effects E j)
  rw [sqrt_hermitian, sqrt_square] at hs
  nlinarith [norm_nonneg (sqrt_effects E j)]

theorem entry_norm_le_overlap {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (j : Fin m) (k : Fin n) : ‖sqrt_effects E j * sqrt_effects F k‖ ≤ c_overlap E F := by
  change (‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (sqrt_effects E j * sqrt_effects F k)‖₊ :
        ℝ) ≤ _
  unfold c_overlap
  exact_mod_cast (Finset.le_sup (f := fun jk : Fin m × Fin n =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (sqrt_effects E jk.1 * sqrt_effects F jk.2)‖₊)
    (Finset.mem_univ (j,k)))

theorem overlap_le_one {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n) :
    c_overlap E F ≤ 1 := by
  change ((Finset.univ.sup (fun jk : Fin m × Fin n =>
    ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (sqrt_effects E jk.1 * sqrt_effects F jk.2)‖₊)
          : NNReal) : ℝ) ≤ 1
  norm_cast
  apply Finset.sup_le
  intro jk _
  change ‖sqrt_effects E jk.1 * sqrt_effects F jk.2‖₊ ≤ 1
  rw [← NNReal.coe_le_coe]
  exact (norm_mul_le _ _).trans (by
    simpa using mul_le_mul (sqrt_effect_norm_le_one E jk.1) (sqrt_effect_norm_le_one F jk.2)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1))

theorem povm_overlap_bounds {d m n : ℕ} [NeZero d]
    (E : FinitePOVM d m) (F : FinitePOVM d n) : 0 < c_overlap E F ∧ c_overlap E F ≤ 1 := by
  refine ⟨?_, overlap_le_one E F⟩
  by_contra h
  have hz : ∀ j k, sqrt_effects E j * sqrt_effects F k = 0 := by
    intro j k
    exact norm_eq_zero.mp (le_antisymm ((entry_norm_le_overlap E F j k).trans (le_of_not_gt h))
      (norm_nonneg _))
  have hef : ∀ j k, E.effects j * F.effects k = 0 := by
    intro j k
    rw [← sqrt_square E j, ← sqrt_square F k]
    calc (sqrt_effects E j * sqrt_effects E j) * (sqrt_effects F k * sqrt_effects F k) =
        sqrt_effects E j * (sqrt_effects E j * sqrt_effects F k) * sqrt_effects F k := by
          simp only [Matrix.mul_assoc]
         _ = 0 := by rw [hz, Matrix.mul_zero, Matrix.zero_mul]
  have hzero : (1 : Q d) = 0 := by
    calc (1 : Q d) = (∑ j, E.effects j) * (∑ k, F.effects k) := by
           rw [E.completeness, F.completeness, Matrix.one_mul]
         _ = 0 := by simp only [Finset.sum_mul, Finset.mul_sum, hef, Finset.sum_const_zero]
  exact one_ne_zero hzero

/-- The finite analytic family used for the entropy interpolation argument. -/
def exponential_sum {ι : Type*} [Fintype ι] (w : ι → ℂ) (a : ι → ℝ) (z : ℂ) : ℂ :=
  ∑ i, w i * Complex.exp (z * (a i : ℂ))

theorem exponential_sum_differentiable {ι : Type*} [Fintype ι] (w : ι → ℂ) (a : ι → ℝ) :
    Differentiable ℂ (exponential_sum w a) := by
  unfold exponential_sum
  fun_prop

theorem exponential_sum_bounded {ι : Type*} [Fintype ι] (w : ι → ℂ) (a : ι → ℝ) :
    BddAbove ((norm ∘ exponential_sum w a) ''
      Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
  refine ⟨∑ i, ‖w i‖ * Real.exp |a i|, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖∑ i, w i * Complex.exp (z * (a i : ℂ))‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have hz0 : 0 ≤ z.re := hz.1
  have hz1 : z.re ≤ 1 := hz.2
  calc z.re * a i ≤ z.re * |a i| := mul_le_mul_of_nonneg_left (le_abs_self _) hz0
       _ ≤ |a i| := by nlinarith [abs_nonneg (a i)]

/-- A right boundary maximum bounds the directional derivative of a real function. -/
theorem right_derivative_nonpos {f : ℝ → ℝ} {f' : ℝ}
    (hd : HasDerivAt f f' 0) (h : ∀ t ∈ Set.Icc (0 : ℝ) 1, f t ≤ f 0) : f' ≤ 0 := by
  have hm : IsLocalMaxOn f (Set.Icc (0 : ℝ) 1) 0 :=
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => h t ht)
  have ht : (1 : ℝ) ∈ posTangentConeAt (Set.Icc (0 : ℝ) 1) 0 := by
    rw [one_mem_posTangentConeAt_iff_mem_closure]
    have heq : Set.Ioi (0 : ℝ) ∩ Set.Icc 0 1 = Set.Ioc 0 1 := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, h.1.le, h.2⟩⟩
    rw [heq, closure_Ioc (by norm_num : (0 : ℝ) ≠ 1)]
    exact ⟨le_rfl, zero_le_one⟩
  simpa using hm.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt ht

/-- Analytic boundary lemma; the two boundary estimates must be proved by the caller. -/
theorem exponential_sum_derivative_nonpos {ι : Type*} [Fintype ι]
    (w : ι → ℂ) (a : ι → ℝ) (hw : ∑ i, w i = 1)
    (h0 : ∀ z : ℂ, z.re = 0 → ‖exponential_sum w a z‖ ≤ 1)
    (h1 : ∀ z : ℂ, z.re = 1 → ‖exponential_sum w a z‖ ≤ 1) :
    ∑ i, (w i).re * a i ≤ 0 := by
  have hstrip (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ‖exponential_sum w a (t : ℂ)‖ ≤ 1 := by
    have h := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip₀₁'
      (exponential_sum w a) (z := (t : ℂ)) (a := 1) (b := 1) ht
      (exponential_sum_differentiable w a).diffContOnCl
      (exponential_sum_bounded w a) (fun z hz => h0 z hz) (fun z hz => h1 z hz)
    simpa using h
  have hd : HasDerivAt (exponential_sum w a) (∑ i, w i * (a i : ℂ)) (0 : ℂ) := by
    unfold exponential_sum
    have hsum : HasDerivAt (∑ i, fun z : ℂ => w i * Complex.exp (z * (a i : ℂ)))
        (∑ i, w i * (Complex.exp (0 * (a i : ℂ)) * (1 * (a i : ℂ)))) (0 : ℂ) :=
      HasDerivAt.sum (fun i _ =>
        (((hasDerivAt_id (0 : ℂ)).mul_const (a i : ℂ)).cexp.const_mul (w i)))
    have hfun : (∑ i, fun z : ℂ => w i * Complex.exp (z * (a i : ℂ))) =
        (fun z : ℂ => ∑ i, w i * Complex.exp (z * (a i : ℂ))) := by
      ext z
      simp
    rw [hfun] at hsum
    simpa only [zero_mul, Complex.exp_zero, one_mul] using hsum
  have hdr := hd.real_of_complex
  have hm : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (exponential_sum w a (t : ℂ)).re ≤ (exponential_sum w a (0 : ℂ)).re := by
    intro t ht
    have hreal := (Complex.re_le_norm (exponential_sum w a (t : ℂ))).trans (hstrip t ht)
    simpa [exponential_sum, hw] using hreal
  have h := right_derivative_nonpos hdr hm
  simpa [Complex.mul_re] using h

theorem exp_log_half {p : ℝ} (hp : 0 < p) : Real.exp (Real.log p / 2) = Real.sqrt p := by
  have hs := Real.sq_sqrt hp.le
  have he : Real.exp (Real.log p / 2) ^ 2 = p := by
    rw [pow_two, ← Real.exp_add]
    convert Real.exp_log hp using 1
    congr 1
    ring
  nlinarith [Real.exp_pos (Real.log p / 2), Real.sqrt_nonneg p]

theorem entropy_weight_bound {p q c : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hc : 0 < c)
    {w : ℂ} (hw : ‖w‖ ≤ c * Real.sqrt p * Real.sqrt q) :
    ‖w‖ * Real.exp ((Real.log p + Real.log q) / 2 - Real.log c) ≤ p * q := by
  by_cases hp0 : p = 0
  · have hz : w = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hp0] using hw) (norm_nonneg _))
    simp [hp0, hz]
  by_cases hq0 : q = 0
  · have hz : w = 0 := norm_eq_zero.mp (le_antisymm (by simpa [hq0] using hw) (norm_nonneg _))
    simp [hq0, hz]
  have hep : Real.exp ((Real.log p + Real.log q) / 2 - Real.log c) =
      Real.sqrt p * Real.sqrt q / c := by
    rw [Real.exp_sub, add_div, Real.exp_add, exp_log_half (lt_of_le_of_ne hp (Ne.symm hp0)),
      exp_log_half (lt_of_le_of_ne hq (Ne.symm hq0)), Real.exp_log hc]
  rw [hep]
  calc ‖w‖ * (Real.sqrt p * Real.sqrt q / c) ≤
      (c * Real.sqrt p * Real.sqrt q) * (Real.sqrt p * Real.sqrt q / c) :=
        mul_le_mul_of_nonneg_right hw (div_nonneg (mul_nonneg (Real.sqrt_nonneg _)
              (Real.sqrt_nonneg _)) hc.le)
       _ = p * q := by
         calc _ = (Real.sqrt p ^ 2 * Real.sqrt q ^ 2) := by field_simp
              _ = p * q := by rw [Real.sq_sqrt hp, Real.sq_sqrt hq]

/-- Scalar interpolation lemma. Its phase bound is discharged by measurement contractions. -/
theorem entropy_from_joint_amplitudes {ι κ : Type*} [Fintype ι] [Fintype κ]
    (p : ι → ℝ) (q : κ → ℝ) (w : ι → κ → ℂ) {c : ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) (hc : 0 < c)
    (hw : ∑ j, ∑ k, w j k = 1)
    (hrow : ∀ j, ∑ k, (w j k).re = p j)
    (hcol : ∀ k, ∑ j, (w j k).re = q k)
    (hentry : ∀ j k, ‖w j k‖ ≤ c * Real.sqrt (p j) * Real.sqrt (q k))
    (hphase : ∀ z : ℂ, z.re = 0 →
      ‖exponential_sum (fun jk : ι × κ => w jk.1 jk.2)
        (fun jk => (Real.log (p jk.1) + Real.log (q jk.2)) / 2 - Real.log c) z‖ ≤ 1) :
    uncertainty_bound c ≤ shannon_entropy_bits p + shannon_entropy_bits q := by
  let a : ι × κ → ℝ := fun jk => (Real.log (p jk.1) + Real.log (q jk.2)) / 2 - Real.log c
  have h1 (z : ℂ) (hz : z.re = 1) :
      ‖exponential_sum (fun jk : ι × κ => w jk.1 jk.2) a z‖ ≤ 1 := by
    unfold exponential_sum
    apply (norm_sum_le _ _).trans
    calc (∑ jk : ι × κ, ‖w jk.1 jk.2 * Complex.exp (z * (a jk : ℂ))‖) ≤
        ∑ jk : ι × κ, p jk.1 * q jk.2 := by
          apply Finset.sum_le_sum
          intro jk _
          rw [norm_mul, Complex.norm_exp]
          simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hz,
            one_mul, mul_zero, sub_zero]
          exact entropy_weight_bound (hp.1 _) (hq.1 _) hc (hentry _ _)
         _ = 1 := by simp [Fintype.sum_prod_type, ← Finset.mul_sum, hq.2, hp.2]
  have hd := exponential_sum_derivative_nonpos (fun jk : ι × κ => w jk.1 jk.2) a
    (by simpa [Fintype.sum_prod_type] using hw) hphase h1
  have heq : (∑ jk : ι × κ, (w jk.1 jk.2).re * a jk) =
      ((∑ j, p j * Real.log (p j)) + ∑ k, q k * Real.log (q k)) / 2 - Real.log c := by
    simp only [a, mul_sub, add_div, mul_add, ← mul_div_assoc,
      Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
      Fintype.sum_prod_type, ← Finset.sum_div]
    have hr : (∑ j, ∑ k, (w j k).re * Real.log (p j)) = ∑ j, p j * Real.log (p j) := by
      simp only [← Finset.sum_mul, hrow]
    have hk : (∑ j, ∑ k, (w j k).re * Real.log (q k)) = ∑ k, q k * Real.log (q k) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, hcol]
    simp only [hk, ← Finset.sum_mul, hrow, hp.2, one_mul]
  rw [heq] at hd
  simp only [shannon_entropy_bits, xlogx_of_nonneg (hp.1 _), xlogx_of_nonneg (hq.1 _),
    uncertainty_bound]
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← add_div, ← mul_div_assoc]
  apply (div_le_div_iff_of_pos_right htwo).mpr
  linarith

abbrev op {d : ℕ} (A : Q d) := Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) A

/-- Finite phases are contractions when averaged against a POVM. -/
theorem phase_effect_contraction {d m : ℕ} [NeZero d] (E : FinitePOVM d m)
    (u : Fin m → ℂ) (hu : ∀ j, ‖u j‖ ≤ 1) : ‖∑ j, u j • E.effects j‖ ≤ 1 := by
  let D : Matrix (Fin d × Fin m) (Fin d × Fin m) ℂ := Matrix.diagonal (fun a => u a.2)
  have hd : ‖D‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun a => hu a.2)
  have hv : ‖V E‖ ≤ 1 := by
    have hh := Matrix.l2_opNorm_conjTranspose_mul_self (V E)
    rw [isometry_v, norm_one] at hh
    nlinarith [norm_nonneg (V E)]
  have hsum : ∑ j, u j • E.effects j = (V E).conjTranspose * D * V E := by
    have hD : D = ∑ j, u j • projector d j := by
      ext a b
      simp only [D, Matrix.diagonal_apply, Matrix.sum_apply, Matrix.smul_apply,
        smul_eq_mul, projector_apply]
      by_cases hab : a = b
      · subst b
        simp
      · simp [hab]
    rw [hD, Matrix.mul_sum, Matrix.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.mul_smul, Matrix.smul_mul, naimark_dilation_exact]
  rw [hsum]
  calc ‖(V E).conjTranspose * D * V E‖ ≤ ‖(V E).conjTranspose‖ * ‖D‖ * ‖V E‖ :=
         (Matrix.l2_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _)
               (norm_nonneg _))
       _ ≤ 1 := by
         rw [Matrix.l2_opNorm_conjTranspose]
         have hh := mul_le_mul hv hd (norm_nonneg D) zero_le_one
         simpa using mul_le_mul hh hv (norm_nonneg (V E)) (by norm_num)

def pure_prob {d m : ℕ} (E : FinitePOVM d m) (ψ : EuclideanSpace ℂ (Fin d)) (j : Fin m) : ℝ :=
  ‖op (sqrt_effects E j) ψ‖ ^ 2

theorem pure_prob_inner {d m : ℕ} (E : FinitePOVM d m) (ψ : EuclideanSpace ℂ (Fin d))
    (j : Fin m) : (pure_prob E ψ j : ℂ) = inner ℂ ψ (op (E.effects j) ψ) := by
  have he : op (E.effects j) = (op (sqrt_effects E j)).adjoint * op (sqrt_effects E j) := by
    rw [← ContinuousLinearMap.star_eq_adjoint, ← map_star, ← map_mul,
          Matrix.star_eq_conjTranspose, sqrt_hermitian, sqrt_square]
  rw [he, mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  simp [pure_prob, inner_self_eq_norm_sq_to_K]

theorem pure_prob_distribution {d m : ℕ} (E : FinitePOVM d m)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) : IsDistribution (pure_prob E ψ) := by
  refine ⟨fun j => sq_nonneg _, ?_⟩
  have h : ((∑ j, pure_prob E ψ j : ℝ) : ℂ) = 1 := by
    rw [Complex.ofReal_sum]
    simp only [pure_prob_inner, ← inner_sum, ← sum_apply, ← map_sum,
      E.completeness, map_one, one_apply_eq_self, inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  exact_mod_cast h

def joint_amplitude {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (j : Fin m) (k : Fin n) : ℂ :=
  inner ℂ ψ (op (E.effects j * F.effects k) ψ)

theorem joint_row {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (j : Fin m) :
    ∑ k, joint_amplitude E F ψ j k = (pure_prob E ψ j : ℂ) := by
  simp only [joint_amplitude, ← inner_sum, ← sum_apply, ← map_sum,
    ← Matrix.mul_sum, F.completeness, Matrix.mul_one, pure_prob_inner]

theorem joint_col {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (k : Fin n) :
    ∑ j, joint_amplitude E F ψ j k = (pure_prob F ψ k : ℂ) := by
  simp only [joint_amplitude, ← inner_sum, ← sum_apply, ← map_sum,
    ← Matrix.sum_mul, E.completeness, Matrix.one_mul, pure_prob_inner]

theorem joint_entry_bound {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (j : Fin m) (k : Fin n) :
    ‖joint_amplitude E F ψ j k‖ ≤ c_overlap E F * Real.sqrt (pure_prob E ψ j) *
      Real.sqrt (pure_prob F ψ k) := by
  have he : E.effects j * F.effects k =
      (sqrt_effects E j).conjTranspose * (sqrt_effects E j * sqrt_effects F k) * sqrt_effects F
            k := by
    rw [sqrt_hermitian]
    rw [← Matrix.mul_assoc, sqrt_square, Matrix.mul_assoc, sqrt_square]
  have heop : op (E.effects j * F.effects k) =
      (op (sqrt_effects E j)).adjoint * op (sqrt_effects E j * sqrt_effects F k) * op
            (sqrt_effects F k) := by
    dsimp only [op]
    rw [he, map_mul, map_mul, ← Matrix.star_eq_conjTranspose, map_star,
      ContinuousLinearMap.star_eq_adjoint]
  rw [joint_amplitude, heop, mul_apply_eq_comp, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right]
  calc ‖inner ℂ (op (sqrt_effects E j) ψ)
        (op (sqrt_effects E j * sqrt_effects F k) (op (sqrt_effects F k) ψ))‖ ≤
        ‖op (sqrt_effects E j) ψ‖ * (‖op (sqrt_effects E j * sqrt_effects F k)‖ * ‖op
              (sqrt_effects F k) ψ‖) :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
          (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _))
       _ ≤ c_overlap E F * Real.sqrt (pure_prob E ψ j) * Real.sqrt (pure_prob F ψ k) := by
         simp only [pure_prob, Real.sqrt_sq_eq_abs, abs_norm]
         have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
           (entry_norm_le_overlap E F j k) (norm_nonneg (op (sqrt_effects F k) ψ)))
           (norm_nonneg (op (sqrt_effects E j) ψ))
         simpa only [op, Matrix.l2_opNorm_toEuclideanCLM, mul_assoc, mul_left_comm] using h

theorem joint_phase_bound {d m n : ℕ} [NeZero d]
    (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) (z : ℂ) (hz : z.re = 0) :
    ‖exponential_sum (fun jk : Fin m × Fin n => joint_amplitude E F ψ jk.1 jk.2)
      (fun jk => (Real.log (pure_prob E ψ jk.1) + Real.log (pure_prob F ψ jk.2)) / 2 -
        Real.log (c_overlap E F)) z‖ ≤ 1 := by
  let u : Fin m → ℂ := fun j => Complex.exp (z * ((Real.log (pure_prob E ψ j) / 2 : ℝ) : ℂ))
  let v : Fin n → ℂ := fun k => Complex.exp (z * ((Real.log (pure_prob F ψ k) / 2 : ℝ) : ℂ))
  let s : ℂ := Complex.exp (z * ((-Real.log (c_overlap E F) : ℝ) : ℂ))
  have hnorm (a : ℝ) : ‖Complex.exp (z * (a : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re, hz]
  have hu : ∀ j, ‖u j‖ ≤ 1 := fun j => (hnorm _).le
  have hv : ∀ k, ‖v k‖ ≤ 1 := fun k => (hnorm _).le
  have hs : ‖s‖ = 1 := hnorm _
  have hexp (j : Fin m) (k : Fin n) :
      Complex.exp (z * (((Real.log (pure_prob E ψ j) + Real.log (pure_prob F ψ k)) / 2 -
        Real.log (c_overlap E F) : ℝ) : ℂ)) = s * (u j * v k) := by
    dsimp [s, u, v]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have heq : exponential_sum (fun jk : Fin m × Fin n => joint_amplitude E F ψ jk.1 jk.2)
      (fun jk => (Real.log (pure_prob E ψ jk.1) + Real.log (pure_prob F ψ jk.2)) / 2 -
        Real.log (c_overlap E F)) z =
      s * inner ℂ ψ (op ((∑ j, u j • E.effects j) * (∑ k, v k • F.effects k)) ψ) := by
    simp only [exponential_sum, Fintype.sum_prod_type, hexp, Matrix.sum_mul,
      Matrix.smul_mul, Matrix.mul_smul, map_sum, map_smul, sum_apply, smul_apply,
      inner_sum, inner_smul_right, Finset.mul_sum, joint_amplitude]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq, norm_mul, hs, one_mul]
  apply (norm_inner_le_norm _ _).trans
  rw [hψ, one_mul]
  calc ‖op ((∑ j, u j • E.effects j) * (∑ k, v k • F.effects k)) ψ‖ ≤
      ‖op ((∑ j, u j • E.effects j) * (∑ k, v k • F.effects k))‖ * ‖ψ‖ :=
        ContinuousLinearMap.le_opNorm _ _
       _ ≤ 1 := by
         rw [hψ, mul_one]
         change ‖(∑ j, u j • E.effects j) * (∑ k, v k • F.effects k)‖ ≤ 1
         apply (norm_mul_le _ _).trans
         have h := mul_le_mul (phase_effect_contraction E u hu) (phase_effect_contraction F v hv)
           (norm_nonneg _) zero_le_one
         simpa using h

theorem maassen_uffink_pure_state {d m n : ℕ} [NeZero d]
    (E : FinitePOVM d m) (F : FinitePOVM d n)
    (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    uncertainty_bound (c_overlap E F) ≤
      shannon_entropy_bits (pure_prob E ψ) + shannon_entropy_bits (pure_prob F ψ) := by
  apply entropy_from_joint_amplitudes (pure_prob E ψ) (pure_prob F ψ) (joint_amplitude E F ψ)
    (pure_prob_distribution E ψ hψ) (pure_prob_distribution F ψ hψ) (povm_overlap_bounds E F).1
  · simp only [joint_row, ← Complex.ofReal_sum, (pure_prob_distribution E ψ hψ).2,
        Complex.ofReal_one]
  · intro j
    have h := congrArg Complex.re (joint_row E F ψ j)
    simpa using h
  · intro k
    have h := congrArg Complex.re (joint_col E F ψ k)
    simpa using h
  · exact joint_entry_bound E F ψ
  · exact joint_phase_bound E F ψ hψ

def pure_density {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) : Q d :=
  Matrix.vecMulVec (⇑ψ) (star (⇑ψ))

theorem pure_density_trace_mul {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (A : Q d) :
    Matrix.trace (pure_density ψ * A) = inner ℂ ψ (op A ψ) := by
  simp only [pure_density, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec_apply,
    Pi.star_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Matrix.ofLp_toEuclideanCLM, Matrix.mulVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem pure_density_valid {d : ℕ} (ψ : EuclideanSpace ℂ (Fin d)) (hψ : ‖ψ‖ = 1) :
    QuantumNoBroadcastingMixed.IsDensityMatrix (pure_density ψ) := by
  refine ⟨Matrix.posSemidef_vecMulVec_self_star _, ?_⟩
  have h := pure_density_trace_mul ψ (1 : Q d)
  simpa [op, inner_self_eq_norm_sq_to_K, hψ] using h

theorem prob_pure_density {d m : ℕ} (E : FinitePOVM d m) (ψ : EuclideanSpace ℂ (Fin d)) :
    prob_dist E (pure_density ψ) = pure_prob E ψ := by
  funext j
  rw [prob_dist, pure_density_trace_mul, ← pure_prob_inner, Complex.ofReal_re]

theorem spectral_density_decomposition {d : ℕ} (ρ : Q d) (hρ : ρ.PosSemidef) :
    ρ = ∑ i, (hρ.isHermitian.eigenvalues i : ℂ) • pure_density (hρ.isHermitian.eigenvectorBasis
          i) := by
  conv_lhs => rw [hρ.isHermitian.spectral_theorem]
  change (hρ.isHermitian.eigenvectorUnitary : Q d) *
    Matrix.diagonal (fun i => (hρ.isHermitian.eigenvalues i : ℂ)) *
      (hρ.isHermitian.eigenvectorUnitary : Q d).conjTranspose = _
  ext a b
  conv_lhs =>
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
  simp only [Matrix.conjTranspose_apply,
    hρ.isHermitian.eigenvectorUnitary_apply, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, pure_density, Matrix.vecMulVec_apply, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem spectral_weights_distribution {d : ℕ} (ρ : Q d)
    (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    IsDistribution hρ.1.isHermitian.eigenvalues := by
  refine ⟨fun i => hρ.1.eigenvalues_nonneg i, ?_⟩
  have h := congrArg Complex.re hρ.1.isHermitian.trace_eq_sum_eigenvalues
  simpa [hρ.2] using h.symm

theorem prob_spectral_mixture {d m : ℕ} (E : FinitePOVM d m) (ρ : Q d) (hρ : ρ.PosSemidef)
    (j : Fin m) : prob_dist E ρ j =
      ∑ i, hρ.isHermitian.eigenvalues i * pure_prob E (hρ.isHermitian.eigenvectorBasis i) j := by
  unfold prob_dist
  conv_lhs => rw [spectral_density_decomposition ρ hρ]
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum, Matrix.trace_smul,
    pure_density_trace_mul, ← pure_prob_inner, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.re_sum]

theorem entropy_finite_concavity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (w : ι → ℝ) (p : ι → κ → ℝ) (hw : IsDistribution w) (hp : ∀ i j, 0 ≤ p i j) :
    (∑ i, w i * shannon_entropy_bits (p i)) ≤
      shannon_entropy_bits (fun j => ∑ i, w i * p i j) := by
  simp_rw [entropy_eq_negMulLog _ (hp _)]
  rw [entropy_eq_negMulLog _ (fun j => Finset.sum_nonneg (fun i _ => mul_nonneg (hw.1 i) (hp i j)))]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro j _
  simpa only [smul_eq_mul] using
    Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ) (w := w)
      (p := fun i => p i j) (fun i _ => hw.1 i) hw.2 (fun i _ => hp i j)

theorem maassen_uffink_mixed_state {d m n : ℕ} [NeZero d]
    (E : FinitePOVM d m) (F : FinitePOVM d n) (ρ : Q d)
    (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    uncertainty_bound (c_overlap E F) ≤
      shannon_entropy_bits (prob_dist E ρ) + shannon_entropy_bits (prob_dist F ρ) := by
  let w := hρ.1.isHermitian.eigenvalues
  let ψ := hρ.1.isHermitian.eigenvectorBasis
  have hw : IsDistribution w := spectral_weights_distribution ρ hρ
  have hE := entropy_finite_concavity w (fun i => pure_prob E (ψ i)) hw (fun i j => sq_nonneg _)
  have hF := entropy_finite_concavity w (fun i => pure_prob F (ψ i)) hw (fun i j => sq_nonneg _)
  have hmixE : (fun j => ∑ i, w i * pure_prob E (ψ i) j) = prob_dist E ρ :=
    funext fun j => (prob_spectral_mixture E ρ hρ.1 j).symm
  have hmixF : (fun j => ∑ i, w i * pure_prob F (ψ i) j) = prob_dist F ρ :=
    funext fun j => (prob_spectral_mixture F ρ hρ.1 j).symm
  rw [hmixE] at hE
  rw [hmixF] at hF
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_left (maassen_uffink_pure_state E F (ψ i) (ψ.orthonormal.1 i)) (hw.1 i))
  rw [← Finset.sum_mul, hw.2, one_mul] at hsum
  simp only [mul_add, Finset.sum_add_distrib] at hsum
  linarith

theorem projection_sqrt {d : ℕ} {P : Q d} (hP : P.PosSemidef) (hi : P * P = P) :
    CFC.sqrt P = P := CFC.sqrt_unique hi hP.nonneg

theorem projection_norm {d : ℕ} {P : Q d} (hP : P.PosSemidef) (hi : P * P = P) (hne : P ≠ 0) :
    ‖P‖ = 1 := by
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self P
  rw [hP.isHermitian, hi] at hh
  nlinarith [norm_pos_iff.mpr hne]

theorem overlap_le_of_entry_le {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    {r : ℝ} (hr : 0 ≤ r) (h : ∀ j k, ‖sqrt_effects E j * sqrt_effects F k‖ ≤ r) :
    c_overlap E F ≤ r := by
  have hh : (Finset.univ.sup (fun jk : Fin m × Fin n =>
      ‖Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin d) (sqrt_effects E jk.1 * sqrt_effects F
            jk.2)‖₊) : NNReal) ≤ ⟨r, hr⟩ := by
    apply Finset.sup_le
    intro jk _
    exact h jk.1 jk.2
  exact NNReal.coe_mono hh

open QuantumPOVMInformationallyComplete in
def pauliZ : FinitePOVM 2 2 := basisPOVM 2

open QuantumPOVMInformationallyComplete in
def pauliX : FinitePOVM 2 2 where
  effects j := if j = 0 then phasePlus else phaseMinus
  pos_semidef j := by
    by_cases h : j = 0
    · simp only [h, ite_true]
      exact phase_pair_density.1.1
    · simp only [h, ite_false]
      exact phase_pair_density.2.1
  completeness := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_succ, phasePlus, phaseMinus, blochEffect, Matrix.one_apply]

theorem pauli_idempotent :
    (∀ j, pauliX.effects j * pauliX.effects j = pauliX.effects j) ∧
    (∀ j, pauliZ.effects j * pauliZ.effects j = pauliZ.effects j) := by
  constructor <;> intro j <;> ext a b <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauliX, pauliZ, QuantumPOVMInformationallyComplete.basisPOVM,
      QuantumPOVMInformationallyComplete.phasePlus, QuantumPOVMInformationallyComplete.phaseMinus,
      QuantumPOVMInformationallyComplete.blochEffect, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliX_norm (k : Fin 2) : ‖pauliX.effects k‖ = 1 := by
  apply projection_norm (pauliX.pos_semidef k) (pauli_idempotent.1 k)
  intro h
  have hh := congrFun (congrFun h 0) 0
  fin_cases k <;> norm_num [pauliX, QuantumPOVMInformationallyComplete.phasePlus,
    QuantumPOVMInformationallyComplete.phaseMinus,
          QuantumPOVMInformationallyComplete.blochEffect] at hh

theorem pauli_product_square (j k : Fin 2) :
    (pauliZ.effects j * pauliX.effects k).conjTranspose * (pauliZ.effects j * pauliX.effects k) =
      (1 / 2 : ℂ) • pauliX.effects k := by
  ext a b
  fin_cases j <;> fin_cases k <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauliX, pauliZ, QuantumPOVMInformationallyComplete.basisPOVM,
      QuantumPOVMInformationallyComplete.phasePlus, QuantumPOVMInformationallyComplete.phaseMinus,
      QuantumPOVMInformationallyComplete.blochEffect, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.smul_apply]

theorem pauli_entry_overlap (j k : Fin 2) :
    ‖sqrt_effects pauliZ j * sqrt_effects pauliX k‖ = 1 / Real.sqrt 2 := by
  have hj : sqrt_effects pauliZ j = pauliZ.effects j :=
    projection_sqrt (pauliZ.pos_semidef j) (pauli_idempotent.2 j)
  have hk : sqrt_effects pauliX k = pauliX.effects k :=
    projection_sqrt (pauliX.pos_semidef k) (pauli_idempotent.1 k)
  rw [hj, hk]
  have hh := Matrix.l2_opNorm_conjTranspose_mul_self (pauliZ.effects j * pauliX.effects k)
  rw [pauli_product_square, norm_smul, pauliX_norm] at hh
  norm_num at hh
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (eq_div_iff hs.ne').mpr
  nlinarith [norm_nonneg (pauliZ.effects j * pauliX.effects k),
    sq_nonneg (‖pauliZ.effects j * pauliX.effects k‖ * Real.sqrt 2 - 1)]

theorem pauli_xz_overlap_exact : c_overlap pauliZ pauliX = 1 / Real.sqrt 2 := by
  apply le_antisymm
  · exact overlap_le_of_entry_le _ _ (by positivity) (fun j k => (pauli_entry_overlap j k).le)
  · rw [← pauli_entry_overlap 0 0]
    exact entry_norm_le_overlap _ _ _ _

theorem pauli_xz_entropy_bound_exact : uncertainty_bound (c_overlap pauliZ pauliX) = 1 := by
  rw [pauli_xz_overlap_exact, uncertainty_bound, Real.log_div (by norm_num)
    (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))), Real.log_one, Real.log_sqrt (by norm_num)]
  have h : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  norm_num

def qubitZero : Q 2 := !![1, 0; 0, 0]
def qubitMixed : Q 2 := (1 / 2 : ℂ) • 1

theorem qubitZero_density : QuantumNoBroadcastingMixed.IsDensityMatrix qubitZero := by
  have heq : qubitZero = pauliZ.effects 0 := by
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  refine ⟨heq ▸ pauliZ.pos_semidef 0, ?_⟩
  norm_num [qubitZero, Matrix.trace, Fin.sum_univ_succ]

theorem qubitMixed_density : QuantumNoBroadcastingMixed.IsDensityMatrix qubitMixed := by
  refine ⟨Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.nonneg_iff]), ?_⟩
  norm_num [qubitMixed, Matrix.trace, Fin.sum_univ_succ]

theorem pauli_probabilities :
    prob_dist pauliZ qubitZero = ![1, 0] ∧ prob_dist pauliX qubitZero = ![1/2, 1/2] ∧
    prob_dist pauliZ qubitMixed = ![1/2, 1/2] ∧ prob_dist pauliX qubitMixed = ![1/2, 1/2] := by
  repeat' constructor
  all_goals
    funext j
    fin_cases j <;> norm_num [prob_dist, pauliZ, pauliX, qubitZero, qubitMixed,
      QuantumPOVMInformationallyComplete.basisPOVM, QuantumPOVMInformationallyComplete.phasePlus,
      QuantumPOVMInformationallyComplete.phaseMinus, QuantumPOVMInformationallyComplete.blochEffect,
      Matrix.trace, Matrix.mul_apply, Matrix.smul_apply, Matrix.vecMul, dotProduct,
      Matrix.diagonal_apply, Fin.sum_univ_succ]

theorem binary_entropy_values : shannon_entropy_bits (![1, 0] : Fin 2 → ℝ) = 0 ∧
    shannon_entropy_bits (![1/2, 1/2] : Fin 2 → ℝ) = 1 := by
  constructor
  · norm_num [shannon_entropy_bits, xlogx, Fin.sum_univ_succ]
  · norm_num [shannon_entropy_bits, xlogx, Fin.sum_univ_succ, Real.log_div]
    field_simp [ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    ring

theorem pauli_entropy_regressions :
    shannon_entropy_bits (prob_dist pauliZ qubitZero) = 0 ∧
    shannon_entropy_bits (prob_dist pauliX qubitZero) = 1 ∧
    shannon_entropy_bits (prob_dist pauliZ qubitMixed) + shannon_entropy_bits (prob_dist pauliX
          qubitMixed) = 2 := by
  rw [pauli_probabilities.1, pauli_probabilities.2.1, pauli_probabilities.2.2.1,
    pauli_probabilities.2.2.2, binary_entropy_values.1, binary_entropy_values.2]
  norm_num

theorem entropy_relabel {ι κ : Type*} [Fintype ι] [Fintype κ] (p : ι → ℝ) (e : κ ≃ ι) :
    shannon_entropy_bits (p ∘ e) = shannon_entropy_bits p := by
  unfold shannon_entropy_bits
  simp only [Function.comp_apply]
  rw [e.sum_comp (fun i => xlogx (p i))]

theorem c_overlap_nonneg {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n) :
    0 ≤ c_overlap E F := NNReal.coe_nonneg _

open QuantumPOVMInformationallyComplete in
theorem overlap_relabel {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (e : Fin m ≃ Fin m) (f : Fin n ≃ Fin n) :
    c_overlap (relabel E e) (relabel F f) = c_overlap E F := by
  apply le_antisymm
  · apply overlap_le_of_entry_le _ _ (c_overlap_nonneg E F)
    intro j k
    exact entry_norm_le_overlap E F (e j) (f k)
  · apply overlap_le_of_entry_le _ _ (c_overlap_nonneg _ _)
    intro j k
    have h := entry_norm_le_overlap (relabel E e) (relabel F f) (e.symm j) (f.symm k)
    simpa [sqrt_effects, relabel] using h

open QuantumPOVMInformationallyComplete in
theorem measurement_entropy_relabel {d m : ℕ} (E : FinitePOVM d m) (ρ :
      QuantumPOVMNaimarkDilation.Q d)
    (e : Fin m ≃ Fin m) :
    shannon_entropy_bits (prob_dist (relabel E e) ρ) = shannon_entropy_bits (prob_dist E ρ) := by
  unfold shannon_entropy_bits prob_dist relabel
  change (-(∑ j, xlogx ((ρ * E.effects (e j)).trace.re))) / Real.log 2 = _
  rw [e.sum_comp (fun j => xlogx ((ρ * E.effects j).trace.re))]

def prepend_zero {d m : ℕ} (E : FinitePOVM d m) : FinitePOVM d (m+1) where
  effects := Fin.cases 0 E.effects
  pos_semidef := Fin.cases Matrix.PosSemidef.zero E.pos_semidef
  completeness := by simp [Fin.sum_univ_succ, E.completeness]

theorem zero_effect_probability {d m : ℕ} (E : FinitePOVM d m) (ρ : Q d) (j : Fin m)
    (hj : E.effects j = 0) : prob_dist E ρ j = 0 := by simp [prob_dist, hj]

theorem prepend_zero_entropy {d m : ℕ} (E : FinitePOVM d m) (ρ : Q d) :
    shannon_entropy_bits (prob_dist (prepend_zero E) ρ) = shannon_entropy_bits (prob_dist E ρ) := by
  simp [shannon_entropy_bits, prob_dist, prepend_zero, Fin.sum_univ_succ]

theorem prepend_zero_overlap {d m n : ℕ} (E : FinitePOVM d m) (F : FinitePOVM d n) :
    c_overlap (prepend_zero E) F = c_overlap E F := by
  apply le_antisymm
  · apply overlap_le_of_entry_le _ _ (c_overlap_nonneg _ _)
    intro j k
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [sqrt_effects, prepend_zero] using c_overlap_nonneg E F
    · exact entry_norm_le_overlap E F j k
  · apply overlap_le_of_entry_le _ _ (c_overlap_nonneg _ _)
    intro j k
    exact entry_norm_le_overlap (prepend_zero E) F j.succ k

def qutritZ : FinitePOVM 3 3 := QuantumPOVMInformationallyComplete.basisPOVM 3

def qutrit_effects : Fin 3 → Q 3 :=
  ![!![1,0,0;0,0,0;0,0,0], !![0,0,0;0,1/2,1/2;0,1/2,1/2],
    !![0,0,0;0,1/2,-1/2;0,-1/2,1/2]]

theorem qutrit_projection_facts (j : Fin 3) :
    (qutrit_effects j).conjTranspose = qutrit_effects j ∧
    qutrit_effects j * qutrit_effects j = qutrit_effects j := by
  constructor <;> ext a b <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [qutrit_effects, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ]

def qutritF : FinitePOVM 3 3 where
  effects := qutrit_effects
  pos_semidef j := by
    have h := Matrix.posSemidef_conjTranspose_mul_self (qutrit_effects j)
    rwa [(qutrit_projection_facts j).1, (qutrit_projection_facts j).2] at h
  completeness := by
    ext a b
    fin_cases a <;> fin_cases b <;> norm_num [qutrit_effects, Fin.sum_univ_succ, Matrix.one_apply]

theorem qutrit_shared_projection : qutritZ.effects 0 = qutritF.effects 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;> rfl

theorem qutrit_overlap_one : c_overlap qutritZ qutritF = 1 := by
  apply le_antisymm (overlap_le_one _ _)
  have h := entry_norm_le_overlap qutritZ qutritF 0 0
  have hsF : sqrt_effects qutritF 0 = qutritF.effects 0 :=
    projection_sqrt (qutritF.pos_semidef 0) (qutrit_projection_facts 0).2
  have hsZ : sqrt_effects qutritZ 0 = qutritF.effects 0 := by
    rw [sqrt_effects, qutrit_shared_projection]
    exact hsF
  have hn : ‖qutritF.effects 0‖ = 1 := by
    apply projection_norm (qutritF.pos_semidef 0) (qutrit_projection_facts 0).2
    intro hz
    have hh := congrFun (congrFun hz 0) 0
    norm_num [qutritF, qutrit_effects] at hh
  rw [hsZ, hsF, show qutritF.effects 0 * qutritF.effects 0 = qutritF.effects 0 from
    (qutrit_projection_facts 0).2, hn] at h
  exact h

theorem qutrit_noncommuting :
    qutritZ.effects 1 * qutritF.effects 1 ≠ qutritF.effects 1 * qutritZ.effects 1 := by
  intro h
  have hh := congrFun (congrFun h 1) 2
  norm_num [qutritZ, qutritF, qutrit_effects, QuantumPOVMInformationallyComplete.basisPOVM,
    Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply] at hh
  change (1 / 2 : ℂ) = 0 at hh
  norm_num at hh

theorem qutrit_zero_density : QuantumNoBroadcastingMixed.IsDensityMatrix (qutritF.effects 0) := by
  refine ⟨qutritF.pos_semidef 0, ?_⟩
  norm_num [qutritF, qutrit_effects, Matrix.trace, Fin.sum_univ_succ]

theorem qutrit_entropy_zero :
    shannon_entropy_bits (prob_dist qutritZ (qutritF.effects 0)) = 0 ∧
    shannon_entropy_bits (prob_dist qutritF (qutritF.effects 0)) = 0 := by
  have hp : prob_dist qutritZ (qutritF.effects 0) = ![1,0,0] ∧
      prob_dist qutritF (qutritF.effects 0) = ![1,0,0] := by
    constructor <;> funext j <;> fin_cases j <;>
      norm_num [prob_dist, qutritZ, qutritF, qutrit_effects,
            QuantumPOVMInformationallyComplete.basisPOVM,
        Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ, Matrix.diagonal_apply, Matrix.vecMul,
              dotProduct]
  rw [hp.1, hp.2]
  norm_num [shannon_entropy_bits, xlogx, Fin.sum_univ_succ]

theorem prob_dist_affine {d m : ℕ} (E : FinitePOVM d m) (ρ σ : Q d) (a b : ℝ) :
    prob_dist E ((a : ℂ) • ρ + (b : ℂ) • σ) =
      fun j => a * prob_dist E ρ j + b * prob_dist E σ j := by
  funext j
  simp [prob_dist, Matrix.add_mul, Matrix.trace_add, Matrix.trace_smul,
    Complex.mul_re]

theorem measurement_entropy_concave {d m : ℕ} (E : FinitePOVM d m) (ρ σ : Q d)
    (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * shannon_entropy_bits (prob_dist E ρ) + b * shannon_entropy_bits (prob_dist E σ) ≤
      shannon_entropy_bits (prob_dist E ((a : ℂ) • ρ + (b : ℂ) • σ)) := by
  rw [prob_dist_affine]
  exact shannon_entropy_concave (prob_dist_isDistribution E ρ hρ).1
    (prob_dist_isDistribution E σ hσ).1 ha hb hab

theorem entropy_continuousOn {ι : Type*} [Fintype ι] :
    ContinuousOn (shannon_entropy_bits : (ι → ℝ) → ℝ) {p | ∀ i, 0 ≤ p i} := by
  have h : Continuous (fun p : ι → ℝ => (∑ i, Real.negMulLog (p i)) / Real.log 2) := by
    fun_prop
  exact h.continuousOn.congr (fun p hp => entropy_eq_negMulLog p hp)

theorem identical_basis_overlap : c_overlap pauliZ pauliZ = 1 := by
  apply le_antisymm (overlap_le_one _ _)
  have hs : sqrt_effects pauliZ 0 = pauliZ.effects 0 :=
    projection_sqrt (pauliZ.pos_semidef 0) (pauli_idempotent.2 0)
  have hn : ‖pauliZ.effects 0‖ = 1 := by
    apply projection_norm (pauliZ.pos_semidef 0) (pauli_idempotent.2 0)
    intro h
    have hh := congrFun (congrFun h 0) 0
    norm_num [pauliZ, QuantumPOVMInformationallyComplete.basisPOVM] at hh
  have h := entry_norm_le_overlap pauliZ pauliZ 0 0
  rwa [hs, pauli_idempotent.2, hn] at h

/-- Reviewed obligations. The uncertainty inequality is a proved field for all density matrices. -/
structure QuantumPOVMInformationEntropySuite : Prop where
  probabilities : ∀ {d m} (E : FinitePOVM d m) ρ,
    QuantumNoBroadcastingMixed.IsDensityMatrix ρ → IsDistribution (prob_dist E ρ)
  nonnegative : ∀ {n} (p : Fin n → ℝ), IsDistribution p → 0 ≤ shannon_entropy_bits p
  concavity : ∀ {n} (p q : Fin n → ℝ), (∀ i, 0 ≤ p i) → (∀ i, 0 ≤ q i) →
    ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * shannon_entropy_bits p + b * shannon_entropy_bits q ≤
        shannon_entropy_bits (fun i => a * p i + b * q i)
  overlap : ∀ {d m n} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n),
    0 < c_overlap E F ∧ c_overlap E F ≤ 1
  pure : ∀ {d m n} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n) ψ, ‖ψ‖ = 1 →
    uncertainty_bound (c_overlap E F) ≤ shannon_entropy_bits (pure_prob E ψ) +
          shannon_entropy_bits (pure_prob F ψ)
  mixed : ∀ {d m n} [NeZero d] (E : FinitePOVM d m) (F : FinitePOVM d n) ρ,
    QuantumNoBroadcastingMixed.IsDensityMatrix ρ → uncertainty_bound (c_overlap E F) ≤
      shannon_entropy_bits (prob_dist E ρ) + shannon_entropy_bits (prob_dist F ρ)
  positive_bound : ∀ c, 0 < c → c < 1 → 0 < uncertainty_bound c
  monotone_bound : ∀ c₁ c₂, 0 < c₁ → c₁ ≤ c₂ → uncertainty_bound c₂ ≤ uncertainty_bound c₁
  pauli_overlap : c_overlap pauliZ pauliX = 1 / Real.sqrt 2
  pauli_bound : uncertainty_bound (c_overlap pauliZ pauliX) = 1
  pure_attainment : shannon_entropy_bits (prob_dist pauliZ qubitZero) = 0 ∧
    shannon_entropy_bits (prob_dist pauliX qubitZero) = 1
  mixed_qubit : shannon_entropy_bits (prob_dist pauliZ qubitMixed) +
    shannon_entropy_bits (prob_dist pauliX qubitMixed) = 2
  noncommuting_counterexample :
    qutritZ.effects 1 * qutritF.effects 1 ≠ qutritF.effects 1 * qutritZ.effects 1 ∧
    c_overlap qutritZ qutritF = 1 ∧
    shannon_entropy_bits (prob_dist qutritZ (qutritF.effects 0)) = 0 ∧
    shannon_entropy_bits (prob_dist qutritF (qutritF.effects 0)) = 0
  label_invariance : ∀ {d m n} (E : FinitePOVM d m) (F : FinitePOVM d n)
    (e : Fin m ≃ Fin m) (f : Fin n ≃ Fin n),
    c_overlap (QuantumPOVMInformationallyComplete.relabel E e)
      (QuantumPOVMInformationallyComplete.relabel F f) = c_overlap E F
  zero_overlap : ∀ {d m n} (E : FinitePOVM d m) (F : FinitePOVM d n),
    c_overlap (prepend_zero E) F = c_overlap E F
  zero_outcome : ∀ {d m} (E : FinitePOVM d m) ρ,
    shannon_entropy_bits (prob_dist (prepend_zero E) ρ) = shannon_entropy_bits (prob_dist E ρ)

theorem verification_suite : QuantumPOVMInformationEntropySuite where
  probabilities := prob_dist_isDistribution
  nonnegative := fun _ hp => shannon_entropy_nonneg hp
  concavity := fun _ _ hp hq _ _ ha hb hab => shannon_entropy_concave hp hq ha hb hab
  overlap := povm_overlap_bounds
  pure := maassen_uffink_pure_state
  mixed := maassen_uffink_mixed_state
  positive_bound := fun _ hc h1 => bound_strictly_positive hc h1
  monotone_bound := fun _ _ h1 h12 => bound_monotone_in_c h1 h12
  pauli_overlap := pauli_xz_overlap_exact
  pauli_bound := pauli_xz_entropy_bound_exact
  pure_attainment := ⟨pauli_entropy_regressions.1, pauli_entropy_regressions.2.1⟩
  mixed_qubit := pauli_entropy_regressions.2.2
  noncommuting_counterexample := ⟨qutrit_noncommuting, qutrit_overlap_one, qutrit_entropy_zero⟩
  label_invariance := overlap_relabel
  zero_overlap := prepend_zero_overlap
  zero_outcome := prepend_zero_entropy

end QuantumPOVMInformationEntropy
