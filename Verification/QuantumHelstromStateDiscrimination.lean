/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMNaimarkDilation
import Verification.QuantumPOVMInformationEntropy
import Verification.QuantumChannelClassicalDataProcessing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite-dimensional Holevo–Helstrom optimization and classical decision rules.
The trace norm is defined via the positive square root of A†A, not the ambient matrix norm.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumChannelClassicalDataProcessing
namespace QuantumHelstromStateDiscrimination
variable {d m n : ℕ}

abbrev Density (ρ : Q d) := QuantumNoBroadcastingMixed.IsDensityMatrix ρ
structure Priors where
  p₀ : ℝ
  p₁ : ℝ
  nonneg₀ : 0 ≤ p₀
  nonneg₁ : 0 ≤ p₁
  total : p₀ + p₁ = 1

structure Effect (d : ℕ) where
  matrix : Q d
  positive : matrix.PosSemidef
  complement : (1 - matrix).PosSemidef

def spectral_map {A : Q d} (h : A.IsHermitian) (f : Fin d → ℝ) : Q d :=
  Unitary.conjStarAlgAut ℂ _ h.eigenvectorUnitary (Matrix.diagonal fun i => (f i : ℂ))

theorem spectral_map_add {A : Q d} (h : A.IsHermitian) (f g : Fin d → ℝ) :
    spectral_map h (f + g) = spectral_map h f + spectral_map h g := by
  simp only [spectral_map, Pi.add_apply, Complex.ofReal_add]
  rw [← Matrix.diagonal_add]
  exact map_add _ _ _

theorem spectral_map_sub {A : Q d} (h : A.IsHermitian) (f g : Fin d → ℝ) :
    spectral_map h (f - g) = spectral_map h f - spectral_map h g := by
  simp only [spectral_map, Pi.sub_apply, Complex.ofReal_sub]
  rw [← Matrix.diagonal_sub]
  exact map_sub _ _ _

theorem spectral_map_mul {A : Q d} (h : A.IsHermitian) (f g : Fin d → ℝ) :
    spectral_map h (f * g) = spectral_map h f * spectral_map h g := by
  simp only [spectral_map, Pi.mul_apply, Complex.ofReal_mul]
  rw [← Matrix.diagonal_mul_diagonal]
  exact map_mul _ _ _

@[simp] theorem spectral_map_one {A : Q d} (h : A.IsHermitian) : spectral_map h 1 = 1 := by
  simp [spectral_map, Matrix.diagonal_one]

@[simp] theorem spectral_map_zero {A : Q d} (h : A.IsHermitian) : spectral_map h 0 = 0 := by
  simp [spectral_map]

theorem spectral_map_eigenvalues {A : Q d} (h : A.IsHermitian) :
    spectral_map h h.eigenvalues = A := h.spectral_theorem.symm

theorem spectral_map_positive {A : Q d} (h : A.IsHermitian) (f : Fin d → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (spectral_map h f).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.PosSemidef.diagonal fun i => by simpa [Complex.nonneg_iff] using hf i

theorem spectral_map_trace {A : Q d} (h : A.IsHermitian) (f : Fin d → ℝ) :
    (spectral_map h f).trace.re = ∑ i, f i := by
  unfold spectral_map
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  simp [Matrix.trace_diagonal]

def positive_part {A : Q d} (h : A.IsHermitian) := spectral_map h fun i => max (h.eigenvalues i) 0
def negative_part {A : Q d} (h : A.IsHermitian) := spectral_map h fun i => max (-h.eigenvalues i) 0
def absolute_part {A : Q d} (h : A.IsHermitian) := spectral_map h fun i => |h.eigenvalues i|
def trace_norm (A : Q d) : ℝ := (CFC.sqrt (A.conjTranspose * A)).trace.re

theorem positive_part_positive {A : Q d} (h : A.IsHermitian) : (positive_part h).PosSemidef :=
  spectral_map_positive h _ fun _ => le_max_right _ _
theorem negative_part_positive {A : Q d} (h : A.IsHermitian) : (negative_part h).PosSemidef :=
  spectral_map_positive h _ fun _ => le_max_right _ _

theorem parts_sub {A : Q d} (h : A.IsHermitian) : positive_part h - negative_part h = A := by
  rw [positive_part, negative_part, ← spectral_map_sub]
  trans spectral_map h h.eigenvalues
  · congr 1
    funext i
    simp only [Pi.sub_apply]
    rcases le_total 0 (h.eigenvalues i) with hi | hi <;> simp [hi, neg_nonpos.mpr, neg_nonneg.mpr]
  · exact spectral_map_eigenvalues h

theorem parts_add {A : Q d} (h : A.IsHermitian) : positive_part h + negative_part h =
  absolute_part h := by
  rw [positive_part, negative_part, absolute_part, ← spectral_map_add]
  congr 1
  funext i
  simp only [Pi.add_apply]
  rcases le_total 0 (h.eigenvalues i) with hi | hi
  · simp [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi), abs_of_nonneg hi]
  · simp [max_eq_right hi, max_eq_left (neg_nonneg.mpr hi), abs_of_nonpos hi]

theorem absolute_part_sqrt {A : Q d} (h : A.IsHermitian) :
    CFC.sqrt (A.conjTranspose * A) = absolute_part h := by
  apply CFC.sqrt_unique
  · rw [absolute_part, ← spectral_map_mul, h]
    conv_rhs => rw [← spectral_map_eigenvalues h, ← spectral_map_mul]
    congr 1
    funext i
    simp [Pi.mul_apply, ← sq, sq_abs]
  · exact (spectral_map_positive h _ fun _ => abs_nonneg _).nonneg

theorem trace_norm_spectral {A : Q d} (h : A.IsHermitian) :
    trace_norm A = ∑ i, |h.eigenvalues i| := by
  rw [trace_norm, absolute_part_sqrt h, absolute_part, spectral_map_trace]

theorem trace_norm_parts {A : Q d} (h : A.IsHermitian) :
    trace_norm A = (positive_part h).trace.re + (negative_part h).trace.re := by
  rw [trace_norm, absolute_part_sqrt h, ← parts_add h, Matrix.trace_add, Complex.add_re]

theorem trace_product_nonneg {A B : Q d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let C := CFC.sqrt B
  have hC : C.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
  have hsq : C * C = B := by simpa [C, pow_two] using CFC.sq_sqrt B hB.nonneg
  have ht := (hA.mul_mul_conjTranspose_same C).trace_nonneg
  rw [hC.isHermitian, Matrix.trace_mul_cycle, hsq] at ht
  rw [Matrix.trace_mul_comm] at ht
  exact (Complex.nonneg_iff.mp ht).1

theorem effect_trace_le {B : Q d} (E : Effect d) (hB : B.PosSemidef) :
    (E.matrix * B).trace.re ≤ B.trace.re := by
  have h := trace_product_nonneg E.complement hB
  simpa only [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, sub_nonneg] using h

theorem spectral_upper_bound {A : Q d} (h : A.IsHermitian) (E : Effect d) :
    (E.matrix * A).trace.re ≤ (positive_part h).trace.re := by
  have hp := effect_trace_le E (positive_part_positive h)
  have hn := trace_product_nonneg E.positive (negative_part_positive h)
  have he : (E.matrix * A).trace.re =
      (E.matrix * positive_part h).trace.re - (E.matrix * negative_part h).trace.re := by
    rw [← Complex.sub_re, ← Matrix.trace_sub, ← mul_sub, parts_sub]
  linarith

def selector (pick : Fin d → Bool) (i : Fin d) : ℝ := if pick i then 1 else 0

def spectral_effect {A : Q d} (h : A.IsHermitian) (pick : Fin d → Bool) : Effect d where
  matrix := spectral_map h (selector pick)
  positive := spectral_map_positive h _ fun i => by simp [selector]; split <;> norm_num
  complement := by
    rw [← spectral_map_one h, ← spectral_map_sub]
    apply spectral_map_positive
    intro i
    simp only [Pi.sub_apply, Pi.one_apply, selector]
    split <;> norm_num

theorem spectral_effect_projector {A : Q d} (h : A.IsHermitian) (pick : Fin d → Bool) :
    (spectral_effect h pick).matrix * (spectral_effect h pick).matrix =
      (spectral_effect h pick).matrix := by
  change spectral_map h _ * spectral_map h _ = spectral_map h _
  rw [← spectral_map_mul]
  congr 1
  funext i
  simp [selector, Pi.mul_apply]

def OptimalSelector {A : Q d} (h : A.IsHermitian) (pick : Fin d → Bool) : Prop :=
  ∀ i, (0 < h.eigenvalues i → pick i = true) ∧ (h.eigenvalues i < 0 → pick i = false)

theorem spectral_effect_attains {A : Q d} (h : A.IsHermitian) (pick : Fin d → Bool)
    (hp : OptimalSelector h pick) :
    ((spectral_effect h pick).matrix * A).trace.re = (positive_part h).trace.re := by
  change (spectral_map h _ * A).trace.re = _
  conv_lhs => arg 1; arg 1; arg 2; rw [← spectral_map_eigenvalues h]
  rw [← spectral_map_mul, positive_part, spectral_map_trace, spectral_map_trace]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (h.eigenvalues i) 0 with hi | hi | hi
  · simp [Pi.mul_apply, selector, (hp i).2 hi, max_eq_right hi.le]
  · simp [Pi.mul_apply, hi]
  · simp [Pi.mul_apply, selector, (hp i).1 hi, max_eq_left hi.le]

def positive_selector {A : Q d} (h : A.IsHermitian) : Fin d → Bool :=
  fun i => decide (0 < h.eigenvalues i)

theorem positive_selector_optimal {A : Q d} (h : A.IsHermitian) :
    OptimalSelector h (positive_selector h) := by
  intro i
  constructor
  · intro hi; simp [positive_selector, hi]
  · intro hi; simp [positive_selector, not_lt_of_ge hi.le]

/-- Zero eigenspaces may be assigned independently to either outcome. -/
def zero_flexible_selector {A : Q d} (h : A.IsHermitian) (z : Fin d → Bool) : Fin d → Bool :=
  fun i => if h.eigenvalues i = 0 then z i else positive_selector h i

theorem zero_flexible_optimal {A : Q d} (h : A.IsHermitian) (z : Fin d → Bool) :
    OptimalSelector h (zero_flexible_selector h z) := by
  intro i
  constructor
  · intro hi; simp [zero_flexible_selector, ne_of_gt hi, positive_selector, hi]
  · intro hi; simp [zero_flexible_selector, ne_of_lt hi, positive_selector, not_lt_of_ge hi.le]

def helstrom_difference (p : Priors) (ρ σ : Q d) : Q d := (p.p₀ : ℂ) • ρ - (p.p₁ : ℂ) • σ

theorem difference_hermitian (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    (helstrom_difference p ρ σ).IsHermitian := by
  apply Matrix.IsHermitian.sub
  · exact hρ.1.isHermitian.smul (by simp [IsSelfAdjoint])
  · exact hσ.1.isHermitian.smul (by simp [IsSelfAdjoint])

theorem difference_trace (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    (helstrom_difference p ρ σ).trace.re = p.p₀ - p.p₁ := by
  simp [helstrom_difference, Matrix.trace_sub, Matrix.trace_smul, hρ.2, hσ.2]

def helstrom_succ_prob (p : Priors) (ρ σ E : Q d) : ℝ :=
  p.p₁ + (E * helstrom_difference p ρ σ).trace.re

theorem success_standard_form (p : Priors) (ρ σ E : Q d) (hσ : Density σ) :
    helstrom_succ_prob p ρ σ E =
      p.p₀ * (E * ρ).trace.re + p.p₁ * ((1 - E) * σ).trace.re := by
  simp [helstrom_succ_prob, helstrom_difference, mul_sub, sub_mul,
    Matrix.trace_sub, Matrix.trace_smul, hσ.2, Complex.mul_re]
  ring

def optimal_success (p : Priors) (ρ σ : Q d) : ℝ := (1 + trace_norm (helstrom_difference p ρ σ)) / 2

theorem helstrom_trace_norm_identity (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    p.p₁ + (positive_part (difference_hermitian p hρ hσ)).trace.re = optimal_success p ρ σ := by
  let h := difference_hermitian p hρ hσ
  have ht := congrArg (fun M : Q d => M.trace.re) (parts_sub h)
  simp only [Matrix.trace_sub, Complex.sub_re] at ht
  rw [difference_trace p hρ hσ] at ht
  rw [optimal_success, trace_norm_parts h]
  linarith [p.total]

theorem helstrom_upper_bound (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : Effect d) : helstrom_succ_prob p ρ σ E.matrix ≤ optimal_success p ρ σ := by
  rw [← helstrom_trace_norm_identity p hρ hσ]
  simpa only [helstrom_succ_prob, add_comm] using
    add_le_add_left (spectral_upper_bound (difference_hermitian p hρ hσ) E) p.p₁

def helstrom_effect (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) : Effect d :=
  spectral_effect (difference_hermitian p hρ hσ) (positive_selector (difference_hermitian p hρ hσ))

theorem helstrom_bound_achievable (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    helstrom_succ_prob p ρ σ (helstrom_effect p hρ hσ).matrix = optimal_success p ρ σ := by
  rw [helstrom_succ_prob, helstrom_effect, spectral_effect_attains _ _ (positive_selector_optimal
    _)]
  exact helstrom_trace_norm_identity p hρ hσ

theorem zero_eigenvalue_choice_irrelevant (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (z : Fin d → Bool) :
    helstrom_succ_prob p ρ σ (spectral_effect (difference_hermitian p hρ hσ)
      (zero_flexible_selector (difference_hermitian p hρ hσ) z)).matrix = optimal_success p ρ σ :=
        by
  rw [helstrom_succ_prob, spectral_effect_attains _ _ (zero_flexible_optimal _ _)]
  exact helstrom_trace_norm_identity p hρ hσ

/-- Classical decision probabilities, with ties assigned to hypothesis zero. -/
def decision_success (a b D : Fin m → ℝ) : ℝ := ∑ j, (D j * a j + (1-D j) * b j)
def guessing (a b : Fin m → ℝ) : ℝ := ∑ j, max (a j) (b j)
def bayes_rule (a b : Fin m → ℝ) : Fin m → ℝ := fun j => if b j ≤ a j then 1 else 0

theorem bayes_rule_valid (a b : Fin m → ℝ) (j : Fin m) :
    0 ≤ bayes_rule a b j ∧ bayes_rule a b j ≤ 1 := by
  unfold bayes_rule; split <;> norm_num

theorem bayes_decision_rule_optimal (a b D : Fin m → ℝ) (hD : ∀ j, 0 ≤ D j ∧ D j ≤ 1) :
    decision_success a b D ≤ guessing a b := by
  apply Finset.sum_le_sum
  intro j _
  have h₀ := mul_le_mul_of_nonneg_left (le_max_left (a j) (b j)) (hD j).1
  have h₁ := mul_le_mul_of_nonneg_left (le_max_right (a j) (b j)) (sub_nonneg.mpr (hD j).2)
  nlinarith

theorem bayes_rule_attains (a b : Fin m → ℝ) : decision_success a b (bayes_rule a b) = guessing a
  b := by
  apply Finset.sum_congr rfl
  intro j _
  unfold bayes_rule
  split <;> simp_all [le_of_lt]

theorem guessing_data_processing (M : ClassicalChannel m n) (a b : Fin m → ℝ) :
    guessing (apply_channel M a) (apply_channel M b) ≤ guessing a b := by
  calc
    _ ≤ ∑ k, ∑ j, M.matrix k j * max (a j) (b j) := by
      apply Finset.sum_le_sum
      intro k _
      apply max_le
      · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (M.nonneg k
        j)
      · exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (le_max_right _ _) (M.nonneg
        k j)
    _ = _ := by
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, M.col_sum_one, guessing]

def guessing_prob (p : Priors) (ρ σ : Q d) (E : FinitePOVM d m) : ℝ :=
  guessing (fun j => p.p₀ * prob_dist E ρ j) (fun j => p.p₁ * prob_dist E σ j)

theorem apply_weight (M : ClassicalChannel m n) (w : ℝ) (a : Fin m → ℝ) :
    apply_channel M (fun j => w*a j) = fun k => w * apply_channel M a k := by
  funext k
  simp only [apply_channel, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem guessing_prob_postprocessing_le (p : Priors) (ρ σ : Q d) (E : FinitePOVM d m)
    (M : ClassicalChannel m n) :
    guessing_prob p ρ σ (postprocess_povm M E) ≤ guessing_prob p ρ σ E := by
  simpa only [guessing_prob, postprocess_prob, apply_weight] using
    guessing_data_processing M (fun j => p.p₀ * prob_dist E ρ j) (fun j => p.p₁ * prob_dist E σ j)

theorem guessing_permutation (e : Fin m ≃ Fin m) (a b : Fin m → ℝ) :
    guessing (apply_channel (permutation_channel e).toClassicalChannel a)
      (apply_channel (permutation_channel e).toClassicalChannel b) = guessing a b := by
  rw [apply_permutation, apply_permutation]
  exact Equiv.sum_comp e (fun j => max (a j) (b j))

theorem guessing_erasure (p : Priors) {a b : Fin m → ℝ} (ha : IsDistribution a) (hb :
  IsDistribution b)
    (u : Fin n → ℝ) (hu : IsDistribution u) :
    guessing (fun k => p.p₀ * apply_channel (erasure_channel m u hu) a k)
      (fun k => p.p₁ * apply_channel (erasure_channel m u hu) b k) = max p.p₀ p.p₁ := by
  rw [apply_erasure ha, apply_erasure hb]
  unfold guessing
  simp_rw [← max_mul_of_nonneg _ _ (hu.1 _)]
  rw [← Finset.mul_sum, hu.2, mul_one]

def decision_effect (E : FinitePOVM d m) (D : Fin m → ℝ) (hD : ∀ j, 0 ≤ D j ∧ D j ≤ 1) : Effect d
  where
  matrix := ∑ j, (D j : ℂ) • E.effects j
  positive := Matrix.posSemidef_sum _ fun j _ => (E.pos_semidef j).smul (by simpa
    [Complex.nonneg_iff] using (hD j).1)
  complement := by
    have he : 1 - ∑ j, (D j : ℂ) • E.effects j = ∑ j, ((1-D j : ℝ) : ℂ) • E.effects j := by
      rw [← E.completeness, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      simp [sub_smul]
    rw [he]
    exact Matrix.posSemidef_sum _ fun j _ => (E.pos_semidef j).smul (by
      simpa only [Complex.nonneg_iff, Complex.ofReal_re, Complex.ofReal_im, and_true] using
        sub_nonneg.mpr (hD j).2)

theorem decision_effect_success (p : Priors) (ρ σ : Q d) (hσ : Density σ)
    (E : FinitePOVM d m) (D : Fin m → ℝ) (hD : ∀ j, 0 ≤ D j ∧ D j ≤ 1) :
    helstrom_succ_prob p ρ σ (decision_effect E D hD).matrix =
      decision_success (fun j => p.p₀ * prob_dist E ρ j) (fun j => p.p₁ * prob_dist E σ j) D := by
  have hs := (prob_dist_isDistribution E σ hσ).2
  simp only [helstrom_succ_prob, decision_effect, helstrom_difference, Finset.sum_mul,
    Matrix.trace_sum, Complex.re_sum, mul_sub, Matrix.trace_sub, Complex.sub_re,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  simp_rw [Matrix.trace_mul_comm (E.effects _) ρ, Matrix.trace_mul_comm (E.effects _) σ]
  simp only [decision_success, prob_dist, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sub_mul, one_mul, ← Finset.mul_sum]
  simp only [prob_dist] at hs
  rw [hs]
  ring_nf
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem guessing_prob_le_helstrom (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : FinitePOVM d m) : guessing_prob p ρ σ E ≤ optimal_success p ρ σ := by
  let a := fun j => p.p₀ * prob_dist E ρ j
  let b := fun j => p.p₁ * prob_dist E σ j
  have h := helstrom_upper_bound p hρ hσ (decision_effect E (bayes_rule a b) (bayes_rule_valid a b))
  rw [decision_effect_success p ρ σ hσ, bayes_rule_attains] at h
  exact h

def zero_effect (d : ℕ) : Effect d := ⟨0, Matrix.PosSemidef.zero, by simpa using
  Matrix.PosSemidef.one⟩
def one_effect (d : ℕ) : Effect d := ⟨1, Matrix.PosSemidef.one, by simpa using
  Matrix.PosSemidef.zero⟩

theorem success_zero (p : Priors) (ρ σ : Q d) : helstrom_succ_prob p ρ σ (zero_effect d).matrix =
  p.p₁ := by
  simp [helstrom_succ_prob, zero_effect]

theorem success_one (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    helstrom_succ_prob p ρ σ (one_effect d).matrix = p.p₀ := by
  simp only [helstrom_succ_prob, one_effect, one_mul, difference_trace p hρ hσ]
  ring

theorem success_le_one (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) (E : Effect d) :
    helstrom_succ_prob p ρ σ E.matrix ≤ 1 := by
  rw [success_standard_form p ρ σ E.matrix hσ]
  have h₀ := effect_trace_le E hρ.1
  have h₁ := effect_trace_le (Effect.mk (1-E.matrix) E.complement (by simpa using E.positive)) hσ.1
  simp only [hρ.2, hσ.2, Complex.one_re] at h₀ h₁
  have hp₀ := mul_le_mul_of_nonneg_left h₀ p.nonneg₀
  have hp₁ := mul_le_mul_of_nonneg_left h₁ p.nonneg₁
  linarith [p.total]

theorem optimal_success_le_one (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    optimal_success p ρ σ ≤ 1 := by
  rw [← helstrom_bound_achievable p hρ hσ]
  exact success_le_one p hρ hσ _

theorem prior_lower_bound (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    max p.p₀ p.p₁ ≤ optimal_success p ρ σ := by
  apply max_le
  · simpa only [success_one p hρ hσ] using helstrom_upper_bound p hρ hσ (one_effect d)
  · simpa only [success_zero] using helstrom_upper_bound p hρ hσ (zero_effect d)

theorem identical_states_optimum (p : Priors) {ρ : Q d} (hρ : Density ρ) :
    optimal_success p ρ ρ = max p.p₀ p.p₁ := by
  apply le_antisymm _ (prior_lower_bound p hρ hρ)
  rw [← helstrom_bound_achievable p hρ hρ, success_standard_form p ρ ρ _ hρ]
  let E := helstrom_effect p hρ hρ
  have h₀ := trace_product_nonneg E.positive hρ.1
  have h₁ := effect_trace_le E hρ.1
  rw [hρ.2] at h₁
  simp only [sub_mul, one_mul, Matrix.trace_sub, hρ.2, Complex.sub_re, Complex.one_re]
  have hm₀ := mul_le_mul_of_nonneg_right (le_max_left p.p₀ p.p₁) h₀
  have hm₁ := mul_le_mul_of_nonneg_right (le_max_right p.p₀ p.p₁) (sub_nonneg.mpr h₁)
  dsimp [E] at hm₀ hm₁
  nlinarith

theorem zero_prior_optimum (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (hp : p.p₀ = 0 ∨ p.p₁ = 0) : optimal_success p ρ σ = 1 := by
  have hlo := prior_lower_bound p hρ hσ
  have hhi := optimal_success_le_one p hρ hσ
  rcases hp with hp | hp
  · have : p.p₁ = 1 := by linarith [p.total]
    exact le_antisymm hhi (by simpa [hp, this] using hlo)
  · have : p.p₀ = 1 := by linarith [p.total]
    exact le_antisymm hhi (by simpa [hp, this] using hlo)

namespace Examples

def fair : Priors := ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num⟩
def rhoOne : Q 2 := !![0, 0; 0, 1]
def rhoPlus : Q 2 := !![1/2, 1/2; 1/2, 1/2]

theorem rhoOne_density : Density rhoOne := by
  have heq : rhoOne = pauliZ.effects 1 := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  refine ⟨heq ▸ pauliZ.pos_semidef 1, ?_⟩
  norm_num [rhoOne, Matrix.trace, Fin.sum_univ_succ]

theorem rhoPlus_density : Density rhoPlus := by
  have heq : rhoPlus = pauliX.effects 0 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [rhoPlus, pauliX, QuantumPOVMInformationallyComplete.phasePlus,
        QuantumPOVMInformationallyComplete.blochEffect]
  refine ⟨heq ▸ pauliX.pos_semidef 0, ?_⟩
  norm_num [rhoPlus, Matrix.trace, Fin.sum_univ_succ]

theorem noncommuting_states : qubitZero * rhoPlus ≠ rhoPlus * qubitZero := by
  intro h
  have := congrArg (fun M : Q 2 => M 0 1) h
  norm_num [qubitZero, rhoPlus, Matrix.mul_apply, Fin.sum_univ_succ] at this

def z_effect : Effect 2 := ⟨qubitZero, qubitZero_density.1, by
  convert rhoOne_density.1 using 1
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [qubitZero, rhoOne, Matrix.one_apply]⟩

theorem orthogonal_success (p : Priors) : helstrom_succ_prob p qubitZero rhoOne z_effect.matrix =
  1 := by
  rw [success_standard_form p _ _ _ rhoOne_density]
  norm_num [z_effect, qubitZero, rhoOne, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.one_apply]
  exact p.total

theorem orthogonal_optimum (p : Priors) : optimal_success p qubitZero rhoOne = 1 := by
  apply le_antisymm (optimal_success_le_one p qubitZero_density rhoOne_density)
  simpa only [orthogonal_success] using helstrom_upper_bound p qubitZero_density rhoOne_density
    z_effect

theorem orthogonal_trace_norm (p : Priors) : trace_norm (helstrom_difference p qubitZero rhoOne) =
  1 := by
  have := orthogonal_optimum p
  unfold optimal_success at this
  linarith

theorem qubit_delta : helstrom_difference fair qubitZero rhoPlus = !![1/4, -1/4; -1/4, -1/4] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    norm_num [helstrom_difference, fair, qubitZero, rhoPlus]

theorem noncommuting_trace_norm : trace_norm (helstrom_difference fair qubitZero rhoPlus) = 1 /
  Real.sqrt 2 := by
  let t : ℝ := 1 / (2 * Real.sqrt 2)
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have ht : 0 ≤ t := le_of_lt (one_div_pos.mpr (mul_pos (by norm_num) hs))
  have ht2 : t * t = 1/8 := by
    dsimp [t]
    have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    field_simp
    nlinarith
  have hc2 : (t : ℂ) * (t : ℂ) = 1/8 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
      using
      congrArg (fun x : ℝ => (x : ℂ)) ht2
  have hroot : CFC.sqrt ((helstrom_difference fair qubitZero rhoPlus).conjTranspose *
      helstrom_difference fair qubitZero rhoPlus) = (t : ℂ) • (1 : Q 2) := by
    apply CFC.sqrt_unique
    · rw [qubit_delta]
      ext i j; fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply,
          Matrix.conjTranspose_apply, hc2, map_ofNat]
    · exact (Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ t by simpa [Complex.nonneg_iff] using
      ht)).nonneg
  rw [trace_norm, hroot]
  norm_num [Matrix.trace_smul, Matrix.trace, Fin.sum_univ_two, Matrix.one_apply, t, Complex.mul_re]
  field_simp
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

theorem noncommuting_optimum : optimal_success fair qubitZero rhoPlus = (1 + 1 / Real.sqrt 2) / 2
  := by
  rw [optimal_success, noncommuting_trace_norm]

def bit_flip : ClassicalChannel 2 2 := (permutation_channel (Equiv.swap 0 1)).toClassicalChannel

theorem z_orthogonal_distributions : prob_dist pauliZ qubitZero = ![1,0] ∧ prob_dist pauliZ rhoOne
  = ![0,1] := by
  constructor <;> ext j <;> fin_cases j <;>
    norm_num [prob_dist, pauliZ, QuantumPOVMInformationallyComplete.basisPOVM,
      qubitZero, rhoOne, Matrix.trace, Matrix.mul_apply, Matrix.vecMul, dotProduct,
        Fin.sum_univ_two]

/-- The fixed rule is deliberately reversed; flipping observations repairs it. -/
theorem suboptimal_rule_can_improve_counterexample :
    decision_success (fun j => fair.p₀ * prob_dist pauliZ qubitZero j)
      (fun j => fair.p₁ * prob_dist pauliZ rhoOne j) ![0,1] = 0 ∧
    decision_success (fun j => fair.p₀ * prob_dist (postprocess_povm bit_flip pauliZ) qubitZero j)
      (fun j => fair.p₁ * prob_dist (postprocess_povm bit_flip pauliZ) rhoOne j) ![0,1] = 1 := by
  rw [postprocess_prob, postprocess_prob, z_orthogonal_distributions.1,
    z_orthogonal_distributions.2]
  norm_num [decision_success, fair, bit_flip, apply_permutation, Fin.sum_univ_two,
    Equiv.swap_apply_def]

end Examples

def effect_povm (E : Effect d) : FinitePOVM d 2 where
  effects := ![E.matrix, 1-E.matrix]
  pos_semidef j := by
    fin_cases j
    · exact E.positive
    · exact E.complement
  completeness := by simp [Fin.sum_univ_two]

theorem helstrom_effect_projective (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    (helstrom_effect p hρ hσ).matrix * (helstrom_effect p hρ hσ).matrix =
      (helstrom_effect p hρ hσ).matrix := spectral_effect_projector _ _

/-- Upper bound and membership establish a genuine attained maximum. -/
theorem helstrom_isGreatest (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    IsGreatest {s : ℝ | ∃ E : Effect d, helstrom_succ_prob p ρ σ E.matrix = s}
      (optimal_success p ρ σ) := by
  refine ⟨⟨helstrom_effect p hρ hσ, helstrom_bound_achievable p hρ hσ⟩, ?_⟩
  rintro s ⟨E, rfl⟩
  exact helstrom_upper_bound p hρ hσ E

theorem guessing_prob_permutation (p : Priors) (ρ σ : Q d) (E : FinitePOVM d m)
    (e : Fin m ≃ Fin m) :
    guessing_prob p ρ σ (postprocess_povm (permutation_channel e).toClassicalChannel E) =
      guessing_prob p ρ σ E := by
  simpa only [guessing_prob, postprocess_prob, apply_weight] using
    guessing_permutation e (fun j => p.p₀ * prob_dist E ρ j) (fun j => p.p₁ * prob_dist E σ j)

theorem guessing_prob_erasure (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : FinitePOVM d m) (u : Fin n → ℝ) (hu : IsDistribution u) :
    guessing_prob p ρ σ (postprocess_povm (erasure_channel m u hu) E) = max p.p₀ p.p₁ := by
  simp only [guessing_prob, postprocess_prob]
  exact guessing_erasure p (prob_dist_isDistribution E ρ hρ) (prob_dist_isDistribution E σ hσ) u hu

theorem identical_fair_nonunique :
    (zero_effect 2).matrix ≠ (one_effect 2).matrix ∧
    helstrom_succ_prob Examples.fair qubitZero qubitZero (zero_effect 2).matrix =
      optimal_success Examples.fair qubitZero qubitZero ∧
    helstrom_succ_prob Examples.fair qubitZero qubitZero (one_effect 2).matrix =
      optimal_success Examples.fair qubitZero qubitZero := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun M : Q 2 => M 0 0) h
    norm_num [zero_effect, one_effect] at this
  · rw [success_zero, identical_states_optimum _ qubitZero_density]
    norm_num [Examples.fair]
  · rw [success_one _ qubitZero_density qubitZero_density, identical_states_optimum _
    qubitZero_density]
    norm_num [Examples.fair]

structure QuantumHelstromStateDiscriminationSuite : Prop where
  spectral_norm : ∀ {d} {A : Q d} (h : A.IsHermitian), trace_norm A = ∑ i, |h.eigenvalues i|
  maximum : ∀ {d} (p : Priors) {ρ σ : Q d}, Density ρ → Density σ →
    IsGreatest {s : ℝ | ∃ E : Effect d, helstrom_succ_prob p ρ σ E.matrix = s} (optimal_success p
      ρ σ)
  projective : ∀ {d} (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ),
    (helstrom_effect p hρ hσ).matrix * (helstrom_effect p hρ hσ).matrix = (helstrom_effect p hρ
      hσ).matrix
  zero_choices : ∀ {d} (p : Priors) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) (z : Fin d →
    Bool),
    helstrom_succ_prob p ρ σ (spectral_effect (difference_hermitian p hρ hσ)
      (zero_flexible_selector (difference_hermitian p hρ hσ) z)).matrix = optimal_success p ρ σ
  bayes : ∀ {m} (a b D : Fin m → ℝ), (∀ j, 0 ≤ D j ∧ D j ≤ 1) → decision_success a b D ≤ guessing
    a b
  bayes_attained : ∀ {m} (a b : Fin m → ℝ), decision_success a b (bayes_rule a b) = guessing a b
  processing : ∀ {d m n} (p : Priors) (ρ σ : Q d) (E : FinitePOVM d m) (M : ClassicalChannel m n),
    guessing_prob p ρ σ (postprocess_povm M E) ≤ guessing_prob p ρ σ E
  measurement_bound : ∀ {d m} (p : Priors) {ρ σ : Q d}, Density ρ → Density σ →
    ∀ E : FinitePOVM d m, guessing_prob p ρ σ E ≤ optimal_success p ρ σ
  noncommuting : qubitZero * Examples.rhoPlus ≠ Examples.rhoPlus * qubitZero ∧
    optimal_success Examples.fair qubitZero Examples.rhoPlus = (1 + 1 / Real.sqrt 2) / 2

theorem verification_suite : QuantumHelstromStateDiscriminationSuite where
  spectral_norm := trace_norm_spectral
  maximum := helstrom_isGreatest
  projective := helstrom_effect_projective
  zero_choices := zero_eigenvalue_choice_irrelevant
  bayes := bayes_decision_rule_optimal
  bayes_attained := bayes_rule_attains
  processing := guessing_prob_postprocessing_le
  measurement_bound := guessing_prob_le_helstrom
  noncommuting := ⟨Examples.noncommuting_states, Examples.noncommuting_optimum⟩

end QuantumHelstromStateDiscrimination
