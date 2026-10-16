/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMNaimarkDilation
import Verification.QuantumPOVMInformationEntropy
import Verification.QuantumChannelClassicalDataProcessing
import Verification.QuantumHelstromStateDiscrimination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Trace distance on density matrices, attained effect optimization, and measurement TV.
No general quantum channel or numerical spectral algorithm is modeled here. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumChannelClassicalDataProcessing QuantumHelstromStateDiscrimination
namespace QuantumChannelTraceDistanceContract
variable {d m n : ℕ}

def trace_distance (ρ σ : Q d) : ℝ := (1 / 2) * trace_norm (ρ - σ)
def TV (p q : Fin m → ℝ) : ℝ := (1 / 2) * ∑ j, |p j - q j|

theorem hermitian_trace_norm_nonneg {A : Q d} (h : A.IsHermitian) : 0 ≤ trace_norm A := by
  rw [trace_norm_spectral h]
  exact Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem hermitian_trace_norm_zero_iff {A : Q d} (h : A.IsHermitian) :
    trace_norm A = 0 ↔ A = 0 := by
  constructor
  · intro hz
    rw [trace_norm_spectral h] at hz
    have he : h.eigenvalues = 0 := by
      funext i
      have hi : |h.eigenvalues i| = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (h.eigenvalues j))).mp hz i
          (Finset.mem_univ i)
      exact abs_eq_zero.mp hi
    rw [← spectral_map_eigenvalues h, he, spectral_map_zero]
  · rintro rfl
    simp [trace_norm]

theorem traceless_positive_trace {A : Q d} (h : A.IsHermitian) (ht : A.trace.re = 0) :
    (positive_part h).trace.re = (1 / 2) * trace_norm A := by
  have hp := congrArg (fun B : Q d => B.trace.re) (parts_sub h)
  simp only [Matrix.trace_sub, Complex.sub_re, ht] at hp
  rw [trace_norm_parts h]
  linarith

def complement_effect (E : Effect d) : Effect d where
  matrix := 1 - E.matrix
  positive := E.complement
  complement := by simpa using E.positive

theorem traceless_effect_bound {A : Q d} (h : A.IsHermitian) (ht : A.trace.re = 0)
    (E : Effect d) : |(E.matrix * A).trace.re| ≤ (1 / 2) * trace_norm A := by
  have hp := spectral_upper_bound h E
  have hn := spectral_upper_bound h (complement_effect E)
  rw [traceless_positive_trace h ht] at hp hn
  simp only [complement_effect, sub_mul, one_mul, Matrix.trace_sub, Complex.sub_re, ht,
    zero_sub] at hn
  exact abs_le.mpr ⟨by linarith, hp⟩

def distance_effect {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) : Effect d :=
  spectral_effect (hρ.1.isHermitian.sub hσ.1.isHermitian)
    (positive_selector (hρ.1.isHermitian.sub hσ.1.isHermitian))

theorem difference_traceless {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    (ρ - σ).trace.re = 0 := by simp [Matrix.trace_sub, hρ.2, hσ.2]

theorem trace_distance_nonneg {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    0 ≤ trace_distance ρ σ :=
  mul_nonneg (by norm_num) (hermitian_trace_norm_nonneg (hρ.1.isHermitian.sub hσ.1.isHermitian))

theorem trace_distance_effect_bound {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : Effect d) : |(E.matrix * (ρ - σ)).trace.re| ≤ trace_distance ρ σ :=
  traceless_effect_bound (hρ.1.isHermitian.sub hσ.1.isHermitian) (difference_traceless hρ hσ) E

theorem distance_effect_attains {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    ((distance_effect hρ hσ).matrix * (ρ - σ)).trace.re = trace_distance ρ σ := by
  rw [distance_effect, spectral_effect_attains _ _ (positive_selector_optimal _),
    traceless_positive_trace _ (difference_traceless hρ hσ)]
  rfl

theorem distance_effect_projective {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    (distance_effect hρ hσ).matrix * (distance_effect hρ hσ).matrix =
      (distance_effect hρ hσ).matrix := spectral_effect_projector _ _

/-- A genuine attained maximum, with no assumed optimizer or compactness oracle. -/
theorem trace_distance_variational_sup {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    IsGreatest {x : ℝ | ∃ E : Effect d, |(E.matrix * (ρ - σ)).trace.re| = x}
      (trace_distance ρ σ) := by
  refine ⟨⟨distance_effect hρ hσ, ?_⟩, ?_⟩
  · rw [distance_effect_attains, abs_of_nonneg (trace_distance_nonneg hρ hσ)]
  · rintro x ⟨E, rfl⟩
    exact trace_distance_effect_bound hρ hσ E

theorem trace_distance_symm {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    trace_distance ρ σ = trace_distance σ ρ := by
  have aux : ∀ {a b : Q d}, Density a → Density b → trace_distance a b ≤ trace_distance b a := by
    intro a b ha hb
    have h := trace_distance_effect_bound hb ha (distance_effect ha hb)
    have he : b - a = -(a - b) := by abel
    rw [he, mul_neg, Matrix.trace_neg, Complex.neg_re, abs_neg, distance_effect_attains,
      abs_of_nonneg (trace_distance_nonneg ha hb)] at h
    exact h
  exact le_antisymm (aux hρ hσ) (aux hσ hρ)

theorem trace_distance_eq_zero_iff {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    trace_distance ρ σ = 0 ↔ ρ = σ := by
  rw [trace_distance, mul_eq_zero]
  norm_num only [one_div, inv_eq_zero, OfNat.ofNat_ne_zero, false_or]
  rw [hermitian_trace_norm_zero_iff (hρ.1.isHermitian.sub hσ.1.isHermitian), sub_eq_zero]

theorem trace_distance_self (ρ : Q d) : trace_distance ρ ρ = 0 := by
  simp [trace_distance, trace_norm]

theorem trace_distance_triangle {ρ σ τ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (hτ : Density τ) : trace_distance ρ σ ≤ trace_distance ρ τ + trace_distance τ σ := by
  let E := distance_effect hρ hσ
  have h₁ := trace_distance_effect_bound hρ hτ E
  have h₂ := trace_distance_effect_bound hτ hσ E
  have he : (E.matrix * (ρ - σ)).trace.re =
      (E.matrix * (ρ - τ)).trace.re + (E.matrix * (τ - σ)).trace.re := by
    rw [← Complex.add_re, ← Matrix.trace_add, ← mul_add]
    congr 3
    abel
  have hatt := distance_effect_attains hρ hσ
  change (E.matrix * (ρ - σ)).trace.re = _ at hatt
  rw [he] at hatt
  linarith [le_abs_self ((E.matrix * (ρ - τ)).trace.re),
    le_abs_self ((E.matrix * (τ - σ)).trace.re)]

theorem trace_distance_le_one {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    trace_distance ρ σ ≤ 1 := by
  let E := distance_effect hρ hσ
  have h₁ := effect_trace_le E hρ.1
  have h₂ := trace_product_nonneg E.positive hσ.1
  have he := distance_effect_attains hρ hσ
  change (E.matrix * (ρ - σ)).trace.re = _ at he
  simp only [mul_sub, Matrix.trace_sub, Complex.sub_re] at he
  rw [hρ.2] at h₁
  norm_num only [Complex.one_re] at h₁
  linarith

theorem fair_success_formula (ρ σ : Q d) (E : Effect d) :
    helstrom_succ_prob Examples.fair ρ σ E.matrix =
      (1 + (E.matrix * (ρ - σ)).trace.re) / 2 := by
  simp only [helstrom_succ_prob, helstrom_difference, Examples.fair, mul_sub,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, Complex.sub_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

theorem trace_distance_helstrom_link {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    optimal_success Examples.fair ρ σ = (1 + trace_distance ρ σ) / 2 := by
  have hl := helstrom_upper_bound Examples.fair hρ hσ (distance_effect hρ hσ)
  rw [fair_success_formula, distance_effect_attains] at hl
  have hu := trace_distance_effect_bound hρ hσ (helstrom_effect Examples.fair hρ hσ)
  have ha := helstrom_bound_achievable Examples.fair hρ hσ
  rw [fair_success_formula] at ha
  have hab := le_abs_self (((helstrom_effect Examples.fair hρ hσ).matrix * (ρ - σ)).trace.re)
  linarith

theorem tv_nonneg (p q : Fin m → ℝ) : 0 ≤ TV p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem tv_self (p : Fin m → ℝ) : TV p p = 0 := by simp [TV]

theorem tv_symm (p q : Fin m → ℝ) : TV p q = TV q p := by
  simp only [TV, abs_sub_comm]

theorem tv_eq_zero_iff (p q : Fin m → ℝ) : TV p q = 0 ↔ p = q := by
  constructor
  · intro h
    have hs : ∑ j, |p j - q j| = 0 := by unfold TV at h; linarith
    funext j
    exact sub_eq_zero.mp (abs_eq_zero.mp
      ((Finset.sum_eq_zero_iff_of_nonneg (fun i _ => abs_nonneg (p i - q i))).mp hs j
        (Finset.mem_univ j)))
  · rintro rfl
    exact tv_self p

theorem tv_triangle (p q r : Fin m → ℝ) : TV p q ≤ TV p r + TV r q := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => abs_sub_le (p j) (r j) (q j))
  rw [Finset.sum_add_distrib] at h
  unfold TV
  linarith

theorem tv_le_one {p q : Fin m → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    TV p q ≤ 1 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    abs_sub_le (p j) 0 (q j))
  simp only [sub_zero, zero_sub, abs_neg, abs_of_nonneg (hp.1 _),
    abs_of_nonneg (hq.1 _), Finset.sum_add_distrib, hp.2, hq.2] at h
  unfold TV
  linarith

/-- This algebraic contraction also holds for unnormalized real input vectors. -/
theorem tv_contractive_under_classical_channel (M : ClassicalChannel m n) (p q : Fin m → ℝ) :
    TV (apply_channel M p) (apply_channel M q) ≤ TV p q := by
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    ∑ k, |apply_channel M p k - apply_channel M q k| ≤
        ∑ k, ∑ j, M.matrix k j * |p j - q j| := by
      apply Finset.sum_le_sum
      intro k _
      simp only [apply_channel, ← Finset.sum_sub_distrib, ← mul_sub]
      calc
        |∑ j, M.matrix k j * (p j - q j)| ≤ ∑ j, |M.matrix k j * (p j - q j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul, abs_of_nonneg (M.nonneg _ _)]
    _ = ∑ j, |p j - q j| := by
      rw [Finset.sum_comm]
      simp [← Finset.sum_mul, M.col_sum_one]

theorem fair_guessing_tv {p q : Fin m → ℝ} (hp : IsDistribution p) (hq : IsDistribution q) :
    guessing (fun j => (1 / 2) * p j) (fun j => (1 / 2) * q j) = (1 + TV p q) / 2 := by
  have he : ∀ a b : ℝ, max ((1 / 2) * a) ((1 / 2) * b) = (a + b + |a - b|) / 4 := by
    intro a b
    rcases le_total a b with h | h
    · rw [max_eq_right (by linarith), abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [max_eq_left (by linarith), abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  calc
    _ = ∑ j, (p j + q j + |p j - q j|) / 4 := Finset.sum_congr rfl fun j _ => he _ _
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, hp.2, hq.2]
      unfold TV
      ring

theorem tv_le_trace_distance_under_povm {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : FinitePOVM d m) : TV (prob_dist E ρ) (prob_dist E σ) ≤ trace_distance ρ σ := by
  have h := guessing_prob_le_helstrom Examples.fair hρ hσ E
  rw [trace_distance_helstrom_link hρ hσ] at h
  change guessing (fun j => (1 / 2) * prob_dist E ρ j)
    (fun j => (1 / 2) * prob_dist E σ j) ≤ _ at h
  rw [fair_guessing_tv (prob_dist_isDistribution E ρ hρ) (prob_dist_isDistribution E σ hσ)] at h
  linarith

theorem effect_povm_prob_zero (E : Effect d) (ρ : Q d) :
    prob_dist (effect_povm E) ρ 0 = (E.matrix * ρ).trace.re := by
  change (ρ * E.matrix).trace.re = _
  rw [Matrix.trace_mul_comm]

theorem effect_povm_prob_one (E : Effect d) {ρ : Q d} (hρ : Density ρ) :
    prob_dist (effect_povm E) ρ 1 = 1 - (E.matrix * ρ).trace.re := by
  change (ρ * (1 - E.matrix)).trace.re = _
  rw [mul_sub, mul_one, Matrix.trace_sub, Complex.sub_re, hρ.2, Matrix.trace_mul_comm]
  rfl

theorem effect_povm_tv {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) (E : Effect d) :
    TV (prob_dist (effect_povm E) ρ) (prob_dist (effect_povm E) σ) =
      |(E.matrix * (ρ - σ)).trace.re| := by
  rw [TV, Fin.sum_univ_two, effect_povm_prob_zero, effect_povm_prob_zero,
    effect_povm_prob_one E hρ, effect_povm_prob_one E hσ]
  have he : (1 - (E.matrix * ρ).trace.re) - (1 - (E.matrix * σ).trace.re) =
      -((E.matrix * ρ).trace.re - (E.matrix * σ).trace.re) := by ring
  rw [he, abs_neg, mul_sub, Matrix.trace_sub, Complex.sub_re]
  ring

def optimal_povm {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) : FinitePOVM d 2 :=
  effect_povm (distance_effect hρ hσ)

theorem tv_attains_trace_distance {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    TV (prob_dist (optimal_povm hρ hσ) ρ) (prob_dist (optimal_povm hρ hσ) σ) =
      trace_distance ρ σ := by
  rw [optimal_povm, effect_povm_tv hρ hσ, distance_effect_attains,
    abs_of_nonneg (trace_distance_nonneg hρ hσ)]

theorem tv_postprocess_le {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : FinitePOVM d m) (M : ClassicalChannel m n) :
    TV (prob_dist (postprocess_povm M E) ρ) (prob_dist (postprocess_povm M E) σ) ≤
      trace_distance ρ σ := by
  rw [postprocess_prob, postprocess_prob]
  exact (tv_contractive_under_classical_channel M _ _).trans
    (tv_le_trace_distance_under_povm hρ hσ E)

theorem tv_permutation (e : Fin m ≃ Fin m) (p q : Fin m → ℝ) :
    TV (apply_channel (permutation_channel e).toClassicalChannel p)
      (apply_channel (permutation_channel e).toClassicalChannel q) = TV p q := by
  rw [apply_permutation, apply_permutation]
  unfold TV
  congr 1
  exact Equiv.sum_comp e (fun j => |p j - q j|)

theorem tv_erasure {p q : Fin m → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (u : Fin n → ℝ) (hu : IsDistribution u) :
    TV (apply_channel (erasure_channel m u hu) p)
      (apply_channel (erasure_channel m u hu) q) = 0 := by
  rw [apply_erasure hp, apply_erasure hq, tv_self]

theorem measurement_tv_permutation (e : Fin m ≃ Fin m) (E : FinitePOVM d m) (ρ σ : Q d) :
    TV (prob_dist (postprocess_povm (permutation_channel e).toClassicalChannel E) ρ)
      (prob_dist (postprocess_povm (permutation_channel e).toClassicalChannel E) σ) =
      TV (prob_dist E ρ) (prob_dist E σ) := by
  rw [postprocess_prob, postprocess_prob, tv_permutation]

theorem measurement_tv_erasure {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ)
    (E : FinitePOVM d m) (u : Fin n → ℝ) (hu : IsDistribution u) :
    TV (prob_dist (postprocess_povm (erasure_channel m u hu) E) ρ)
      (prob_dist (postprocess_povm (erasure_channel m u hu) E) σ) = 0 := by
  rw [postprocess_prob, postprocess_prob]
  exact tv_erasure (prob_dist_isDistribution E ρ hρ) (prob_dist_isDistribution E σ hσ) u hu

namespace Regression
open QuantumHelstromStateDiscrimination.Examples

theorem orthogonal_distance : trace_distance qubitZero rhoOne = 1 := by
  have h := trace_distance_helstrom_link qubitZero_density rhoOne_density
  rw [orthogonal_optimum] at h
  linarith

theorem noncommuting_distance : trace_distance qubitZero rhoPlus = 1 / Real.sqrt 2 := by
  have h := trace_distance_helstrom_link qubitZero_density rhoPlus_density
  rw [noncommuting_optimum] at h
  linarith

theorem uninformative_measurement_zero {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    TV (prob_dist (effect_povm (zero_effect d)) ρ)
      (prob_dist (effect_povm (zero_effect d)) σ) = 0 := by
  rw [effect_povm_tv hρ hσ]
  simp [QuantumHelstromStateDiscrimination.zero_effect]

theorem strict_measurement_loss :
    TV (prob_dist (effect_povm (zero_effect 2)) qubitZero)
      (prob_dist (effect_povm (zero_effect 2)) rhoOne) < trace_distance qubitZero rhoOne := by
  rw [uninformative_measurement_zero qubitZero_density rhoOne_density, orthogonal_distance]
  norm_num

theorem z_measurement_noncommuting_loss :
    TV (prob_dist pauliZ qubitZero) (prob_dist pauliZ rhoPlus) = 1 / 2 ∧
      TV (prob_dist pauliZ qubitZero) (prob_dist pauliZ rhoPlus) <
        trace_distance qubitZero rhoPlus := by
  have he : TV (prob_dist pauliZ qubitZero) (prob_dist pauliZ rhoPlus) = 1 / 2 := by
    norm_num [TV, prob_dist, pauliZ, qubitZero, rhoPlus, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, QuantumPOVMInformationallyComplete.basisPOVM,
      Matrix.vecMul, dotProduct]
  refine ⟨he, ?_⟩
  rw [he, noncommuting_distance]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  apply (lt_div_iff₀ hp).mpr
  nlinarith

end Regression

/-- The binary spectral measurement attains the maximum over every finite POVM. -/
theorem measurement_tv_isGreatest {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    IsGreatest {x : ℝ | ∃ m, ∃ E : FinitePOVM d m, TV (prob_dist E ρ) (prob_dist E σ) = x}
      (trace_distance ρ σ) := by
  refine ⟨⟨2, optimal_povm hρ hσ, tv_attains_trace_distance hρ hσ⟩, ?_⟩
  rintro x ⟨m, E, rfl⟩
  exact tv_le_trace_distance_under_povm hρ hσ E

structure QuantumChannelTraceDistanceContractSuite : Prop where
  nonnegative : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ → 0 ≤ trace_distance ρ σ
  symmetric : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ → trace_distance ρ σ = trace_distance σ ρ
  separates : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ → (trace_distance ρ σ = 0 ↔ ρ = σ)
  triangle : ∀ {d} {ρ σ τ : Q d}, Density ρ → Density σ → Density τ →
    trace_distance ρ σ ≤ trace_distance ρ τ + trace_distance τ σ
  unit_bound : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ → trace_distance ρ σ ≤ 1
  helstrom : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ →
    optimal_success Examples.fair ρ σ = (1 + trace_distance ρ σ) / 2
  variational : ∀ {d} {ρ σ : Q d}, Density ρ → Density σ →
    IsGreatest {x : ℝ | ∃ E : Effect d, |(E.matrix * (ρ - σ)).trace.re| = x} (trace_distance ρ σ)
  projective : ∀ {d} {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ),
    (distance_effect hρ hσ).matrix * (distance_effect hρ hσ).matrix = (distance_effect hρ hσ).matrix
  measurement : ∀ {d m} {ρ σ : Q d}, Density ρ → Density σ → ∀ E : FinitePOVM d m,
    TV (prob_dist E ρ) (prob_dist E σ) ≤ trace_distance ρ σ
  attained : ∀ {d} {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ),
    TV (prob_dist (optimal_povm hρ hσ) ρ) (prob_dist (optimal_povm hρ hσ) σ) = trace_distance ρ σ
  classical : ∀ {m n} (M : ClassicalChannel m n) (p q : Fin m → ℝ),
    TV (apply_channel M p) (apply_channel M q) ≤ TV p q
  noncommuting : trace_distance qubitZero Examples.rhoPlus = 1 / Real.sqrt 2
  strict_loss : TV (prob_dist (effect_povm (QuantumHelstromStateDiscrimination.zero_effect 2))
    qubitZero) (prob_dist (effect_povm (QuantumHelstromStateDiscrimination.zero_effect 2))
      Examples.rhoOne) < trace_distance qubitZero Examples.rhoOne

theorem verification_suite : QuantumChannelTraceDistanceContractSuite where
  nonnegative := trace_distance_nonneg
  symmetric := trace_distance_symm
  separates := trace_distance_eq_zero_iff
  triangle := trace_distance_triangle
  unit_bound := trace_distance_le_one
  helstrom := trace_distance_helstrom_link
  variational := trace_distance_variational_sup
  projective := distance_effect_projective
  measurement := tv_le_trace_distance_under_povm
  attained := tv_attains_trace_distance
  classical := tv_contractive_under_classical_channel
  noncommuting := Regression.noncommuting_distance
  strict_loss := Regression.strict_measurement_loss

end QuantumChannelTraceDistanceContract
