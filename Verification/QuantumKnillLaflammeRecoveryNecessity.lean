/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumKnillLaflammeGeneralRecoveryTheorem

/-! Necessity and sufficiency for exact recovery in finite dimensions.
Recovery is arbitrary, with an independently quantified Kraus family size.
No scalar-composite or environment-independence assumption is supplied. -/
noncomputable section
open scoped BigOperators ComplexOrder
open Matrix
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeGeneralRecoveryTheorem
namespace QuantumKnillLaflammeRecoveryNecessity
variable {k d e r s : ℕ}

/-- The action on matrix units determines all entrywise Kraus pairings. -/
theorem identity_entry {ι : Type*} [Fintype ι] (F : ι → Q k)
    (h : ∀ X : Q k, ∑ t, F t * X * (F t).conjTranspose = X)
    (a b p q : Fin k) :
    ∑ t, F t a p * star (F t b q) = if a = p ∧ b = q then 1 else 0 := by
  have hh := congrArg (fun M : Q k => M a b) (h (Matrix.single p q 1))
  simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.single, Matrix.conjTranspose_apply,
    ite_and, eq_comm] using hh

/-- Positive squares prevent cancellation of off-diagonal entries. -/
theorem identity_offdiagonal {ι : Type*} [Fintype ι] (F : ι → Q k)
    (h : ∀ X : Q k, ∑ t, F t * X * (F t).conjTranspose = X)
    (t : ι) (a p : Fin k) (hap : a ≠ p) : F t a p = 0 := by
  have hh := congrArg Complex.re (identity_entry F h a a p p)
  have hz : ∑ t, Complex.normSq (F t a p) = 0 := by
    simpa [hap, Complex.mul_conj] using hh
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t (_ : t ∈ Finset.univ) => Complex.normSq_nonneg (F t a p))).mp hz t
      (Finset.mem_univ t)
  exact Complex.normSq_eq_zero.mp ht

/-- Off-diagonal matrix units force each Kraus operator's diagonal to be constant. -/
theorem identity_diagonal {ι : Type*} [Fintype ι] (F : ι → Q k)
    (h : ∀ X : Q k, ∑ t, F t * X * (F t).conjTranspose = X)
    (t : ι) (a b : Fin k) : F t a a = F t b b := by
  have haa : ∑ t, Complex.normSq (F t a a) = 1 := by
    simpa [Complex.mul_conj] using congrArg Complex.re (identity_entry F h a a a a)
  have hbb : ∑ t, Complex.normSq (F t b b) = 1 := by
    simpa [Complex.mul_conj] using congrArg Complex.re (identity_entry F h b b b b)
  have hab : ∑ t, (F t a a * star (F t b b)).re = 1 := by
    simpa using congrArg Complex.re (identity_entry F h a b a b)
  have hz : ∑ t, Complex.normSq (F t a a - F t b b) = 0 := by
    simp_rw [Complex.normSq_sub]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, haa, hbb]
    simp only [Complex.star_def] at hab
    rw [hab]; norm_num
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun t (_ : t ∈ Finset.univ) => Complex.normSq_nonneg (F t a a - F t b b))).mp hz t
      (Finset.mem_univ t)
  exact sub_eq_zero.mp (Complex.normSq_eq_zero.mp ht)

theorem identity_kraus_scalar {ι : Type*} [Fintype ι] (hk : 0 < k) (F : ι → Q k)
    (h : ∀ X : Q k, ∑ t, F t * X * (F t).conjTranspose = X) (t : ι) :
    F t = F t ⟨0, hk⟩ ⟨0, hk⟩ • (1 : Q k) := by
  ext a b
  by_cases hab : a = b
  · subst b; simpa using identity_diagonal F h t a ⟨0, hk⟩
  · simp [hab, identity_offdiagonal F h t a b hab]

def ExactRecovery (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) : Prop :=
  ∀ X : Q k, apply_channel R (apply_channel E (encode J X)) = X

def compositeOperator (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) (μ : Fin s) (a : Fin r) : Q k :=
  R.operators μ * E.operators a * J

def compositeCoefficient (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) (μ : Fin s) (a : Fin r) : ℂ :=
  compositeOperator E J R μ a ⟨0, hk⟩ ⟨0, hk⟩

theorem composite_action (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) (X : Q k) :
    ∑ t : Fin s × Fin r, compositeOperator E J R t.1 t.2 * X *
      (compositeOperator E J R t.1 t.2).conjTranspose =
      apply_channel R (apply_channel E (encode J X)) := by
  simp only [Fintype.sum_prod_type, compositeOperator, apply_channel_eq, encode,
    Matrix.conjTranspose_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem lemma_composite_scalar (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) (h : ExactRecovery E J R)
    (μ : Fin s) (a : Fin r) :
    compositeOperator E J R μ a = compositeCoefficient hk E J R μ a • (1 : Q k) := by
  apply identity_kraus_scalar hk (fun t : Fin s × Fin r => compositeOperator E J R t.1 t.2)
    (fun X => (composite_action E J R X).trans (h X)) (μ, a)

/-- Gram coefficients: a is conjugated and b is not. -/
def recoveredCoefficients (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) : Q r :=
  fun a b => ∑ μ, star (compositeCoefficient hk E J R μ a) *
    compositeCoefficient hk E J R μ b

theorem knill_laflamme_necessity (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) (h : ExactRecovery E J R) :
    StandardKnillLaflamme E J (recoveredCoefficients hk E J R) := by
  intro a b
  have hsum : (∑ μ, (compositeOperator E J R μ a).conjTranspose *
      compositeOperator E J R μ b) =
      J.conjTranspose * (E.operators a).conjTranspose * E.operators b * J := by
    calc
      _ = J.conjTranspose * (E.operators a).conjTranspose *
          (∑ μ, (R.operators μ).conjTranspose * R.operators μ) * E.operators b * J := by
        simp only [compositeOperator, Matrix.conjTranspose_mul, Matrix.mul_sum,
          Matrix.sum_mul, Matrix.mul_assoc]
      _ = _ := by rw [R.complete, Matrix.mul_one]
  rw [← hsum]
  simp only [lemma_composite_scalar hk E J R h, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    smul_smul, ← Finset.sum_smul, recoveredCoefficients, mul_comm]

theorem recovered_coefficients_unique (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) (h : ExactRecovery E J R)
    (Λ : Q r) (hΛ : StandardKnillLaflamme E J Λ) : recoveredCoefficients hk E J R = Λ := by
  ext a b
  have hh := (knill_laflamme_necessity hk E J R h a b).symm.trans (hΛ a b)
  have hd := congrArg (fun M : Q k => M ⟨0, hk⟩ ⟨0, hk⟩) hh
  simpa using hd

/-- The size of the recovery Kraus family is existential, independent of E. -/
def Recoverable (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ) : Prop :=
  ∃ s, ∃ R : KrausChannel e k s, ExactRecovery E J R

theorem recovery_necessity_equivalence (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    Recoverable E J ↔ ∃ Λ : Q r, StandardKnillLaflamme E J Λ := by
  constructor
  · rintro ⟨s, R, h⟩
    exact ⟨recoveredCoefficients hk E J R, knill_laflamme_necessity hk E J R h⟩
  · rintro ⟨Λ, hΛ⟩
    let C : GeneralCode E J := ⟨hk, hJ, Λ, hΛ⟩
    exact ⟨r + e, generalRecovery C, general_recovery_theorem C⟩

theorem criterion_environment_equivalence (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) :
    (∃ Λ : Q r, StandardKnillLaflamme E J Λ) ↔ ∃ σ : Q r, EnvironmentConstant E J σ := by
  constructor
  · rintro ⟨Λ, h⟩
    exact ⟨Λ.transpose, (knill_laflamme_equiv_environment _ _ _).mp
      ((standard_iff_transpose _ _ _).mp h)⟩
  · rintro ⟨σ, h⟩
    refine ⟨σ.transpose, (standard_iff_transpose _ _ _).mpr ?_⟩
    simpa using (knill_laflamme_equiv_environment _ _ _).mpr h

theorem recovery_environment_equivalence (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    Recoverable E J ↔ ∃ σ : Q r, EnvironmentConstant E J σ :=
  (recovery_necessity_equivalence hk E J hJ).trans (criterion_environment_equivalence E J)

/-- For a genuine code the fixed environment is automatically a density matrix. -/
theorem recovery_environment_density_equivalence (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    Recoverable E J ↔ ∃ σ : Q r, Density σ ∧ EnvironmentConstant E J σ := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := (recovery_environment_equivalence hk E J hJ).mp h
    exact ⟨σ, environment_density hk E J hJ σ
      ((knill_laflamme_equiv_environment _ _ _).mpr hσ), hσ⟩
  · rintro ⟨σ, _, hσ⟩
    exact (recovery_environment_equivalence hk E J hJ).mpr ⟨σ, hσ⟩

/-- Full-qubit dephasing has no exact recovery, for any recovery Kraus count. -/
theorem dephasing_not_recoverable : ¬ Recoverable (dephasing_channel 2) (1 : Q 2) := by
  intro h
  obtain ⟨σ, hσ⟩ := (recovery_environment_equivalence (by decide)
    (dephasing_channel 2) (1 : Q 2) (by simp)).mp h
  exact Regression.dephasing_not_constant σ hσ

structure QuantumKnillLaflammeRecoveryNecessitySuite : Prop where
  identity_scalar : ∀ {k n} (hk : 0 < k) (F : Fin n → Q k),
    (∀ X : Q k, ∑ t, F t * X * (F t).conjTranspose = X) →
    ∀ t, F t = F t ⟨0, hk⟩ ⟨0, hk⟩ • (1 : Q k)
  composite_scalar : ∀ {k d e r s} (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s), ExactRecovery E J R →
    ∀ μ a, compositeOperator E J R μ a = compositeCoefficient hk E J R μ a • (1 : Q k)
  necessity : ∀ {k d e r s} (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s), ExactRecovery E J R →
    StandardKnillLaflamme E J (recoveredCoefficients hk E J R)
  coefficient_uniqueness : ∀ {k d e r s} (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s), ExactRecovery E J R →
    ∀ Λ, StandardKnillLaflamme E J Λ → recoveredCoefficients hk E J R = Λ
  criterion : ∀ {k d e r} (_hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    (Recoverable E J ↔ ∃ Λ : Q r, StandardKnillLaflamme E J Λ)
  environment : ∀ {k d e r} (_hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    (Recoverable E J ↔ ∃ σ : Q r, EnvironmentConstant E J σ)
  density_environment : ∀ {k d e r} (_hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    (Recoverable E J ↔ ∃ σ : Q r, Density σ ∧ EnvironmentConstant E J σ)
  dephasing_impossible : ¬ Recoverable (dephasing_channel 2) (1 : Q 2)

theorem verification_suite : QuantumKnillLaflammeRecoveryNecessitySuite where
  identity_scalar := identity_kraus_scalar
  composite_scalar := lemma_composite_scalar
  necessity := knill_laflamme_necessity
  coefficient_uniqueness := recovered_coefficients_unique
  criterion := recovery_necessity_equivalence
  environment := recovery_environment_equivalence
  density_environment := recovery_environment_density_equivalence
  dephasing_impossible := dephasing_not_recoverable

end QuantumKnillLaflammeRecoveryNecessity
