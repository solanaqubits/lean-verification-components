/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumComplementaryChannelContract
import Verification.QuantumStinespringDilationContract
import Verification.QuantumCPTPChannelContract

/-! Finite Knill-Laflamme / complementary-channel equivalence.
The algebraic equivalence holds on all complex matrices. A positive logical
dimension and an isometric encoding are needed to obtain a density environment.
No recovery channel or general quantum-error-correction theorem is constructed. -/
noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumComplementaryChannelContract QuantumHelstromStateDiscrimination
namespace QuantumKnillLaflammeEnvironmentCriterion
variable {k d e r : ℕ}

/-- The code consists exactly of the vectors in the image of J. -/
def codeSpace (J : Matrix (Fin d) (Fin k) ℂ) : Set (Fin d → ℂ) := Set.range J.mulVec

def encode (J : Matrix (Fin d) (Fin k) ℂ) (X : Q k) : Q d := J * X * J.conjTranspose

/-- Environment-index convention: j is conjugated, i is not. -/
def KnillLaflamme (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (σ : Q r) : Prop :=
  ∀ i j, J.conjTranspose * (K.operators j).conjTranspose * K.operators i * J =
    σ i j • (1 : Q k)

def EnvironmentConstant (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (σ : Q r) : Prop :=
  ∀ X : Q k, complementary_channel K (encode J X) = X.trace • σ

/-- Trace cyclicity puts the compressed error product against the logical input. -/
theorem encoded_complementary_entry (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (X : Q k) (i j : Fin r) :
    complementary_channel K (encode J X) i j =
      ((J.conjTranspose * (K.operators j).conjTranspose * K.operators i * J) * X).trace := by
  rw [complementary_entry, encode, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

/-- The reverse trace pairing is explicitly tested on matrix units E_ba. -/
theorem scalar_of_trace_pairing (A : Q k) (c : ℂ)
    (h : ∀ X : Q k, (A * X).trace = X.trace * c) : A = c • (1 : Q k) := by
  ext a b
  have hx := h (Matrix.single b a 1)
  rw [Matrix.trace_mul_comm, Matrix.trace_single_mul] at hx
  by_cases hab : a = b
  · subst b
    simpa using hx
  · rw [Matrix.trace_single_eq_of_ne b a (1 : ℂ) (Ne.symm hab)] at hx
    simpa [Matrix.one_apply, hab] using hx

theorem knill_laflamme_equiv_environment (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (σ : Q r) :
    KnillLaflamme K J σ ↔ EnvironmentConstant K J σ := by
  constructor
  · intro h X
    ext i j
    rw [encoded_complementary_entry, h i j]
    simp [Matrix.trace_smul, mul_comm]
  · intro h i j
    apply scalar_of_trace_pairing
    intro X
    rw [← encoded_complementary_entry]
    exact congrArg (fun M : Q r => M i j) (h X)

theorem encode_trace (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    (X : Q k) : (encode J X).trace = X.trace := by
  rw [encode, Matrix.trace_mul_cycle, hJ, Matrix.one_mul]

theorem encode_density (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    {ρ : Q k} (hρ : Density ρ) : Density (encode J ρ) :=
  ⟨hρ.1.mul_mul_conjTranspose_same J, (encode_trace J hJ ρ).trans hρ.2⟩

theorem environment_of_density (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (σ : Q r) (h : KnillLaflamme K J σ) {ρ : Q k} (hρ : Density ρ) :
    complementary_channel K (encode J ρ) = σ := by
  rw [(knill_laflamme_equiv_environment K J σ).mp h ρ, hρ.2, one_smul]

theorem basis_density (i : Fin k) : Density (QuantumNoBroadcastingMixed.basisProjector i) := by
  refine ⟨?_, QuantumNoBroadcastingMixed.basisProjector_trace i⟩
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split_ifs <;> norm_num

theorem environment_density (hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    (σ : Q r) (h : KnillLaflamme K J σ) : Density σ := by
  have hi := basis_density (⟨0, hk⟩ : Fin k)
  have hc := complementary_density K (encode_density J hJ hi)
  rwa [environment_of_density K J σ h hi] at hc

theorem environment_hermitian (hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    (σ : Q r) (h : KnillLaflamme K J σ) : σ.IsHermitian :=
  (environment_density hk K J hJ σ h).1.isHermitian

/-- Standard literature convention, with i conjugated and j unconjugated. -/
def StandardKnillLaflamme (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (lam : Q r) : Prop :=
  ∀ i j, J.conjTranspose * (K.operators i).conjTranspose * K.operators j * J =
    lam i j • (1 : Q k)

theorem standard_iff_transpose (K : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (lam : Q r) : StandardKnillLaflamme K J lam ↔ KnillLaflamme K J lam.transpose := by
  constructor <;> intro h i j <;> exact h j i

theorem coefficient_indices (hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (lam σ : Q r)
    (hlam : StandardKnillLaflamme K J lam) (hσ : KnillLaflamme K J σ) :
    ∀ i j, σ i j = lam j i := by
  intro i j
  have he := (hσ i j).symm.trans (hlam j i)
  have hd := congrArg (fun A : Q k => A ⟨0, hk⟩ ⟨0, hk⟩) he
  simpa using hd


theorem environment_unique (hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) {σ τ : Q r}
    (hσ : EnvironmentConstant K J σ) (hτ : EnvironmentConstant K J τ) : σ = τ := by
  have h := (hσ (Matrix.single ⟨0, hk⟩ ⟨0, hk⟩ 1)).symm.trans
    (hτ (Matrix.single ⟨0, hk⟩ ⟨0, hk⟩ 1))
  simpa using h

theorem unitary_criterion (U : Matrix.unitaryGroup (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    KnillLaflamme (unitary_channel U) J (1 : Q 1) := by
  apply (knill_laflamme_equiv_environment _ _ _).mpr
  intro X
  rw [unitary_complementary, encode_trace J hJ]

namespace Regression

/-- Two logical dimensions embedded in the first of two orthogonal blocks. -/
def code : Matrix (Fin 4) (Fin 2) ℂ := !![1, 0; 0, 1; 0, 0; 0, 0]

def blockSwap : Q 4 := !![0, 0, 1, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 1, 0, 0]

def errors : Fin 2 → Q 4 := ![(3 / 5 : ℂ) • 1, (4 / 5 : ℂ) • blockSwap]

def orthogonal_channel : KrausChannel 4 4 2 where
  operators := errors
  complete := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      norm_num [errors, blockSwap, Matrix.mul_apply, Matrix.conjTranspose_apply,
        Fin.sum_univ_succ, Matrix.one_apply]
    all_goals norm_num [map_ofNat]

def environment : Q 2 := !![9 / 25, 0; 0, 16 / 25]

theorem code_isometry : code.conjTranspose * code = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [code, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem orthogonal_error_spaces :
    (errors 0 * code).conjTranspose * (errors 1 * code) = 0 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [errors, blockSwap, code, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem both_errors_nonzero : errors 0 * code ≠ 0 ∧ errors 1 * code ≠ 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 2) ℂ => M 0 0) h
    norm_num [errors, code, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply] at he
  · intro h
    have he := congrArg (fun M : Matrix (Fin 4) (Fin 2) ℂ => M 2 0) h
    norm_num [errors, code, blockSwap, Matrix.mul_apply, Fin.sum_univ_succ] at he
    change (4 / 5 : ℂ) = 0 at he
    norm_num at he

theorem orthogonal_criterion : KnillLaflamme orthogonal_channel code environment := by
  intro i j
  ext a b
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [orthogonal_channel, errors, blockSwap, code, environment,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]
  all_goals norm_num [map_ofNat]

theorem orthogonal_environment (X : Q 2) :
    complementary_channel orthogonal_channel (encode code X) = X.trace • environment :=
  (knill_laflamme_equiv_environment _ _ _).mp orthogonal_criterion X

theorem orthogonal_environment_density : Density environment :=
  environment_density (by decide) orthogonal_channel code code_isometry
    environment orthogonal_criterion

theorem dephasing_basis (i : Fin 2) :
    complementary_channel (dephasing_channel 2) (QuantumNoBroadcastingMixed.basisProjector i) =
      QuantumNoBroadcastingMixed.basisProjector i := by
  rw [dephasing_complementary]
  simp [QuantumNoBroadcastingMixed.basisProjector]

theorem dephasing_distinguishes :
    complementary_channel (dephasing_channel 2) (QuantumNoBroadcastingMixed.basisProjector 0) ≠
      complementary_channel (dephasing_channel 2)
        (QuantumNoBroadcastingMixed.basisProjector 1) := by
  rw [dephasing_basis, dephasing_basis]
  intro h
  have he := congrArg (fun M : Q 2 => M 0 0) h
  norm_num [QuantumNoBroadcastingMixed.basisProjector, Matrix.diagonal] at he

theorem dephasing_not_constant (σ : Q 2) :
    ¬ EnvironmentConstant (dephasing_channel 2) (1 : Q 2) σ := by
  intro h
  have h0 := h (QuantumNoBroadcastingMixed.basisProjector 0)
  have h1 := h (QuantumNoBroadcastingMixed.basisProjector 1)
  simp only [encode, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one,
    QuantumNoBroadcastingMixed.basisProjector_trace, one_smul] at h0 h1
  exact dephasing_distinguishes (h0.trans h1.symm)

theorem dephasing_not_criterion (σ : Q 2) :
    ¬ KnillLaflamme (dephasing_channel 2) (1 : Q 2) σ := by
  rw [knill_laflamme_equiv_environment]
  exact dephasing_not_constant σ
end Regression


structure QuantumKnillLaflammeEnvironmentCriterionSuite : Prop where
  equivalence : ∀ {k d e r} (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (σ : Q r),
    KnillLaflamme K J σ ↔ EnvironmentConstant K J σ
  admissible : ∀ {k d e r} (_hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    ∀ σ : Q r, KnillLaflamme K J σ → Density σ
  hermitian : ∀ {k d e r} (_hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    ∀ σ : Q r, KnillLaflamme K J σ → σ.IsHermitian
  constant_on_states : ∀ {k d e r} (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (σ : Q r), KnillLaflamme K J σ →
    ∀ {ρ : Q k}, Density ρ → complementary_channel K (encode J ρ) = σ
  index_convention : ∀ {k d e r} (_hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (lam σ : Q r),
    StandardKnillLaflamme K J lam → KnillLaflamme K J σ → ∀ i j, σ i j = lam j i
  transpose_equivalence : ∀ {k d e r} (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (lam : Q r),
    StandardKnillLaflamme K J lam ↔ KnillLaflamme K J lam.transpose
  unique : ∀ {k d e r} (_hk : 0 < k) (K : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) {σ τ : Q r},
    EnvironmentConstant K J σ → EnvironmentConstant K J τ → σ = τ
  unitary : ∀ {k d} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 →
    KnillLaflamme (unitary_channel U) J (1 : Q 1)
  orthogonal_example : KnillLaflamme Regression.orthogonal_channel
    Regression.code Regression.environment
  nonzero_errors : Regression.errors 0 * Regression.code ≠ 0 ∧
    Regression.errors 1 * Regression.code ≠ 0
  orthogonal_errors : (Regression.errors 0 * Regression.code).conjTranspose *
    (Regression.errors 1 * Regression.code) = 0
  dephasing_counterexample : ∀ σ : Q 2,
    ¬ KnillLaflamme (dephasing_channel 2) (1 : Q 2) σ

theorem verification_suite : QuantumKnillLaflammeEnvironmentCriterionSuite where
  equivalence := knill_laflamme_equiv_environment
  admissible := environment_density
  hermitian := environment_hermitian
  constant_on_states := environment_of_density
  index_convention := coefficient_indices
  transpose_equivalence := standard_iff_transpose
  unique := environment_unique
  unitary := unitary_criterion
  orthogonal_example := Regression.orthogonal_criterion
  nonzero_errors := Regression.both_errors_nonzero
  orthogonal_errors := Regression.orthogonal_error_spaces
  dephasing_counterexample := Regression.dephasing_not_criterion

end QuantumKnillLaflammeEnvironmentCriterion
