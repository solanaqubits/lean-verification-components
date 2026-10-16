import Verification.QuantumKnillLaflammeEnvironmentCriterion

noncomputable section
open scoped BigOperators ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumComplementaryChannelContract QuantumHelstromStateDiscrimination
open QuantumKnillLaflammeEnvironmentCriterion
namespace KnillLaflammeRegression

-- A complex phase distinguishes transpose from the original coefficient matrix.
def phaseW : Matrix (Fin 2) (Fin 1) ℂ := fun i _ => ![3/5, (4/5) * Complex.I] i

theorem phaseW_isometry : phaseW.conjTranspose * phaseW = 1 := by
  ext a b
  fin_cases a; fin_cases b
  norm_num [phaseW, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring_nf
  norm_num [map_ofNat]

def phaseChannel : KrausChannel 2 2 2 :=
  changed_kraus (unitary_channel (1 : Matrix.unitaryGroup (Fin 2) ℂ)) phaseW phaseW_isometry

def phaseSigma : Q 2 := phaseW * phaseW.conjTranspose

theorem phaseConstant : EnvironmentConstant phaseChannel (1 : Q 2) phaseSigma := by
  intro X
  simp only [encode, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  rw [phaseChannel, changed_complementary_channel, unitary_complementary]
  simp [phaseSigma]

theorem phaseKL : KnillLaflamme phaseChannel (1 : Q 2) phaseSigma :=
  (knill_laflamme_equiv_environment _ _ _).mpr phaseConstant

theorem phaseSigma_entries : phaseSigma = !![9/25, -12/25 * Complex.I;
    12/25 * Complex.I, 16/25] := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [phaseSigma, phaseW, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_one]
  all_goals ring_nf
  all_goals norm_num

example : StandardKnillLaflamme phaseChannel (1 : Q 2) phaseSigma.transpose := by
  rw [standard_iff_transpose, Matrix.transpose_transpose]
  exact phaseKL
example : phaseSigma 0 1 = phaseSigma.transpose 1 0 := rfl
example : phaseSigma ≠ phaseSigma.transpose := by
  rw [phaseSigma_entries]
  intro h
  have hi := congrArg (fun M : Q 2 => (M 0 1).im) h
  norm_num [Matrix.transpose_apply] at hi
example : Density phaseSigma := environment_density (by decide) _ _ (by simp) _ phaseKL
example : phaseSigma.IsHermitian := environment_hermitian (by decide) _ _ (by simp) _ phaseKL
example : phaseSigma.trace = 1 := (environment_density (by decide) _ _ (by simp) _ phaseKL).2
example : complementary_channel phaseChannel (encode (1 : Q 2) Examples.rhoPlus) = phaseSigma :=
  environment_of_density _ _ _ phaseKL Examples.rhoPlus_density
example : ∀ i j, phaseSigma i j = phaseSigma.transpose j i :=
  coefficient_indices (by decide) _ _ _ _
    ((standard_iff_transpose _ _ _).mpr (by simpa using phaseKL)) phaseKL

-- Genuine dimension-two code, two nonzero errors, unequal probabilities.
example : Regression.code.conjTranspose * Regression.code = 1 := Regression.code_isometry
example : Regression.errors 0 * Regression.code ≠ 0 ∧ Regression.errors 1 * Regression.code ≠ 0 :=
  Regression.both_errors_nonzero
example : (Regression.errors 0 * Regression.code).conjTranspose *
    (Regression.errors 1 * Regression.code) = 0 := Regression.orthogonal_error_spaces
example : Density Regression.environment := Regression.orthogonal_environment_density
example : Regression.environment 0 0 = (9/25 : ℂ) ∧
    Regression.environment 1 1 = (16/25 : ℂ) := ⟨rfl, rfl⟩
example : complementary_channel Regression.orthogonal_channel
    (encode Regression.code (Matrix.single 0 1 Complex.I)) = 0 := by
  rw [Regression.orthogonal_environment]
  simp
example : complementary_channel Regression.orthogonal_channel
    (encode Regression.code (QuantumNoBroadcastingMixed.basisProjector 0)) =
    complementary_channel Regression.orthogonal_channel
      (encode Regression.code (QuantumNoBroadcastingMixed.basisProjector 1)) := by
  rw [Regression.orthogonal_environment, Regression.orthogonal_environment]
  simp [QuantumNoBroadcastingMixed.basisProjector_trace]
example : Density (encode Regression.code Examples.rhoPlus) :=
  encode_density _ Regression.code_isometry Examples.rhoPlus_density
example (x : Fin 2 → ℂ) : Regression.code.mulVec x ∈ codeSpace Regression.code := ⟨x, rfl⟩
example {d k} (U : Matrix.unitaryGroup (Fin d) ℂ)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    KnillLaflamme (unitary_channel U) J (1 : Q 1) := unitary_criterion U J hJ

-- Definite leakage in the full-space dephasing counterexample.
example : Density (QuantumNoBroadcastingMixed.basisProjector (0 : Fin 2)) := basis_density _
example : Density (QuantumNoBroadcastingMixed.basisProjector (1 : Fin 2)) := basis_density _
example : complementary_channel (dephasing_channel 2)
    (QuantumNoBroadcastingMixed.basisProjector 0) ≠
    complementary_channel (dephasing_channel 2) (QuantumNoBroadcastingMixed.basisProjector 1) :=
  Regression.dephasing_distinguishes
example (σ : Q 2) : ¬ KnillLaflamme (dephasing_channel 2) (1 : Q 2) σ :=
  Regression.dephasing_not_criterion σ

-- Neither zero logical dimension nor a zero non-isometry can certify trace one.
example : KnillLaflamme (identity_channel 1) (0 : Matrix (Fin 1) (Fin 0) ℂ) (0 : Q 1) := by
  intro i j
  ext a b
  exact Fin.elim0 a
example : (0 : Matrix (Fin 1) (Fin 0) ℂ).conjTranspose *
    (0 : Matrix (Fin 1) (Fin 0) ℂ) = 1 := by
  ext a b; exact Fin.elim0 a
example : KnillLaflamme (identity_channel 2) (0 : Q 2) (0 : Q 1) := by
  intro i j
  simp
example : ¬ Density (0 : Q 1) := by
  intro h
  simpa using h.2

-- Diagonal probes alone miss an off-diagonal compressed product.
example : ((Matrix.single 0 1 1 : Q 2) * Matrix.single 0 0 1).trace = 0 := by
  rw [Matrix.trace_mul_single]
  norm_num [Matrix.single]
example : ((Matrix.single 0 1 1 : Q 2) * Matrix.single 1 1 1).trace = 0 := by
  rw [Matrix.trace_mul_single]
  norm_num [Matrix.single]
example : ((Matrix.single 0 1 1 : Q 2) * Matrix.single 1 0 1).trace = 1 := by
  rw [Matrix.trace_mul_single]
  norm_num [Matrix.single]
example : QuantumKnillLaflammeEnvironmentCriterionSuite :=
  QuantumKnillLaflammeEnvironmentCriterion.verification_suite
end KnillLaflammeRegression
