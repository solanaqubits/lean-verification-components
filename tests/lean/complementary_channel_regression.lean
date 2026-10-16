import Verification.QuantumComplementaryChannelContract

noncomputable section
open scoped BigOperators Kronecker ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumStinespringDilationContract QuantumComplementaryChannelContract
open QuantumHelstromStateDiscrimination.Examples
namespace ComplementaryRegression

-- A rectangular environment embedding with a genuinely complex phase.
def W : Matrix (Fin 3) (Fin 2) ℂ := !![1, 0; 0, Complex.I; 0, 0]
theorem W_isometry : W.conjTranspose * W = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]

def reset : KrausChannel 2 1 2 := reset_channel 0
def transformed : KrausChannel 2 1 3 := changed_kraus reset W W_isometry
def nonHermitian : Q 2 := !![0, Complex.I; 2, 0]

-- Both reduction directions and the orientation of complex off-diagonal entries.
example : complementary_channel reset nonHermitian = nonHermitian := reset_complementary _ _
example : complementary_channel reset nonHermitian 0 1 = Complex.I := by
  rw [reset, reset_complementary]; rfl
example : complementary_channel reset nonHermitian 1 0 = 2 := by
  rw [reset, reset_complementary]; rfl
example : partialTrace (dilation reset nonHermitian) = 0 := by
  rw [partial_trace_stinespring_eq_channel, reset, reset_channel_apply]
  norm_num [nonHermitian, Matrix.trace, Fin.sum_univ_two]
example : complementary_channel transformed nonHermitian =
    !![0, 1, 0; 2 * Complex.I, 0, 0; 0, 0, 0] := by
  rw [transformed, changed_complementary_channel, reset, reset_complementary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W, nonHermitian, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  ring
example (X : Q 2) : apply_channel transformed X = apply_channel reset X :=
  changed_main_channel _ _ _ _
example : QuantumHelstromStateDiscrimination.Density (complementary_channel transformed rhoPlus) :=
  complementary_density _ rhoPlus_density
example : complementary_channel transformed rhoPlus =
    !![1/2, -Complex.I/2, 0; Complex.I/2, 1/2, 0; 0, 0, 0] := by
  rw [transformed, changed_complementary_channel, reset, reset_complementary]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [W, rhoPlus, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two]
  all_goals ring_nf
  all_goals norm_num
example (X : Q 2) : dilation transformed X = change_environment W (dilation reset X) :=
  changed_dilation _ _ _ _
example : (stinespring_matrix transformed.operators).conjTranspose *
    stinespring_matrix transformed.operators = 1 := stinespring_isometry _

-- Unitary channels leave a fixed normalized one-dimensional environment.
example {d} (U : Matrix.unitaryGroup (Fin d) ℂ) {ρ : Q d}
    (h : QuantumHelstromStateDiscrimination.Density ρ) :
    complementary_channel (unitary_channel U) ρ = 1 := by
  rw [unitary_complementary, h.2, one_smul]
example : complementary_channel (identity_channel 2) rhoPlus = 1 := by
  have h := complementary_trace (identity_channel 2) rhoPlus
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  rw [rhoPlus_density.2] at h
  simpa [Matrix.trace] using h

-- Nontrivial reset with output dimension 3 and input dimension 2.
example (X : Q 2) : complementary_channel (reset_channel (2 : Fin 3)) X = X :=
  reset_complementary _ _
example : apply_channel (reset_channel (d := 2) (2 : Fin 3)) rhoPlus =
    QuantumNoBroadcastingMixed.basisProjector (2 : Fin 3) := reset_density _ rhoPlus_density

-- Lost marginal coherence survives only in joint correlations for this pair.
example : complementary_channel (dephasing_channel 2) rhoPlus = !![1/2, 0; 0, 1/2] := by
  rw [dephasing_complementary]
  ext i j; fin_cases i <;> fin_cases j <;> rfl
example : complementary_channel (dephasing_channel 2)
    QuantumCPTPChannelContract.Regression.rhoMinus = complementary_channel (dephasing_channel 2) rhoPlus :=
  QuantumComplementaryChannelContract.Regression.dephasing_environment_equal.symm
example : dilation (dephasing_channel 2) rhoPlus ≠
    dilation (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus :=
  QuantumComplementaryChannelContract.Regression.correlations_retain_distinction.2.2
example : complementary_channel (dephasing_channel 2) rhoPlus *
    complementary_channel (dephasing_channel 2) rhoPlus ≠ complementary_channel (dephasing_channel 2) rhoPlus := by
  rw [dephasing_complementary]
  intro h
  have he := congrArg (fun X : Q 2 => X 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, rhoPlus] at he

-- Padding really changes the environment dimension and preserves the old block.
example (X : Q 2) : complementary_channel (append_zero reset) X 0 1 = X 0 1 := by
  exact (append_zero_complementary_old reset X 0 1).trans (congrArg (fun M : Q 2 => M 0 1)
    (reset_complementary (0 : Fin 1) X))
example (X : Q 2) (i : Fin 3) : complementary_channel (append_zero reset) X 2 i = 0 :=
  append_zero_complementary_last_row _ _ _
example (X : Q 2) (i : Fin 3) : complementary_channel (append_zero reset) X i 2 = 0 :=
  append_zero_complementary_last_col _ _ _
example (X : Q 2) : apply_channel (append_zero (append_zero reset)) X = apply_channel reset X := by
  simp only [append_zero_channel]

-- Covariance needs no isometry, whereas invariance of the main channel does.
example (M : Ext 1 2) : partialTrace_system (change_environment (0 : Matrix (Fin 3) (Fin 2) ℂ) M) = 0 := by
  rw [complementary_environment_covariance]
  simp
example : (0 : Matrix (Fin 3) (Fin 2) ℂ).conjTranspose * (0 : Matrix (Fin 3) (Fin 2) ℂ) ≠ (1 : Q 2) := by simp
example : partialTrace (change_environment (0 : Q 1) (1 : Ext 1 1)) ≠ partialTrace (1 : Ext 1 1) := by
  intro h
  have he := congrArg (fun M : Q 1 => M 0 0) h
  norm_num [change_environment, environment_lift, partialTrace] at he

-- Complete positivity covers arbitrary finite block amplifications, not just positivity.
example : QuantumNoBroadcastingMixed.IsCompletelyPositive
    (apply_channel (complementary_kraus transformed)) := complementary_completely_positive _
example : QuantumComplementaryChannelContractSuite := QuantumComplementaryChannelContract.verification_suite
end ComplementaryRegression
