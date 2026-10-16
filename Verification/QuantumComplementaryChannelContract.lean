/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumCPTPChannelContract
import Verification.QuantumStinespringDilationContract

/-! Complementary channels for a supplied finite Kraus representation.
Indices are output system × environment. The joint matrix need not be pure.
Environment changes below are supplied isometries, not a uniqueness theorem. -/
noncomputable section
open scoped BigOperators Kronecker ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumStinespringDilationContract QuantumHelstromStateDiscrimination
namespace QuantumComplementaryChannelContract
variable {d e r r' : ℕ}

/-- Trace out the FIRST index of the existing system × environment layout. -/
def partialTrace_system (M : Ext e r) : Q r := fun i j => ∑ a, M (a, i) (a, j)

def complementary_channel (K : KrausChannel d e r) (X : Q d) : Q r :=
  partialTrace_system (dilation K X)

/-- Exchange the output and Kraus indices, keeping the input index fixed. -/
def complementary_operators (K : KrausChannel d e r) :
    Fin e → Matrix (Fin r) (Fin d) ℂ := fun a j b => K.operators j a b

theorem complementary_complete (K : KrausChannel d e r) :
    ∑ a, (complementary_operators K a).conjTranspose * complementary_operators K a = 1 := by
  rw [← K.complete]
  ext b c
  simp only [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    complementary_operators]
  exact Finset.sum_comm

def complementary_kraus (K : KrausChannel d e r) : KrausChannel d r e where
  operators := complementary_operators K
  complete := complementary_complete K

theorem complementary_eq_apply (K : KrausChannel d e r) (X : Q d) :
    complementary_channel K X = apply_channel (complementary_kraus K) X := by
  ext i j
  simp [complementary_channel, partialTrace_system, dilation, stinespring_matrix,
    apply_channel_eq, complementary_kraus, complementary_operators,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.sum_apply]

theorem complementary_entry (K : KrausChannel d e r) (X : Q d) (i j : Fin r) :
    complementary_channel K X i j = (K.operators i * X * (K.operators j).conjTranspose).trace := by
  simp [complementary_channel, partialTrace_system, dilation, stinespring_matrix,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem complementary_trace (K : KrausChannel d e r) (X : Q d) :
    (complementary_channel K X).trace = X.trace := by
  rw [complementary_eq_apply]
  exact channel_trace_preserving _ X

theorem complementary_completely_positive (K : KrausChannel d e r) :
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (complementary_kraus K)) :=
  channel_completely_positive _

theorem complementary_density (K : KrausChannel d e r) {ρ : Q d} (hρ : Density ρ) :
    Density (complementary_channel K ρ) := by
  rw [complementary_eq_apply]
  exact channel_density _ hρ

theorem complementary_add (K : KrausChannel d e r) (X Y : Q d) :
    complementary_channel K (X + Y) = complementary_channel K X + complementary_channel K Y := by
  simp only [complementary_eq_apply, map_add]

theorem complementary_smul (K : KrausChannel d e r) (c : ℂ) (X : Q d) :
    complementary_channel K (c • X) = c • complementary_channel K X := by
  simp only [complementary_eq_apply, map_smul]

theorem simultaneous_reductions (K : KrausChannel d e r) (X : Q d) :
    partialTrace (dilation K X) = apply_channel K X ∧
    partialTrace_system (dilation K X) = apply_channel (complementary_kraus K) X :=
  ⟨partial_trace_stinespring_eq_channel K X, complementary_eq_apply K X⟩

/-- An environment block at fixed output-system indices. -/
def system_block (M : Ext e r) (a b : Fin e) : Q r := fun i j => M (a, i) (b, j)

def environment_lift (W : Matrix (Fin r') (Fin r) ℂ) :
    Matrix (Fin e × Fin r') (Fin e × Fin r) ℂ := (1 : Q e) ⊗ₖ W

def change_environment (W : Matrix (Fin r') (Fin r) ℂ) (M : Ext e r) : Ext e r' :=
  environment_lift (e := e) W * M * (environment_lift (e := e) W).conjTranspose

theorem change_environment_block (W : Matrix (Fin r') (Fin r) ℂ)
    (M : Ext e r) (a b : Fin e) :
    system_block (change_environment W M) a b = W * system_block M a b * W.conjTranspose := by
  ext i j
  simp [system_block, change_environment, environment_lift, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.one_apply,
    Fintype.sum_prod_type, apply_ite (starRingEnd ℂ)]

theorem system_reduction_as_sum (M : Ext e r) :
    partialTrace_system M = ∑ a, system_block M a a := by
  ext i j
  simp [partialTrace_system, system_block, Matrix.sum_apply]

theorem environment_reduction_as_trace (M : Ext e r) (a b : Fin e) :
    partialTrace M a b = (system_block M a b).trace := rfl

/-- The covariance identity holds for every W, even without the isometry premise. -/
theorem complementary_environment_covariance (W : Matrix (Fin r') (Fin r) ℂ)
    (M : Ext e r) :
    partialTrace_system (change_environment W M) =
      W * partialTrace_system M * W.conjTranspose := by
  simp only [system_reduction_as_sum, change_environment_block,
    Matrix.mul_sum, Matrix.sum_mul]

theorem main_environment_invariant (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) (M : Ext e r) :
    partialTrace (change_environment W M) = partialTrace M := by
  ext a b
  rw [environment_reduction_as_trace, change_environment_block,
    Matrix.trace_mul_cycle, hW, Matrix.one_mul, environment_reduction_as_trace]


theorem environment_lift_isometry (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) :
    (environment_lift (e := e) W).conjTranspose * environment_lift (e := e) W = 1 := by
  simp only [environment_lift, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, Matrix.one_mul, hW, Matrix.one_kronecker_one]

/-- The transformed dilation remains an isometry, including rectangular W. -/
theorem changed_stinespring_isometry (K : KrausChannel d e r)
    (W : Matrix (Fin r') (Fin r) ℂ) (hW : W.conjTranspose * W = 1) :
    (environment_lift (e := e) W * stinespring_matrix K.operators).conjTranspose *
      (environment_lift (e := e) W * stinespring_matrix K.operators) = 1 := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (environment_lift (e := e) W).conjTranspose,
    environment_lift_isometry W hW, Matrix.one_mul, stinespring_isometry]

def changed_kraus (K : KrausChannel d e r) (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) : KrausChannel d e r' where
  operators := fun j a b => (environment_lift (e := e) W * stinespring_matrix K.operators) (a, j) b
  complete := by
    have hg := stinespring_isometry_general (fun (j : Fin r') (a : Fin e) (b : Fin d) =>
      (environment_lift (e := e) W * stinespring_matrix K.operators) (a, j) b)
    exact hg.symm.trans (changed_stinespring_isometry K W hW)

theorem changed_stinespring (K : KrausChannel d e r) (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) :
    stinespring_matrix (changed_kraus K W hW).operators =
      environment_lift (e := e) W * stinespring_matrix K.operators := rfl

theorem changed_dilation (K : KrausChannel d e r) (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) (X : Q d) :
    dilation (changed_kraus K W hW) X = change_environment W (dilation K X) := by
  simp only [dilation, changed_stinespring, Matrix.conjTranspose_mul,
    change_environment, Matrix.mul_assoc]

theorem changed_main_channel (K : KrausChannel d e r) (W : Matrix (Fin r') (Fin r) ℂ)
    (hW : W.conjTranspose * W = 1) (X : Q d) :
    apply_channel (changed_kraus K W hW) X = apply_channel K X := by
  rw [← partial_trace_stinespring_eq_channel, changed_dilation,
    main_environment_invariant W hW, partial_trace_stinespring_eq_channel]

theorem changed_complementary_channel (K : KrausChannel d e r)
    (W : Matrix (Fin r') (Fin r) ℂ) (hW : W.conjTranspose * W = 1) (X : Q d) :
    complementary_channel (changed_kraus K W hW) X =
      W * complementary_channel K X * W.conjTranspose := by
  unfold complementary_channel
  rw [changed_dilation, complementary_environment_covariance]

/-- One-dimensional environments have no input-dependent normalized state. -/
theorem unitary_complementary (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) :
    complementary_channel (unitary_channel U) X = X.trace • (1 : Q 1) := by
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst i; subst j
  rw [complementary_entry]
  change ((U : Q d) * X * (U : Q d).conjTranspose).trace = _
  rw [← unitary_channel_apply, channel_trace_preserving]
  simp

theorem reset_complementary (v : Fin e) (X : Q d) :
    complementary_channel (reset_channel v) X = X := by
  ext i j
  simp [complementary_entry, reset_channel, Matrix.trace, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.single, ite_and]

theorem dephasing_complementary (X : Q d) :
    complementary_channel (dephasing_channel d) X = Matrix.diagonal (fun i => X i i) := by
  ext i j
  simp [complementary_entry, dephasing_channel, QuantumNoBroadcastingMixed.basisProjector,
    Matrix.diagonal, Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  split_ifs <;> simp_all

/-- Padding embeds the old environment as its leading block. -/
theorem append_zero_complementary_old (K : KrausChannel d e r) (X : Q d) (i j : Fin r) :
    complementary_channel (append_zero K) X i.castSucc j.castSucc =
      complementary_channel K X i j := by
  simp [complementary_entry, append_zero]

theorem append_zero_complementary_last_row (K : KrausChannel d e r) (X : Q d) (j : Fin (r + 1)) :
    complementary_channel (append_zero K) X (Fin.last r) j = 0 := by
  simp [complementary_entry, append_zero]

theorem append_zero_complementary_last_col (K : KrausChannel d e r) (X : Q d) (i : Fin (r + 1)) :
    complementary_channel (append_zero K) X i (Fin.last r) = 0 := by
  simp [complementary_entry, append_zero]

namespace Regression
open QuantumHelstromStateDiscrimination.Examples

theorem dephasing_environment_equal :
    complementary_channel (dephasing_channel 2) rhoPlus =
      complementary_channel (dephasing_channel 2)
        QuantumCPTPChannelContract.Regression.rhoMinus := by
  simp only [dephasing_complementary, ← dephasing_channel_apply]
  exact QuantumCPTPChannelContract.Regression.dephasing_identifies_pair

/-- Neither marginal distinguishes this pair, but the joint matrices differ. -/
theorem correlations_retain_distinction :
    apply_channel (dephasing_channel 2) rhoPlus =
      apply_channel (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus ∧
    complementary_channel (dephasing_channel 2) rhoPlus =
      complementary_channel (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus ∧
    dilation (dephasing_channel 2) rhoPlus ≠
      dilation (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus :=
  ⟨QuantumCPTPChannelContract.Regression.dephasing_identifies_pair,
    dephasing_environment_equal,
    QuantumStinespringDilationContract.Regression.dephasing_joint_distinct⟩
end Regression


structure QuantumComplementaryChannelContractSuite : Prop where
  complete : ∀ {d e r} (K : KrausChannel d e r),
    ∑ a, (complementary_operators K a).conjTranspose * complementary_operators K a = 1
  realization : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    complementary_channel K X = apply_channel (complementary_kraus K) X
  entries : ∀ {d e r} (K : KrausChannel d e r) (X : Q d) (i j : Fin r),
    complementary_channel K X i j = (K.operators i * X * (K.operators j).conjTranspose).trace
  trace_preserved : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    (complementary_channel K X).trace = X.trace
  completely_positive : ∀ {d e r} (K : KrausChannel d e r),
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (complementary_kraus K))
  density : ∀ {d e r} (K : KrausChannel d e r) {ρ : Q d},
    Density ρ → Density (complementary_channel K ρ)
  reductions : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    partialTrace (dilation K X) = apply_channel K X ∧
    partialTrace_system (dilation K X) = apply_channel (complementary_kraus K) X
  main_invariant : ∀ {d e r r'} (K : KrausChannel d e r)
    (W : Matrix (Fin r') (Fin r) ℂ) (hW : W.conjTranspose * W = 1) (X : Q d),
    apply_channel (changed_kraus K W hW) X = apply_channel K X
  complementary_covariant : ∀ {d e r r'} (K : KrausChannel d e r)
    (W : Matrix (Fin r') (Fin r) ℂ) (hW : W.conjTranspose * W = 1) (X : Q d),
    complementary_channel (changed_kraus K W hW) X =
      W * complementary_channel K X * W.conjTranspose
  unitary_environment : ∀ {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d),
    complementary_channel (unitary_channel U) X = X.trace • (1 : Q 1)
  reset_environment : ∀ {d e} (v : Fin e) (X : Q d),
    complementary_channel (reset_channel v) X = X
  dephasing_environment : ∀ {d} (X : Q d),
    complementary_channel (dephasing_channel d) X = Matrix.diagonal (fun i => X i i)
  padding_block : ∀ {d e r} (K : KrausChannel d e r) (X : Q d) (i j : Fin r),
    complementary_channel (append_zero K) X i.castSucc j.castSucc = complementary_channel K X i j

theorem verification_suite : QuantumComplementaryChannelContractSuite where
  complete := complementary_complete
  realization := complementary_eq_apply
  entries := complementary_entry
  trace_preserved := complementary_trace
  completely_positive := complementary_completely_positive
  density := complementary_density
  reductions := simultaneous_reductions
  main_invariant := changed_main_channel
  complementary_covariant := changed_complementary_channel
  unitary_environment := unitary_complementary
  reset_environment := reset_complementary
  dephasing_environment := dephasing_complementary
  padding_block := append_zero_complementary_old

end QuantumComplementaryChannelContract
