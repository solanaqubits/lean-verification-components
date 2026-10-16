/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMInformationEntropy
import Verification.QuantumCPTPChannelContract
import Verification.QuantumPOVMNaimarkDilation

/-! Finite Stinespring dilation for a supplied rectangular Kraus family.
The product index is output system × environment. No minimality, uniqueness,
numerical implementation or general unitary extension is asserted. -/
noncomputable section
open scoped BigOperators Kronecker ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
namespace QuantumStinespringDilationContract
variable {d e r : ℕ}

/-- Stack Kraus operators, with the environment in the second product index. -/
def stinespring_matrix (K : Fin r → Matrix (Fin e) (Fin d) ℂ) :
    Matrix (Fin e × Fin r) (Fin d) ℂ := fun a b => K a.2 a.1 b

theorem stinespring_isometry_general (K : Fin r → Matrix (Fin e) (Fin d) ℂ) :
    (stinespring_matrix K).conjTranspose * stinespring_matrix K =
      ∑ j, (K j).conjTranspose * K j := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespring_matrix,
    Fintype.sum_prod_type, Matrix.sum_apply]
  exact Finset.sum_comm

theorem stinespring_isometry (K : KrausChannel d e r) :
    (stinespring_matrix K.operators).conjTranspose * stinespring_matrix K.operators = 1 := by
  rw [stinespring_isometry_general, K.complete]

def dilation (K : KrausChannel d e r) (X : Q d) : Ext e r :=
  stinespring_matrix K.operators * X * (stinespring_matrix K.operators).conjTranspose

/-- Partial trace is exact on all complex matrices, with no positivity hypothesis. -/
theorem partial_trace_stinespring_eq_channel (K : KrausChannel d e r) (X : Q d) :
    partialTrace (dilation K X) = apply_channel K X := by
  ext a b
  simp [partialTrace, dilation, apply_channel_eq, Matrix.mul_apply,
    Matrix.conjTranspose_apply, stinespring_matrix, Matrix.sum_apply]

/-- The Heisenberg formula holds for arbitrary observables, not just effects. -/
theorem stinespring_dual_map_identity (K : KrausChannel d e r) (E : Q e) :
    (stinespring_matrix K.operators).conjTranspose * (E ⊗ₖ (1 : Q r)) *
      stinespring_matrix K.operators = dual_channel K E := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, stinespring_matrix, RCLike.star_def,
    Matrix.kroneckerMap_apply, Matrix.one_apply, mul_ite, mul_one, mul_zero, Fintype.sum_prod_type,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, dual_channel_eq, Matrix.sum_apply]
  exact Finset.sum_comm

/-- The joint matrix retains the input; information is lost only after reduction. -/
theorem dilation_recover (K : KrausChannel d e r) (X : Q d) :
    (stinespring_matrix K.operators).conjTranspose * dilation K X *
      stinespring_matrix K.operators = X := by
  simp only [dilation, ← Matrix.mul_assoc, stinespring_isometry, Matrix.one_mul]
  rw [Matrix.mul_assoc, stinespring_isometry, Matrix.mul_one]

theorem dilation_injective (K : KrausChannel d e r) : Function.Injective (dilation K) := by
  intro X Y h
  have hh := congrArg (fun M => (stinespring_matrix K.operators).conjTranspose * M *
    stinespring_matrix K.operators) h
  simpa only [dilation_recover] using hh

theorem dilation_trace (K : KrausChannel d e r) (X : Q d) :
    (dilation K X).trace = X.trace := by
  rw [dilation, Matrix.trace_mul_cycle, stinespring_isometry, Matrix.one_mul]

theorem dilation_positive (K : KrausChannel d e r) {X : Q d} (hX : X.PosSemidef) :
    (dilation K X).PosSemidef := hX.mul_mul_conjTranspose_same _

/-- Isometric embedding preserves multiplication, hence the pure-state projector criterion. -/
theorem dilation_mul (K : KrausChannel d e r) (X Y : Q d) :
    dilation K X * dilation K Y = dilation K (X * Y) := by
  simp only [dilation, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (stinespring_matrix K.operators).conjTranspose,
    stinespring_isometry, Matrix.one_mul]

theorem dilation_idempotent_iff (K : KrausChannel d e r) (X : Q d) :
    dilation K X * dilation K X = dilation K X ↔ X * X = X := by
  rw [dilation_mul]
  exact (dilation_injective K).eq_iff

/-- A mixed input remains a density matrix, not necessarily a pure state. -/
theorem dilation_density (K : KrausChannel d e r) {ρ : Q d}
    (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    QuantumNoBroadcastingMixed.IsDensityMatrix (dilation K ρ) :=
  ⟨dilation_positive K hρ.1, (dilation_trace K ρ).trans hρ.2⟩

/-- A zero block may be appended without altering the represented channel. -/
def append_zero (K : KrausChannel d e r) : KrausChannel d e (r + 1) where
  operators := Fin.snoc K.operators 0
  complete := by
    simpa [Fin.sum_univ_castSucc] using K.complete

theorem append_zero_channel (K : KrausChannel d e r) (X : Q d) :
    apply_channel (append_zero K) X = apply_channel K X := by
  simp [apply_channel_eq, append_zero, Fin.sum_univ_castSucc]

theorem append_zero_reduction (K : KrausChannel d e r) (X : Q d) :
    partialTrace (dilation (append_zero K) X) = partialTrace (dilation K X) := by
  simp only [partial_trace_stinespring_eq_channel, append_zero_channel]

theorem append_zero_block (K : KrausChannel d e r) (a : Fin e) (b : Fin d) :
    stinespring_matrix (append_zero K).operators (a, Fin.last r) b = 0 := by
  simp [stinespring_matrix, append_zero]

theorem identity_dilation_entry (X : Q d) (a b : Fin d) :
    dilation (identity_channel d) X (a, 0) (b, 0) = X a b := by
  simp [dilation, stinespring_matrix, identity_channel, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.one_apply]

theorem unitary_dilation_entry (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d)
    (a b : Fin d) :
    dilation (unitary_channel U) X (a, 0) (b, 0) =
      ((U : Q d) * X * (U : Q d).conjTranspose) a b := by
  rfl

namespace Regression
open QuantumHelstromStateDiscrimination.Examples

/-- A genuine rectangular 2-to-1 reset with a two-dimensional environment. -/
def rectangular_reset : KrausChannel 2 1 2 := reset_channel 0

theorem rectangular_reset_output (X : Q 2) :
    partialTrace (dilation rectangular_reset X) =
      X.trace • QuantumNoBroadcastingMixed.basisProjector (0 : Fin 1) := by
  rw [partial_trace_stinespring_eq_channel]
  exact reset_channel_apply _ X

/-- Off-diagonal coherence survives in the joint system/environment matrix. -/
theorem dephasing_joint_entry (X : Q 2) (a b : Fin 2) :
    dilation (dephasing_channel 2) X (a, a) (b, b) = X a b := by
  simp [dilation, stinespring_matrix, dephasing_channel,
    QuantumNoBroadcastingMixed.basisProjector, Matrix.diagonal,
    Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem dephasing_joint_coherence :
    dilation (dephasing_channel 2) rhoPlus (0, 0) (1, 1) = 1 / 2 := by
  rw [dephasing_joint_entry]
  rfl

theorem dephasing_reduced_coherence :
    partialTrace (dilation (dephasing_channel 2) rhoPlus) 0 1 = 0 := by
  rw [partial_trace_stinespring_eq_channel, dephasing_channel_apply]
  rfl

theorem dephasing_joint_distinct :
    dilation (dephasing_channel 2) rhoPlus ≠
      dilation (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus := by
  intro h
  have he := dilation_injective (dephasing_channel 2) h
  have hij := congrArg (fun X : Q 2 => X 0 1) he
  norm_num [rhoPlus, QuantumCPTPChannelContract.Regression.rhoMinus] at hij

theorem dephasing_reduced_equal :
    partialTrace (dilation (dephasing_channel 2) rhoPlus) =
      partialTrace (dilation (dephasing_channel 2)
        QuantumCPTPChannelContract.Regression.rhoMinus) := by
  simp only [partial_trace_stinespring_eq_channel]
  exact QuantumCPTPChannelContract.Regression.dephasing_identifies_pair

end Regression

structure QuantumStinespringDilationContractSuite : Prop where
  gram : ∀ {d e r} (K : Fin r → Matrix (Fin e) (Fin d) ℂ),
    (stinespring_matrix K).conjTranspose * stinespring_matrix K =
      ∑ j, (K j).conjTranspose * K j
  isometry : ∀ {d e r} (K : KrausChannel d e r),
    (stinespring_matrix K.operators).conjTranspose * stinespring_matrix K.operators = 1
  reduction : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    partialTrace (dilation K X) = apply_channel K X
  dual : ∀ {d e r} (K : KrausChannel d e r) (E : Q e),
    (stinespring_matrix K.operators).conjTranspose * (E ⊗ₖ (1 : Q r)) *
      stinespring_matrix K.operators = dual_channel K E
  density : ∀ {d e r} (K : KrausChannel d e r) {ρ : Q d},
    QuantumNoBroadcastingMixed.IsDensityMatrix ρ →
      QuantumNoBroadcastingMixed.IsDensityMatrix (dilation K ρ)
  recover : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    (stinespring_matrix K.operators).conjTranspose * dilation K X *
      stinespring_matrix K.operators = X
  redundant_environment : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    partialTrace (dilation (append_zero K) X) = partialTrace (dilation K X)
  joint_coherence : dilation (dephasing_channel 2)
    QuantumHelstromStateDiscrimination.Examples.rhoPlus (0, 0) (1, 1) = 1 / 2
  reduced_coherence : partialTrace (dilation (dephasing_channel 2)
    QuantumHelstromStateDiscrimination.Examples.rhoPlus) 0 1 = 0

theorem verification_suite : QuantumStinespringDilationContractSuite where
  gram := stinespring_isometry_general
  isometry := stinespring_isometry
  reduction := partial_trace_stinespring_eq_channel
  dual := stinespring_dual_map_identity
  density := dilation_density
  recover := dilation_recover
  redundant_environment := append_zero_reduction
  joint_coherence := Regression.dephasing_joint_coherence
  reduced_coherence := Regression.dephasing_reduced_coherence

end QuantumStinespringDilationContract
