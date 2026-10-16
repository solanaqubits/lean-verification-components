/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumReferencePreservingRecoveryContract

/-! Exact correction of a fixed, known erased tensor factor. The physical
index Fin (a*b) is identified with A × B using finProdFinEquiv, A first.
The complement retains B, not A. No flagged stochastic erasure model is used. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumComplementaryChannelContract QuantumKnillLaflammeEnvironmentCriterion
open QuantumKnillLaflammeRecoveryNecessity QuantumReferencePreservingRecoveryContract
open QuantumHelstromStateDiscrimination
namespace QuantumErasureCorrectabilityContract
variable {a b k s : ℕ}

def pair (i : Fin a) (j : Fin b) : Fin (a * b) := finProdFinEquiv (i,j)

@[simp] theorem pair_eq_pair (i u : Fin a) (j v : Fin b) :
    pair i j = pair u v ↔ i = u ∧ j = v := by
  simp [pair]

/-- Matrix entries of I_A tensor <j|_B in the declared flat ordering. -/
def erasureOperator (a b : ℕ) (j : Fin b) : Matrix (Fin a) (Fin (a * b)) ℂ :=
  fun i x => if pair i j = x then 1 else 0

theorem erasure_complete (a b : ℕ) :
    ∑ j, (erasureOperator a b j).conjTranspose * erasureOperator a b j = 1 := by
  ext x y
  obtain ⟨⟨u,v⟩, rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨w,z⟩, rfl⟩ := finProdFinEquiv.surjective y
  change (∑ j, (erasureOperator a b j).conjTranspose * erasureOperator a b j)
    (pair u v) (pair w z) = (1 : Q (a * b)) (pair u v) (pair w z)
  simp [erasureOperator, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_ite, ite_and, eq_comm, apply_ite (starRingEnd ℂ)]

def erasureChannel (a b : ℕ) : KrausChannel (a * b) a b where
  operators := erasureOperator a b
  complete := erasure_complete a b

/-- Trace out B; the result lives on A. -/
def traceB (Y : Q (a * b)) : Q a := partialTrace (toProduct a b Y)
/-- Trace out A; the result lives on the lost subsystem B. -/
def traceA (Y : Q (a * b)) : Q b := partialTrace_system (toProduct a b Y)

theorem erasure_apply (Y : Q (a * b)) : apply_channel (erasureChannel a b) Y = traceB Y := by
  ext i j
  simp [apply_channel_eq, erasureChannel, erasureOperator, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply, traceB, partialTrace, toProduct, pair,
    mul_ite, ite_mul]

theorem erasure_complement (Y : Q (a * b)) :
    complementary_channel (erasureChannel a b) Y = traceA Y := by
  ext i j
  simp [complementary_entry, erasureChannel, erasureOperator, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.trace, Matrix.diag, traceA, partialTrace_system,
    toProduct, pair, mul_ite, ite_mul]

/-- Recovery family size is independent and existentially quantified. -/
def ErasureRecoverable (J : Matrix (Fin (a * b)) (Fin k) ℂ) : Prop :=
  ∃ s, ∃ R : KrausChannel a k s, ∀ X : Q k, apply_channel R (traceB (encode J X)) = X

theorem erasure_correctability_equivalence (hk : 0 < k)
    (J : Matrix (Fin (a * b)) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1) :
    ErasureRecoverable J ↔ ∃ σ : Q b, Density σ ∧
      ∀ X : Q k, traceA (encode J X) = X.trace • σ := by
  simpa only [ErasureRecoverable, Recoverable, ExactRecovery, EnvironmentConstant,
    erasure_apply, erasure_complement] using
    recovery_environment_density_equivalence hk (erasureChannel a b) J hJ

theorem erasure_reference_recovery (J : Matrix (Fin (a * b)) (Fin k) ℂ)
    (R : KrausChannel a k s) (h : ∀ X : Q k, apply_channel R (traceB (encode J X)) = X)
    (m : ℕ) (X : Joint m k) : liftedRecovery (erasureChannel a b) J R m X = X := by
  apply reference_preserving_recovery
  intro Y
  simpa only [erasure_apply] using h Y

theorem erased_reference_independence (hk : 0 < k)
    (J : Matrix (Fin (a * b)) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    (h : ErasureRecoverable J) :
    ∃ σ : Q b, Density σ ∧ ∀ m (X : Joint m k),
      amplify (environmentMap (erasureChannel a b) J) m X = traceLogical X ⊗ₖ σ := by
  obtain ⟨σ,hσ,hc⟩ := (erasure_correctability_equivalence hk J hJ).mp h
  refine ⟨σ,hσ,independence_env_reference _ _ _ ?_⟩
  intro Y
  simpa only [erasure_complement] using hc Y

namespace Examples
/-- |psi> maps to |psi> tensor |v>; v is a fixed erased-basis label. -/
def fixedCode (k : ℕ) (v : Fin b) : Matrix (Fin (k * b)) (Fin k) ℂ :=
  (erasureOperator k b v).conjTranspose

theorem fixedCode_isometry (k : ℕ) (v : Fin b) :
    (fixedCode k v).conjTranspose * fixedCode k v = 1 := by
  ext i j
  simp [fixedCode, erasureOperator, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, mul_ite]

theorem fixedCode_survives (v : Fin b) (X : Q k) :
    traceB (encode (fixedCode k v) X) = X := by
  ext i j
  simp [traceB, partialTrace, toProduct, encode, fixedCode, erasureOperator,
    Matrix.mul_apply, Matrix.conjTranspose_apply, pair, mul_ite, ite_mul, ite_and]

theorem fixedCode_recoverable (v : Fin b) : ErasureRecoverable (fixedCode k v) := by
  refine ⟨1,identity_channel k,?_⟩
  intro X
  rw [fixedCode_survives, identity_channel_apply]

/-- A=(logical qubit, retained auxiliary qubit), B=erased auxiliary qubit.
The fixed auxiliary state is (3/5)|00>+(4/5)|11>. -/
def entangledCode : Matrix (Fin (4 * 2)) (Fin 2) ℂ :=
  !![3/5,0; 0,0; 0,0; 4/5,0; 0,3/5; 0,0; 0,0; 0,4/5]

def mixedLost : Q 2 := !![9/25,0; 0,16/25]

theorem entangledCode_isometry : entangledCode.conjTranspose * entangledCode = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [entangledCode, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat]

/-- Explicit recovery: trace out the retained auxiliary qubit in A. -/
theorem entangledCode_recovery (X : Q 2) :
    apply_channel (erasureChannel 2 2) (traceB (encode entangledCode X)) = X := by
  rw [erasure_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceB, partialTrace, toProduct, encode, entangledCode, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, finProdFinEquiv,
      Matrix.vecMul, dotProduct, map_ofNat] <;> ring

theorem entangledCode_lost (X : Q 2) :
    traceA (encode entangledCode X) = X.trace • mixedLost := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceA, partialTrace_system, toProduct, encode, entangledCode, mixedLost,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      finProdFinEquiv, Matrix.trace, Matrix.diag, Matrix.vecMul, dotProduct, map_ofNat] <;> ring

theorem entangledCode_recoverable : ErasureRecoverable entangledCode :=
  ⟨2,erasureChannel 2 2,entangledCode_recovery⟩

theorem mixedLost_density : Density mixedLost := by
  apply environment_density (by decide) (erasureChannel 4 2) entangledCode
    entangledCode_isometry mixedLost
  apply (knill_laflamme_equiv_environment _ _ _).mpr
  intro X
  rw [erasure_complement, entangledCode_lost]

/-- Strictly mixed: the lost state is not an idempotent rank-one density. -/
theorem mixedLost_not_pure : mixedLost * mixedLost ≠ mixedLost := by
  intro h
  have he := congrArg (fun M : Q 2 => M 0 0) h
  norm_num [mixedLost, Matrix.mul_apply, Fin.sum_univ_succ] at he

/-- Repetition encoding into A tensor B, ordered 00,01,10,11. -/
def repetitionCode : Matrix (Fin (2 * 2)) (Fin 2) ℂ := !![1,0; 0,0; 0,0; 0,1]

theorem repetitionCode_isometry : repetitionCode.conjTranspose * repetitionCode = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [repetitionCode, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem repetition_survivor (X : Q 2) :
    traceB (encode repetitionCode X) = apply_channel (dephasing_channel 2) X := by
  rw [dephasing_channel_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceB, partialTrace, toProduct, encode, repetitionCode, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, finProdFinEquiv, Matrix.vecMul, dotProduct]

theorem repetition_coherence_lost :
    traceB (encode repetitionCode (Matrix.single 0 1 (1 : ℂ))) = 0 := by
  rw [repetition_survivor, dephasing_channel_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem repetition_not_recoverable : ¬ ErasureRecoverable repetitionCode := by
  rintro ⟨s,R,h⟩
  apply dephasing_not_recoverable
  refine ⟨s,R,?_⟩
  intro X
  have hx := h X
  rw [repetition_survivor] at hx
  change apply_channel R (apply_channel (dephasing_channel 2) (encode (1 : Q 2) X)) = X
  simpa only [encode, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using hx

end Examples

structure QuantumErasureCorrectabilityContractSuite : Prop where
  complete : ∀ a b, ∑ j,
    (erasureOperator a b j).conjTranspose * erasureOperator a b j = 1
  partial_trace : ∀ {a b} (Y : Q (a * b)), apply_channel (erasureChannel a b) Y = traceB Y
  complement : ∀ {a b} (Y : Q (a * b)),
    complementary_channel (erasureChannel a b) Y = traceA Y
  criterion : ∀ {a b k}, 0 < k → ∀ (J : Matrix (Fin (a * b)) (Fin k) ℂ),
    J.conjTranspose * J = 1 → (ErasureRecoverable J ↔ ∃ σ : Q b, Density σ ∧
      ∀ X : Q k, traceA (encode J X) = X.trace • σ)
  reference : ∀ {a b k s} (J : Matrix (Fin (a * b)) (Fin k) ℂ) (R : KrausChannel a k s),
    (∀ X : Q k, apply_channel R (traceB (encode J X)) = X) →
      ∀ m (X : Joint m k), liftedRecovery (erasureChannel a b) J R m X = X
  decoupling : ∀ {a b k}, 0 < k → ∀ (J : Matrix (Fin (a * b)) (Fin k) ℂ),
    J.conjTranspose * J = 1 → ErasureRecoverable J →
      ∃ σ : Q b, Density σ ∧ ∀ m (X : Joint m k),
        amplify (environmentMap (erasureChannel a b) J) m X = traceLogical X ⊗ₖ σ
  fixed_code : ∀ {k b} (v : Fin b), ErasureRecoverable (Examples.fixedCode k v)
  entangled_code : ErasureRecoverable Examples.entangledCode
  mixed_lost : Density Examples.mixedLost ∧
    Examples.mixedLost * Examples.mixedLost ≠ Examples.mixedLost
  entangled_environment : ∀ X : Q 2,
    traceA (encode Examples.entangledCode X) = X.trace • Examples.mixedLost
  repetition_obstruction : ¬ ErasureRecoverable Examples.repetitionCode

theorem verification_suite : QuantumErasureCorrectabilityContractSuite where
  complete := erasure_complete
  partial_trace := erasure_apply
  complement := erasure_complement
  criterion := erasure_correctability_equivalence
  reference := erasure_reference_recovery
  decoupling := erased_reference_independence
  fixed_code := Examples.fixedCode_recoverable
  entangled_code := Examples.entangledCode_recoverable
  mixed_lost := ⟨Examples.mixedLost_density,Examples.mixedLost_not_pure⟩
  entangled_environment := Examples.entangledCode_lost
  repetition_obstruction := Examples.repetition_not_recoverable

end QuantumErasureCorrectabilityContract
