/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumKnillLaflammeRecoveryNecessity

/-! Exact recovery with arbitrary finite references, environment decoupling and
one normalized maximally entangled test. Product indices are reference first.
The flat-index wrapper uses finProdFinEquiv explicitly. No approximate or
numerical recovery statement is made. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeRecoveryNecessity
open QuantumComplementaryChannelContract
namespace QuantumReferencePreservingRecoveryContract
variable {k d e r s : ℕ}
abbrev Joint (m n : ℕ) := Matrix (Fin m × Fin n) (Fin m × Fin n) ℂ

/-- The existing singleton Kraus linear map for encoding. -/
def encodingMap (J : Matrix (Fin d) (Fin k) ℂ) : Q k →ₗ[ℂ] Q d :=
  QuantumNoBroadcastingMixed.krausMap (fun _ : Fin 1 => J)

@[simp] theorem encodingMap_apply (J : Matrix (Fin d) (Fin k) ℂ) (X : Q k) :
    encodingMap J X = encode J X := by
  simp [encodingMap, QuantumNoBroadcastingMixed.krausMap, encode]

abbrev amplify := @QuantumNoBroadcastingMixed.amplify

def recoveryMap (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) : Q k →ₗ[ℂ] Q k :=
  (apply_channel R).comp ((apply_channel E).comp (encodingMap J))

def liftedRecovery (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) (m : ℕ) (X : Joint m k) : Joint m k :=
  amplify (apply_channel R) m (amplify (apply_channel E) m (amplify (encodingMap J) m X))

theorem liftedRecovery_eq (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s) (m : ℕ) (X : Joint m k) :
    liftedRecovery E J R m X = amplify (recoveryMap E J R) m X := rfl

/-- The tensor interpretation uses the existing Kraus amplification theorem. -/
theorem encoding_amplify (J : Matrix (Fin d) (Fin k) ℂ) (m : ℕ) (X : Joint m k) :
    amplify (encodingMap J) m X =
      ((1 : Q m) ⊗ₖ J) * X * ((1 : Q m) ⊗ₖ J).conjTranspose := by
  simpa [encodingMap] using
    QuantumNoBroadcastingMixed.amplify_kraus (fun _ : Fin 1 => J) m X

theorem channel_amplify (E : KrausChannel d e r) (m : ℕ) (X : Joint m d) :
    amplify (apply_channel E) m X = ∑ a,
      ((1 : Q m) ⊗ₖ E.operators a) * X * ((1 : Q m) ⊗ₖ E.operators a).conjTranspose :=
  QuantumNoBroadcastingMixed.amplify_kraus E.operators m X

/-- The same R works for every reference dimension, including the empty one. -/
theorem reference_preserving_recovery (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s)
    (h : ExactRecovery E J R) (m : ℕ) (X : Joint m k) :
    liftedRecovery E J R m X = X := by
  have he : recoveryMap E J R = LinearMap.id := by
    apply LinearMap.ext
    intro Y
    simpa only [recoveryMap, LinearMap.comp_apply, encodingMap_apply, LinearMap.id_apply]
      using h Y
  rw [liftedRecovery_eq, he]
  rfl

def toProduct (m n : ℕ) (X : Q (m * n)) : Joint m n :=
  fun i j => X (finProdFinEquiv i) (finProdFinEquiv j)

def fromProduct (m n : ℕ) (X : Joint m n) : Q (m * n) :=
  fun i j => X (finProdFinEquiv.symm i) (finProdFinEquiv.symm j)

theorem reference_preserving_recovery_flat (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s)
    (h : ExactRecovery E J R) (m : ℕ) (X : Q (m * k)) :
    fromProduct m k (liftedRecovery E J R m (toProduct m k X)) = X := by
  rw [reference_preserving_recovery E J R h]
  ext i j
  exact congrArg₂ X (finProdFinEquiv.apply_symm_apply i) (finProdFinEquiv.apply_symm_apply j)

/-- Trace over the logical (second) factor; the reference factor remains. -/
def traceLogical {m n : ℕ} (X : Joint m n) : Q m := fun a b => ∑ i, X (a,i) (b,i)

def environmentMap (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ) :
    Q k →ₗ[ℂ] Q r := (apply_channel (complementary_kraus E)).comp (encodingMap J)

theorem independence_env_reference (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (σ : Q r) (h : EnvironmentConstant E J σ)
    (m : ℕ) (X : Joint m k) :
    amplify (environmentMap E J) m X = traceLogical X ⊗ₖ σ := by
  ext i j
  have hc := congrArg (fun M : Q r => M i.2 j.2)
    (h (fun a b => X (i.1,a) (j.1,b)))
  simpa only [environmentMap, amplify, QuantumNoBroadcastingMixed.amplify,
    LinearMap.comp_apply, encodingMap_apply, complementary_eq_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.trace, traceLogical,
    Matrix.kroneckerMap_apply, Matrix.diag] using hc

/-- Density environment follows from recovery; it is not a new assumption. -/
theorem recovery_decouples_environment (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (hJ : J.conjTranspose * J = 1)
    (R : KrausChannel e k s) (h : ExactRecovery E J R) :
    ∃ σ : Q r, QuantumHelstromStateDiscrimination.Density σ ∧
      ∀ m (X : Joint m k), amplify (environmentMap E J) m X = traceLogical X ⊗ₖ σ := by
  obtain ⟨σ, hσ, hc⟩ := (recovery_environment_density_equivalence hk E J hJ).mp ⟨s,R,h⟩
  exact ⟨σ,hσ,independence_env_reference E J σ hc⟩

/-- Normalized maximally entangled density matrix, reference index first.
The entry formula avoids numerical square roots; normalization requires k>0. -/
def maximallyEntangled (k : ℕ) : Joint k k :=
  fun i j => if i.1 = i.2 ∧ j.1 = j.2 then (k : ℂ)⁻¹ else 0

theorem maximallyEntangled_block (a b : Fin k) :
    (fun i j => maximallyEntangled k (a,i) (b,j) : Q k) = (k : ℂ)⁻¹ • Matrix.single a b 1 := by
  ext i j
  change (if a = i ∧ b = j then (k : ℂ)⁻¹ else 0) =
    (k : ℂ)⁻¹ * (if a = i ∧ b = j then 1 else 0)
  split_ifs <;> simp

/-- Extracting a block of the normalized Choi state recovers a matrix unit. -/
theorem entangled_test_iff_identity (hk : 0 < k) (T : Q k →ₗ[ℂ] Q k) :
    amplify T k (maximallyEntangled k) = maximallyEntangled k ↔ ∀ X, T X = X := by
  constructor
  · intro h
    have hn : (k : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk))
    have hs (a b : Fin k) : T (Matrix.single a b 1) = Matrix.single a b 1 := by
      have hb := congrArg (fun M : Joint k k => (fun i j => M (a,i) (b,j) : Q k)) h
      change T (fun i j => maximallyEntangled k (a,i) (b,j) : Q k) =
        (fun i j => maximallyEntangled k (a,i) (b,j)) at hb
      rw [maximallyEntangled_block, map_smul] at hb
      exact (smul_right_injective _ hn) hb
    intro X
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum]
    have ht (a b : Fin k) : T (Matrix.single a b (X a b)) = Matrix.single a b (X a b) := by
      have he : Matrix.single a b (X a b) = (X a b) • Matrix.single a b (1 : ℂ) := by simp
      rw [he, map_smul, hs]
    simp_rw [ht]
    exact (Matrix.matrix_eq_sum_single X).symm
  · intro h
    ext i j
    exact congrArg (fun M : Q k => M i.2 j.2) (h _)

theorem maximally_entangled_recovery_equivalence (hk : 0 < k) (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s) :
    liftedRecovery E J R k (maximallyEntangled k) = maximallyEntangled k ↔ ExactRecovery E J R := by
  rw [liftedRecovery_eq, entangled_test_iff_identity hk]
  simp only [recoveryMap, LinearMap.comp_apply, encodingMap_apply, ExactRecovery]

/-- Positivity and unit trace of the actual entangled test state. -/
theorem maximallyEntangled_density (hk : 0 < k) :
    QuantumNoBroadcastingMixed.IsDensityMatrix (maximallyEntangled k) := by
  let v : Fin k × Fin k → ℂ := fun i => if i.1 = i.2 then 1 else 0
  have he : maximallyEntangled k = (k : ℂ)⁻¹ • Matrix.vecMulVec v (star v) := by
    ext i j
    change (if i.1 = i.2 ∧ j.1 = j.2 then (k : ℂ)⁻¹ else 0) =
      (k : ℂ)⁻¹ * ((if i.1 = i.2 then 1 else 0) * star (if j.1 = j.2 then 1 else 0))
    split_ifs <;> simp_all
  constructor
  · rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star v).smul (inv_nonneg.mpr (Nat.cast_nonneg k))
  · simp [Matrix.trace, Matrix.diag, maximallyEntangled, Fintype.sum_prod_type,
      Nat.ne_of_gt hk]

theorem traceLogical_eq_partialTrace {m n : ℕ} (X : Joint m n) :
    traceLogical X = partialTrace X := rfl

/-- A Bell coherence is present before dephasing. -/
theorem bell_coherence : maximallyEntangled 2 (0,0) (1,1) = 1/2 := by
  norm_num [maximallyEntangled]

theorem dephasing_bell_coherence :
    amplify (apply_channel (dephasing_channel 2)) 2 (maximallyEntangled 2) (0,0) (1,1) = 0 := by
  change apply_channel (dephasing_channel 2) _ 0 1 = 0
  rw [dephasing_channel_apply]
  simp

theorem dephasing_preserves_basis (a : Fin 2) :
    apply_channel (dephasing_channel 2) (Matrix.single a a 1) = Matrix.single a a 1 := by
  rw [dephasing_channel_apply]
  ext i j
  by_cases h : i = j
  · subst j; simp
  · have hn : ¬(a = i ∧ a = j) := fun ⟨hai, haj⟩ => h (hai.symm.trans haj)
    simp [Matrix.single_apply, h, hn]

/-- No recovery family of any finite size repairs the encoded Bell state. -/
theorem dephasing_bell_not_recoverable (R : KrausChannel 2 2 s) :
    liftedRecovery (dephasing_channel 2) (1 : Q 2) R 2 (maximallyEntangled 2) ≠
      maximallyEntangled 2 := by
  intro h
  exact dephasing_not_recoverable ⟨s,R,
    (maximally_entangled_recovery_equivalence (by decide) _ _ _).mp h⟩

structure QuantumReferencePreservingRecoveryContractSuite : Prop where
  tensor_encoding : ∀ {k d} (J : Matrix (Fin d) (Fin k) ℂ) m (X : Joint m k),
    amplify (encodingMap J) m X = ((1 : Q m) ⊗ₖ J) * X * ((1 : Q m) ⊗ₖ J).conjTranspose
  recovery : ∀ {k d e r s} (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s), ExactRecovery E J R → ∀ m (X : Joint m k),
      liftedRecovery E J R m X = X
  flat_recovery : ∀ {k d e r s} (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (R : KrausChannel e k s), ExactRecovery E J R → ∀ m (X : Q (m * k)),
      fromProduct m k (liftedRecovery E J R m (toProduct m k X)) = X
  environment : ∀ {k d e r} (E : KrausChannel d e r) (J : Matrix (Fin d) (Fin k) ℂ)
    (σ : Q r), EnvironmentConstant E J σ → ∀ m (X : Joint m k),
      amplify (environmentMap E J) m X = traceLogical X ⊗ₖ σ
  derived_environment : ∀ {k d e r s}, 0 < k → ∀ (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ), J.conjTranspose * J = 1 → ∀ (R : KrausChannel e k s),
    ExactRecovery E J R → ∃ σ : Q r, QuantumHelstromStateDiscrimination.Density σ ∧
      ∀ m (X : Joint m k), amplify (environmentMap E J) m X = traceLogical X ⊗ₖ σ
  entangled_density : ∀ {k}, 0 < k →
    QuantumNoBroadcastingMixed.IsDensityMatrix (maximallyEntangled k)
  entangled_criterion : ∀ {k d e r s}, 0 < k → ∀ (E : KrausChannel d e r)
    (J : Matrix (Fin d) (Fin k) ℂ) (R : KrausChannel e k s),
    liftedRecovery E J R k (maximallyEntangled k) = maximallyEntangled k ↔ ExactRecovery E J R
  dephasing_population : ∀ a : Fin 2,
    apply_channel (dephasing_channel 2) (Matrix.single a a 1) = Matrix.single a a 1
  dephasing_coherence :
    amplify (apply_channel (dephasing_channel 2)) 2 (maximallyEntangled 2) (0,0) (1,1) = 0
  dephasing_impossible : ∀ {s} (R : KrausChannel 2 2 s),
    liftedRecovery (dephasing_channel 2) (1 : Q 2) R 2 (maximallyEntangled 2) ≠ maximallyEntangled 2

theorem verification_suite : QuantumReferencePreservingRecoveryContractSuite where
  tensor_encoding := encoding_amplify
  recovery := reference_preserving_recovery
  flat_recovery := reference_preserving_recovery_flat
  environment := independence_env_reference
  derived_environment := recovery_decouples_environment
  entangled_density := maximallyEntangled_density
  entangled_criterion := maximally_entangled_recovery_equivalence
  dephasing_population := dephasing_preserves_basis
  dephasing_coherence := dephasing_bell_coherence
  dephasing_impossible := dephasing_bell_not_recoverable

end QuantumReferencePreservingRecoveryContract
