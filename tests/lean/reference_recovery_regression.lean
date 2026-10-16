import Verification.QuantumReferencePreservingRecoveryContract

noncomputable section
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumKnillLaflammeGeneralRecoveryTheorem
open QuantumKnillLaflammeRecoveryNecessity QuantumReferencePreservingRecoveryContract
namespace ReferenceRecoveryRegression
abbrev C := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexCode
abbrev E := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.complexChannel
abbrev J := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.logicalCode
abbrev R := generalRecovery C
abbrev Z := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.zeroCode
abbrev EZ := QuantumOrthogonalErrorRecoveryContract.Examples.sectorChannel
abbrev D := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.repeatedCode
abbrev ED := QuantumUnitaryKrausDiagonalizationRecoveryContract.Examples.repeatedChannel
abbrev T := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularCode
abbrev ET := QuantumKnillLaflammeGeneralRecoveryTheorem.Examples.rectangularChannel

example (m : ℕ) (X : Joint m 2) : liftedRecovery E J R m X = X :=
  reference_preserving_recovery E J R (general_recovery_theorem C) m X
example (X : Q (3*2)) : fromProduct 3 2 (liftedRecovery E J R 3 (toProduct 3 2 X)) = X :=
  reference_preserving_recovery_flat E J R (general_recovery_theorem C) 3 X
example (X : Joint 0 2) : liftedRecovery E J R 0 X = X :=
  reference_preserving_recovery E J R (general_recovery_theorem C) 0 X
example (X : Joint 1 2) : liftedRecovery E J R 1 X = X :=
  reference_preserving_recovery E J R (general_recovery_theorem C) 1 X
example : liftedRecovery E J R 2 (maximallyEntangled 2) = maximallyEntangled 2 :=
  reference_preserving_recovery E J R (general_recovery_theorem C) 2 _
example : liftedRecovery E J R 3 (Matrix.single (0,0) (2,1) Complex.I) =
    Matrix.single (0,0) (2,1) Complex.I :=
  reference_preserving_recovery E J R (general_recovery_theorem C) 3 _
example {s : ℕ} (R' : KrausChannel 4 2 s) (h : ExactRecovery E J R')
    (m : ℕ) (X : Joint m 2) : liftedRecovery E J R' m X = X :=
  reference_preserving_recovery E J R' h m X
example {s : ℕ} (R' : KrausChannel 4 2 s) :
    liftedRecovery E J R' 2 (maximallyEntangled 2) = maximallyEntangled 2 ↔ ExactRecovery E J R' :=
  maximally_entangled_recovery_equivalence (by decide) E J R'
example (m : ℕ) (X : Joint m 2) :
    amplify (environmentMap E J) m X = traceLogical X ⊗ₖ C.coefficients.transpose :=
  independence_env_reference E J _ ((knill_laflamme_equiv_environment _ _ _).mp
    ((standard_iff_transpose _ _ _).mp C.knill_laflamme)) m X
example : ∃ σ : Q 2, QuantumHelstromStateDiscrimination.Density σ ∧
    ∀ m (X : Joint m 2), amplify (environmentMap E J) m X = traceLogical X ⊗ₖ σ :=
  recovery_decouples_environment (by decide) E J C.isometry R (general_recovery_theorem C)
example (m : ℕ) (X : Joint m 2) : amplify (encodingMap J) m X =
    ((1 : Q m) ⊗ₖ J) * X * ((1 : Q m) ⊗ₖ J).conjTranspose := encoding_amplify J m X
example (m : ℕ) (X : Joint m 4) : amplify (apply_channel E) m X =
    ∑ a, ((1 : Q m) ⊗ₖ E.operators a) * X * ((1 : Q m) ⊗ₖ E.operators a).conjTranspose :=
  channel_amplify E m X
example (X : Joint 3 2) : traceLogical X = partialTrace X := traceLogical_eq_partialTrace X
example : QuantumNoBroadcastingMixed.IsDensityMatrix (maximallyEntangled 2) :=
  maximallyEntangled_density (by decide)
example : QuantumNoBroadcastingMixed.IsDensityMatrix (maximallyEntangled 3) :=
  maximallyEntangled_density (by decide)
example : maximallyEntangled 2 (0,0) (1,1) = 1/2 := bell_coherence
example : maximallyEntangled 2 (0,0) (0,0) = 1/2 := by norm_num [maximallyEntangled]
example : maximallyEntangled 2 (0,1) (0,1) = 0 := by norm_num [maximallyEntangled]
example : maximallyEntangled 3 (0,0) (2,2) = 1/3 := by norm_num [maximallyEntangled]
example : traceLogical (maximallyEntangled 2) = (1/2 : ℂ) • (1 : Q 2) := by
  ext a b
  fin_cases a <;> fin_cases b <;> norm_num [traceLogical, maximallyEntangled, Fin.sum_univ_succ]
example (A : Q 2 →ₗ[ℂ] Q 2) :
    amplify A 2 (maximallyEntangled 2) = maximallyEntangled 2 ↔ ∀ X, A X = X :=
  entangled_test_iff_identity (by decide) A
example : (fun a b : Fin 2 => maximallyEntangled 2 (0,a) (1,b)) =
    (2 : ℂ)⁻¹ • Matrix.single 0 1 1 := maximallyEntangled_block 0 1
example (X : Joint 3 2) : liftedRecovery EZ J (generalRecovery Z) 3 X = X :=
  reference_preserving_recovery _ _ _ (general_recovery_theorem Z) 3 X
example : liftedRecovery ED J (generalRecovery D) 2 (maximallyEntangled 2) = maximallyEntangled 2 :=
  reference_preserving_recovery _ _ _ (general_recovery_theorem D) 2 _
example (m : ℕ) (X : Joint m 2) : liftedRecovery ET (1 : Q 2) (generalRecovery T) m X = X :=
  reference_preserving_recovery _ _ _ (general_recovery_theorem T) m X
example : liftedRecovery ET (1 : Q 2) (generalRecovery T) 2 (maximallyEntangled 2) = maximallyEntangled 2 :=
  reference_preserving_recovery _ _ _ (general_recovery_theorem T) 2 _
example (a : Fin 2) : apply_channel (dephasing_channel 2) (Matrix.single a a 1) = Matrix.single a a 1 :=
  dephasing_preserves_basis a
example : amplify (apply_channel (dephasing_channel 2)) 2 (maximallyEntangled 2) (0,0) (1,1) = 0 :=
  dephasing_bell_coherence
example : amplify (apply_channel (dephasing_channel 2)) 2 (maximallyEntangled 2) ≠ maximallyEntangled 2 := by
  intro h
  have he := congrArg (fun M : Joint 2 2 => M (0,0) (1,1)) h
  rw [dephasing_bell_coherence, bell_coherence] at he
  norm_num at he
example {s : ℕ} (R' : KrausChannel 2 2 s) :
    liftedRecovery (dephasing_channel 2) (1 : Q 2) R' 2 (maximallyEntangled 2) ≠ maximallyEntangled 2 :=
  dephasing_bell_not_recoverable R'
example : QuantumReferencePreservingRecoveryContractSuite := verification_suite
end ReferenceRecoveryRegression
