import Verification.QuantumErasureCorrectabilityContract

noncomputable section
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract QuantumHelstromStateDiscrimination
open QuantumComplementaryChannelContract QuantumKnillLaflammeEnvironmentCriterion
open QuantumKnillLaflammeRecoveryNecessity QuantumReferencePreservingRecoveryContract
open QuantumErasureCorrectabilityContract QuantumErasureCorrectabilityContract.Examples
namespace ErasureCorrectabilityRegression

example : ∑ j, (erasureOperator 2 3 j).conjTranspose * erasureOperator 2 3 j = 1 :=
  erasure_complete 2 3
example (Y : Q (2 * 3)) : apply_channel (erasureChannel 2 3) Y = traceB Y := erasure_apply Y
example (Y : Q (2 * 3)) : complementary_channel (erasureChannel 2 3) Y = traceA Y :=
  erasure_complement Y
example (Y : Q (2 * 3)) : (apply_channel (erasureChannel 2 3) Y).trace = Y.trace :=
  channel_trace_preserving _ Y
example : QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel (erasureChannel 2 3)) :=
  channel_completely_positive _
example (Y : Q (2 * 3)) (h : Density Y) : Density (traceB Y) := by
  rw [← erasure_apply]; exact channel_density _ h
example (Y : Q (2 * 3)) (h : Density Y) : Density (traceA Y) := by
  rw [← erasure_complement, complementary_eq_apply]; exact channel_density _ h
example : complementary_channel (erasureChannel 2 2)
    (Matrix.single (pair (0 : Fin 2) (0 : Fin 2)) (pair 0 1) Complex.I) 0 1 = Complex.I := by
  rw [erasure_complement]
  norm_num [traceA, partialTrace_system, toProduct, pair, finProdFinEquiv,
    Matrix.single, Fin.sum_univ_succ]
example : complementary_channel (erasureChannel 2 2)
    (Matrix.single (pair (0 : Fin 2) (0 : Fin 2)) (pair 0 1) Complex.I) 1 0 = 0 := by
  rw [erasure_complement]
  norm_num [traceA, partialTrace_system, toProduct, pair, finProdFinEquiv,
    Matrix.single, Fin.sum_univ_succ]
example (v : Fin 3) : (fixedCode 2 v).conjTranspose * fixedCode 2 v = 1 := fixedCode_isometry 2 v
example (v : Fin 3) (X : Q 2) : traceB (encode (fixedCode 2 v) X) = X := fixedCode_survives v X
example (v : Fin 3) : ErasureRecoverable (fixedCode 2 v) := fixedCode_recoverable v
example : traceB (encode (fixedCode 2 (1 : Fin 3)) (Matrix.single 0 1 Complex.I)) =
    Matrix.single 0 1 Complex.I := fixedCode_survives _ _
example : entangledCode.conjTranspose * entangledCode = 1 := entangledCode_isometry
example (X : Q 2) : apply_channel (erasureChannel 2 2) (traceB (encode entangledCode X)) = X :=
  entangledCode_recovery X
example : ErasureRecoverable entangledCode := entangledCode_recoverable
example (X : Q 2) : traceA (encode entangledCode X) = X.trace • mixedLost := entangledCode_lost X
example : Density mixedLost := mixedLost_density
example : mixedLost * mixedLost ≠ mixedLost := mixedLost_not_pure
example : mixedLost 0 0 = 9/25 ∧ mixedLost 1 1 = 16/25 := by simp [mixedLost]
example : traceA (encode entangledCode (Matrix.single 0 1 Complex.I)) = 0 := by
  rw [entangledCode_lost]; simp
example : apply_channel (erasureChannel 2 2)
    (traceB (encode entangledCode (Matrix.single 0 1 Complex.I))) = Matrix.single 0 1 Complex.I :=
  entangledCode_recovery _
example (m : ℕ) (X : Joint m 2) :
    liftedRecovery (erasureChannel 4 2) entangledCode (erasureChannel 2 2) m X = X :=
  erasure_reference_recovery _ _ entangledCode_recovery m X
example : liftedRecovery (erasureChannel 4 2) entangledCode (erasureChannel 2 2)
    2 (maximallyEntangled 2) = maximallyEntangled 2 :=
  erasure_reference_recovery _ _ entangledCode_recovery 2 _
example (m : ℕ) (X : Joint m 2) :
    amplify (environmentMap (erasureChannel 4 2) entangledCode) m X = traceLogical X ⊗ₖ mixedLost := by
  apply independence_env_reference
  intro Y
  rw [erasure_complement, entangledCode_lost]
example : ∃ σ : Q 2, Density σ ∧ ∀ m (X : Joint m 2),
    amplify (environmentMap (erasureChannel 4 2) entangledCode) m X = traceLogical X ⊗ₖ σ :=
  erased_reference_independence (by decide) _ entangledCode_isometry entangledCode_recoverable
example : repetitionCode.conjTranspose * repetitionCode = 1 := repetitionCode_isometry
example (X : Q 2) : traceB (encode repetitionCode X) = apply_channel (dephasing_channel 2) X :=
  repetition_survivor X
example : traceB (encode repetitionCode (Matrix.single 0 1 (1 : ℂ))) = 0 :=
  repetition_coherence_lost
example : ¬ ErasureRecoverable repetitionCode := repetition_not_recoverable
example {s : ℕ} (R : KrausChannel 2 2 s) :
    ¬ (∀ X : Q 2, apply_channel R (traceB (encode repetitionCode X)) = X) :=
  fun h => repetition_not_recoverable ⟨s,R,h⟩
example : ¬ ∃ σ : Q 2, Density σ ∧ ∀ X : Q 2, traceA (encode repetitionCode X) = X.trace • σ := by
  intro h
  exact repetition_not_recoverable
    ((erasure_correctability_equivalence (by decide) _ repetitionCode_isometry).mpr h)
example : ¬ ∃ Λ : Q 2, StandardKnillLaflamme (erasureChannel 2 2) repetitionCode Λ := by
  intro h
  obtain ⟨s,R,hR⟩ := (recovery_necessity_equivalence (by decide) _ _ repetitionCode_isometry).mpr h
  apply repetition_not_recoverable
  refine ⟨s,R,?_⟩
  intro X
  simpa only [erasure_apply] using hR X
example : QuantumErasureCorrectabilityContractSuite := verification_suite
end ErasureCorrectabilityRegression
