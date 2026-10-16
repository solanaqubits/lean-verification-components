import Verification.QuantumCPTPChannelContract

open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
open QuantumHelstromStateDiscrimination QuantumHelstromStateDiscrimination.Examples
open QuantumChannelTraceDistanceContract QuantumCPTPChannelContract
open QuantumCPTPChannelContract.Regression

example : QuantumCPTPChannelContractSuite := QuantumCPTPChannelContract.verification_suite
example {d e r : ℕ} (K : KrausChannel d e r) (X Y : Q d) :
    apply_channel K (X + Y) = apply_channel K X + apply_channel K Y := channel_add K X Y
example {d e r : ℕ} (K : KrausChannel d e r) (z : ℂ) (X : Q d) :
    apply_channel K (z • X) = z • apply_channel K X := channel_smul K z X
example (K : KrausChannel 2 3 4) (X : Q 2) : (apply_channel K X).trace = X.trace :=
  channel_trace_preserving K X
example (K : KrausChannel 2 3 4) (X : Q 2) (hX : X.PosSemidef) :
    (apply_channel K X).PosSemidef := channel_positive K hX
example (K : KrausChannel 2 3 4) (a : ℕ)
    (X : Matrix (Fin a × Fin 2) (Fin a × Fin 2) ℂ) (hX : X.PosSemidef) :
    (QuantumNoBroadcastingMixed.amplify (apply_channel K) a X).PosSemidef :=
  channel_completely_positive K a X hX
example (K : KrausChannel 2 3 4) : Density (apply_channel K rhoPlus) := channel_density K rhoPlus_density
example (K : KrausChannel 2 3 4) : dual_channel K 1 = 1 := dual_unital K
example (K : KrausChannel 2 3 4) (E : Q 3) (X : Q 2) :
    (E * apply_channel K X).trace = (dual_channel K E * X).trace := trace_adjoint_identity K E X
example (K : KrausChannel 2 3 4) (E : Effect 3) : (pullback_effect K E).matrix.PosSemidef :=
  (pullback_effect K E).positive
example (K : KrausChannel 2 3 4) (E : Effect 3) : (1 - (pullback_effect K E).matrix).PosSemidef :=
  (pullback_effect K E).complement
example (K : KrausChannel 2 3 4) :
    trace_distance (apply_channel K qubitZero) (apply_channel K rhoPlus) ≤ 1 / Real.sqrt 2 := by
  simpa only [QuantumChannelTraceDistanceContract.Regression.noncommuting_distance] using
    trace_distance_contractive K qubitZero_density rhoPlus_density
example (K : KrausChannel 2 3 4) :
    trace_norm (apply_channel K qubitZero - apply_channel K rhoPlus) ≤ trace_norm (qubitZero - rhoPlus) :=
  trace_norm_contractive K qubitZero_density rhoPlus_density
example (K : KrausChannel 2 3 4) :
    optimal_success fair (apply_channel K qubitZero) (apply_channel K rhoPlus) ≤
      optimal_success fair qubitZero rhoPlus := optimal_success_contractive K qubitZero_density rhoPlus_density
example (F : QuantumNoBroadcastingMixed.Channel (Fin 2) (Fin 3)) :
    trace_distance (F.toLinearMap qubitZero) (F.toLinearMap rhoOne) ≤ 1 := by
  simpa only [QuantumChannelTraceDistanceContract.Regression.orthogonal_distance] using
    cptp_trace_distance_contractive F qubitZero_density rhoOne_density
example (F : QuantumNoBroadcastingMixed.Channel (Fin 2) (Fin 3))
    (G : QuantumNoBroadcastingMixed.Channel (Fin 3) (Fin 1)) :
    trace_distance ((G.comp F).toLinearMap qubitZero) ((G.comp F).toLinearMap rhoOne) ≤
      trace_distance qubitZero rhoOne := cptp_trace_distance_contractive (G.comp F) qubitZero_density rhoOne_density
example (X : Q 0) : apply_channel (identity_channel 0) X = X := identity_channel_apply X
example : trace_distance (apply_channel (identity_channel 2) qubitZero)
    (apply_channel (identity_channel 2) rhoOne) = 1 := by
  rw [identity_preserves_distance, QuantumChannelTraceDistanceContract.Regression.orthogonal_distance]
example (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    trace_distance (apply_channel (unitary_channel U) qubitZero)
      (apply_channel (unitary_channel U) rhoPlus) = 1 / Real.sqrt 2 := by
  rw [unitary_preserves_distance U qubitZero_density rhoPlus_density,
    QuantumChannelTraceDistanceContract.Regression.noncommuting_distance]
example (U : Matrix.unitaryGroup (Fin 2) ℂ) (X : Q 2) :
    apply_channel (unitary_channel (star U)) (apply_channel (unitary_channel U) X) = X :=
  unitary_inverse_apply U X
example : trace_distance (apply_channel (reset_channel (0 : Fin 3)) qubitZero)
    (apply_channel (reset_channel (0 : Fin 3)) rhoOne) = 0 := reset_distance_zero _ qubitZero_density rhoOne_density
example : apply_channel (reset_channel (0 : Fin 2)) rhoPlus = qubitZero := by
  rw [reset_density _ rhoPlus_density]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [QuantumNoBroadcastingMixed.basisProjector, qubitZero, Matrix.diagonal]
-- A trace-preserving channel need not be unital; its dual is unital.
example : apply_channel (reset_channel (0 : Fin 2)) (1 : Q 2) ≠ 1 := by
  intro h
  have h11 := congrArg (fun X : Q 2 => X 1 1) h
  norm_num [reset_channel_apply, QuantumNoBroadcastingMixed.basisProjector, Matrix.diagonal] at h11
example : apply_channel (dephasing_channel 2) rhoPlus = qubitMixed := by
  rw [dephasing_channel_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rhoPlus, qubitMixed, Matrix.diagonal]
example : apply_channel (dephasing_channel 2) qubitZero = qubitZero := by
  rw [dephasing_channel_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [qubitZero, Matrix.diagonal]
example : Density rhoMinus := rhoMinus_density
example : apply_channel (dephasing_channel 2) rhoPlus = apply_channel (dephasing_channel 2) rhoMinus :=
  dephasing_identifies_pair
example : trace_distance (apply_channel (dephasing_channel 2) rhoPlus)
    (apply_channel (dephasing_channel 2) rhoMinus) = 0 := by
  rw [dephasing_identifies_pair, trace_distance_self]
example : trace_distance (apply_channel (dephasing_channel 2) rhoPlus)
    (apply_channel (dephasing_channel 2) rhoMinus) < trace_distance rhoPlus rhoMinus := dephasing_strict_loss
example (K : KrausChannel 2 3 4) (E : FinitePOVM 3 5) :
    TV (prob_dist E (apply_channel K qubitZero)) (prob_dist E (apply_channel K rhoPlus)) ≤
      trace_distance qubitZero rhoPlus :=
  (tv_le_trace_distance_under_povm (channel_density K qubitZero_density)
    (channel_density K rhoPlus_density) E).trans (trace_distance_contractive K qubitZero_density rhoPlus_density)
