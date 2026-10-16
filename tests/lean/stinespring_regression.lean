import Verification.QuantumStinespringDilationContract

open scoped BigOperators Kronecker ComplexOrder
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumStinespringDilationContract
open QuantumHelstromStateDiscrimination.Examples

-- Arbitrary dimensions, including unequal input and output dimensions.
example {d e r} (K : Fin r → Matrix (Fin e) (Fin d) ℂ) :
    (stinespring_matrix K).conjTranspose * stinespring_matrix K =
      ∑ j, (K j).conjTranspose * K j := stinespring_isometry_general K

example {d e r} (K : KrausChannel d e r) :
    (stinespring_matrix K.operators).conjTranspose * stinespring_matrix K.operators = 1 :=
  stinespring_isometry K

example {d e r} (K : KrausChannel d e r) (X : Q d) :
    partialTrace (dilation K X) = apply_channel K X := partial_trace_stinespring_eq_channel K X

example {d e r} (K : KrausChannel d e r) (E : Q e) :
    (stinespring_matrix K.operators).conjTranspose * (E ⊗ₖ (1 : Q r)) *
      stinespring_matrix K.operators = dual_channel K E := stinespring_dual_map_identity K E

example {d e r} (K : KrausChannel d e r) {ρ : Q d}
    (h : QuantumNoBroadcastingMixed.IsDensityMatrix ρ) :
    QuantumNoBroadcastingMixed.IsDensityMatrix (dilation K ρ) := dilation_density K h

example {d e r} (K : KrausChannel d e r) (X : Q d) :
    (dilation K X).trace = X.trace := dilation_trace K X

example {d e r} (K : KrausChannel d e r) : Function.Injective (dilation K) := dilation_injective K

example {d e r} (K : KrausChannel d e r) (X : Q d) :
    dilation K X * dilation K X = dilation K X ↔ X * X = X := dilation_idempotent_iff K X

-- Non-Hermitian matrices are included; reduction is not restricted to states.
example : partialTrace (dilation (identity_channel 2) (!![0, Complex.I; 0, 0] : Q 2)) =
    !![0, Complex.I; 0, 0] := by simp [partial_trace_stinespring_eq_channel]

example : dilation (identity_channel 2) (!![0, Complex.I; 0, 0] : Q 2) (0, 0) (1, 0) =
    Complex.I := identity_dilation_entry _ _ _

example {d} (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) (a b : Fin d) :
    dilation (unitary_channel U) X (a, 0) (b, 0) =
      ((U : Q d) * X * (U : Q d).conjTranspose) a b := unitary_dilation_entry U X a b

-- A 2-to-1 reset stores the original matrix entirely in its environment.
example (X : Q 2) : dilation Regression.rectangular_reset X (0, 0) (0, 1) = X 0 1 := by
  simp [dilation, stinespring_matrix, Regression.rectangular_reset, reset_channel,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single]

example (X : Q 2) : partialTrace (dilation Regression.rectangular_reset X) =
    X.trace • QuantumNoBroadcastingMixed.basisProjector (0 : Fin 1) :=
  Regression.rectangular_reset_output X

example : partialTrace (dilation Regression.rectangular_reset rhoPlus) = 1 := by
  rw [partial_trace_stinespring_eq_channel]
  change apply_channel (reset_channel (d := 2) (0 : Fin 1)) rhoPlus = _
  rw [reset_density _ rhoPlus_density]
  ext i j
  fin_cases i; fin_cases j; rfl

-- A 2-to-3 reset also fits the same construction.
example : (dilation (reset_channel (d := 2) (2 : Fin 3)) rhoPlus).trace = 1 := by
  rw [QuantumStinespringDilationContract.dilation_trace, rhoPlus_density.2]

example : partialTrace (dilation (reset_channel (d := 2) (2 : Fin 3)) rhoPlus) =
    QuantumNoBroadcastingMixed.basisProjector (2 : Fin 3) := by
  rw [partial_trace_stinespring_eq_channel, reset_density _ rhoPlus_density]

example : QuantumNoBroadcastingMixed.IsDensityMatrix (dilation (dephasing_channel 2) rhoPlus) :=
  dilation_density _ rhoPlus_density

example : dilation (dephasing_channel 2) rhoPlus (0, 0) (1, 1) = 1 / 2 :=
  Regression.dephasing_joint_coherence

example : partialTrace (dilation (dephasing_channel 2) rhoPlus) 0 1 = 0 :=
  Regression.dephasing_reduced_coherence

example : dilation (dephasing_channel 2) rhoPlus * dilation (dephasing_channel 2) rhoPlus =
    dilation (dephasing_channel 2) rhoPlus := by
  rw [dilation_idempotent_iff]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [rhoPlus, Matrix.mul_apply, Fin.sum_univ_two]

example : dilation (dephasing_channel 2) rhoPlus ≠
    dilation (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus :=
  Regression.dephasing_joint_distinct

example : partialTrace (dilation (dephasing_channel 2) rhoPlus) =
    partialTrace (dilation (dephasing_channel 2) QuantumCPTPChannelContract.Regression.rhoMinus) :=
  Regression.dephasing_reduced_equal

-- Mixed inputs do NOT become pure under an isometry.
example : let mixed : Q 2 := !![1/2, 0; 0, 1/2]
    dilation (dephasing_channel 2) mixed * dilation (dephasing_channel 2) mixed ≠
      dilation (dephasing_channel 2) mixed := by
  dsimp only
  rw [ne_eq, dilation_idempotent_iff]
  intro h
  have hh := congrArg (fun M : Q 2 => M 0 0) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hh

example {d e r} (K : KrausChannel d e r) (X : Q d) :
    partialTrace (dilation (append_zero K) X) = partialTrace (dilation K X) :=
  append_zero_reduction K X

example {d e r} (K : KrausChannel d e r) (a : Fin e) (b : Fin d) :
    stinespring_matrix (append_zero K).operators (a, Fin.last r) b = 0 := append_zero_block K a b

example (X : Q 2) : partialTrace (dilation (append_zero (append_zero (identity_channel 2))) X) = X := by
  simp [partial_trace_stinespring_eq_channel, append_zero_channel]

example : dilation (append_zero (dephasing_channel 2)) rhoPlus (0, 2) (1, 2) = 0 := by
  simp [dilation, Matrix.mul_apply, Matrix.conjTranspose_apply, stinespring_matrix,
    append_zero, Fin.snoc]

-- The non-isometric family [0] cannot be confused with a trace-preserving channel.
example : (stinespring_matrix (fun _ : Fin 1 => (0 : Q 1))).conjTranspose *
    stinespring_matrix (fun _ : Fin 1 => (0 : Q 1)) ≠ 1 := by
  rw [stinespring_isometry_general]
  simp

example : QuantumStinespringDilationContractSuite := verification_suite
