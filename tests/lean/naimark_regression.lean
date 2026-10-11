import Verification.QuantumPOVMNaimarkDilation

open QuantumPOVMNaimarkDilation
open scoped ComplexOrder Kronecker

example (d k : ℕ) [NeZero k] (E : FinitePOVM d k) :
    ∃ U : Ext d k, U.conjTranspose*U=1 ∧ U*U.conjTranspose=1 ∧ U*J d k=V E ∧
      ∀ M : Q d, dilate E M=U*(M ⊗ₖ outcomeProjector (0 : Fin k))*U.conjTranspose :=
  unitary_dilation_extension E
example (d : ℕ) (E : FinitePOVM d 1) :
    Matrix.of (fun i j => V E (i,0) j) = (1:Q d) := singleton_isometry E
example : (binaryPOVM 2 (1/2) (by constructor <;> norm_num)).effects 0 *
    (binaryPOVM 2 (1/2) (by constructor <;> norm_num)).effects 0 ≠
    (binaryPOVM 2 (1/2) (by constructor <;> norm_num)).effects 0 :=
  binary_nonprojective (1/2) (by constructor <;> norm_num)
example (ρ : Q 2) (hρ : ρ.trace=1) :
    probability (binaryPOVM 2 (1/2) (by constructor <;> norm_num)) ρ 0=1/2 := by
  simpa using (binary_probability (1/2) (by constructor <;> norm_num) ρ hρ).1
example (ρ : Q 2) (hρ : ρ.PosSemidef ∧ ρ.trace=1) :
    (dilate (binaryPOVM 2 (1/2) (by constructor <;> norm_num)) ρ).PosSemidef ∧
    (dilate (binaryPOVM 2 (1/2) (by constructor <;> norm_num)) ρ).trace=1 :=
  density_matrix_dilation _ _ hρ
example : sqrt_effects (binaryPOVM 2 0 (by constructor <;> norm_num)) 0=0 := by
  apply (zero_effect _ 0 _).1
  simp [binaryPOVM]
example : sqrt_effects (binaryPOVM 2 0 (by constructor <;> norm_num)) 1=1 := by
  have h := projective_sqrt (binaryPOVM 2 0 (by constructor <;> norm_num)) 1
    (by simp [binaryPOVM])
  simpa [binaryPOVM] using h
example (m : Fin 3) (M : Q 4) :
    partialTrace (projector 4 m*dilate bellPOVM M*projector 4 m)=
      sqrt_effects bellPOVM m*M*sqrt_effects bellPOVM m := lueders_instrument_reduction _ _ _
example (p : ℝ) (hp : QuantumDepolarizingChannel.Physical p) (M : Q 2) (j : Fin 4) :
    probability (depolarizingPOVM p hp) M j=
      (QuantumDepolarizingChannel.K p j*M*(QuantumDepolarizingChannel.K p j).conjTranspose).trace :=
  bridge_to_depolarizing_channel p hp j M
example : qubitX*zeroDensity*qubitX.conjTranspose ≠ (1:Q 2)*zeroDensity*(1:Q 2).conjTranspose := by
  rw [counterexample_povm_not_instrument.2.2.1,counterexample_povm_not_instrument.2.2.2.1]
  exact counterexample_povm_not_instrument.2.2.2.2.symm
example : QuantumPOVMNaimarkDilationSuite := quantum_povm_naimark_dilation_master_suite
