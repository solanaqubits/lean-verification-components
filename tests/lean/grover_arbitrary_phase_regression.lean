import Verification.QuantumGroverArbitraryPhase

open QuantumGroverArbitraryPhase
open scoped ComplexConjugate

-- Arbitrary complex input and unequal phases: no normalization or matching assumption.
example (v : State) (ω : Fin 4) (φ ψ : ℝ) :
    normSquared (arbitraryGroverStep ω φ ψ v) = normSquared v :=
  arbitrary_grover_norm_preservation ω φ ψ v

example (ω : Fin 4) (φ ψ : ℝ) (u v : State) :
    hermitian u (arbitraryGroverStep ω φ ψ v) = hermitian (adjointStep ω φ ψ u) v :=
  arbitrary_grover_adjoint ω φ ψ u v

example (v : State) : adjointStep 2 (Real.pi/2) 0 (arbitraryGroverStep 2 (Real.pi/2) 0 v) = v :=
  (arbitrary_grover_unitary 2 (Real.pi/2) 0 v).1

example (v : State) : arbitraryGroverStep 3 0 (Real.pi/2) (adjointStep 3 0 (Real.pi/2) v) = v :=
  (arbitrary_grover_unitary 3 0 (Real.pi/2) v).2

example (a b : ℂ) : InPlane 1 (arbitraryGroverStep 1 0 Real.pi (twoLevel 1 a b)) :=
  arbitrary_grover_plane_invariant 1 0 Real.pi _ ⟨a,b,rfl⟩

example (a b c d : ℂ) (h : planeState 2 a b = planeState 2 c d) : a=c ∧ b=d :=
  plane_coordinates_unique 2 a b c d h

example (ω : Fin 4) (φ ψ : ℝ) (k : ℕ) :
    normSquared (stateAt ω φ ψ k) = 1 ∧ InPlane ω (stateAt ω φ ψ k) :=
  ⟨stateAt_normalized ω φ ψ k, stateAt_in_plane ω φ ψ k⟩

example (ω : Fin 4) : successWeight ω (arbitraryGroverStep ω 0 0 uniform) = 1/4 := by
  rw [arbitrary_grover_success_formula]; norm_num

example (ω : Fin 4) :
    successWeight ω (arbitraryGroverStep ω (Real.pi/2) (Real.pi/2) uniform) = 13/16 := by
  rw [arbitrary_grover_success_formula, Real.cos_pi_div_two]; norm_num

example (ω : Fin 4) : successWeight ω (arbitraryGroverStep ω Real.pi Real.pi uniform) = 1 :=
  (arbitrary_grover_zero_overshoot_exact ω).1

example (ω : Fin 4) (φ : ℝ) (h : Real.cos φ ≠ -1) :
    successWeight ω (arbitraryGroverStep ω φ φ uniform) ≠ 1 := by
  intro he; exact h ((arbitrary_grover_success_iff ω φ).mp he)

example (t : QuantumGroverSearch.TargetItem) (v : QuantumGroverSearch.QState4) :
    arbitraryGroverStep (QuantumGroverMultipleTargets.itemIndex t) Real.pi Real.pi (embedLegacy v) =
      -embedLegacy (QuantumGroverSearch.groverStep (QuantumGroverSearch.targetToBasis t) v) :=
  arbitrary_grover_reduction_to_legacy t v

example (ω : Fin 4) (v : Fin 4 → ℝ) (i : Fin 4) :
    Complex.normSq (arbitraryGroverStep ω Real.pi Real.pi (embed v) i) =
      (QuantumGroverMultipleTargets.groverStep {ω} v i)^2 :=
  canonical_measurement_weights ω v i

-- The sign and equal-phase restrictions must not accidentally reappear as false claims.
example (ω : Fin 4) : arbitraryGroverStep ω Real.pi Real.pi uniform ≠ marked ω :=
  canonical_sign_not_literal ω

example (ω : Fin 4) : (0 : ℝ) ≠ Real.pi ∧ ∀ v, InPlane ω v →
    InPlane ω (arbitraryGroverStep ω 0 Real.pi v) := unequal_phases_still_invariant ω

-- Outside the symmetric plane, unitarity still holds; the plane is not all of C^4.
example : ¬ InPlane 0 ![0,1,-1,0] := by
  rintro ⟨a,b,h⟩
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  norm_num [twoLevel, Matrix.cons_val_one, Matrix.cons_val_two, Fin.ext_iff] at h1 h2
  rw [← h1] at h2
  norm_num at h2

example : QuantumGroverArbitraryPhaseSuite := quantum_grover_arbitrary_phase_master_suite
