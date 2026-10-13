import Verification.QuantumPOVMInformationallyComplete

noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMInformationallyComplete

example : QuantumPOVMInformationallyCompleteSuite := verification_suite
example (d : ℕ) : Module.finrank ℝ (HermMat d) = d ^ 2 := herm_finrank d
example {d k : ℕ} (E : POVM d k) : is_ic_povm E ↔ Function.Injective (measurement E) :=
  ic_povm_iff_injective E
example {d k : ℕ} (E : POVM d k) (h : is_ic_povm E) : d ^ 2 ≤ k :=
  ic_povm_outcome_bound E h
example (X : HermMat 1) : X = ∑ m, hs_inner X (effect scalarPOVM m) • dual_frame scalarPOVM scalar_ic m :=
  dual_frame_reconstruction_identity scalarPOVM scalar_ic X
example : is_ic_povm qubitTetrahedron := qubit_tetrahedron_ic_povm
example (m : Fin 4) : (tetraEffect m).PosSemidef := qubitTetrahedron.pos_semidef m
example : (∑ m : Fin 4, tetraEffect m) = 1 := qubitTetrahedron.completeness
example (i j : Fin 4) (h : i ≠ j) : Matrix.trace (tetraEffect i * tetraEffect j) = 1 / 12 := by
  rw [tetra_symmetric_overlap, if_neg h]
example : phasePlus * phasePlus = phasePlus := by
  rw [phasePlus, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    bloch_square 1 0 0 (by norm_num), smul_smul]
  norm_num
example : (⟨phasePlus, phase_pair_density.1.1.isHermitian⟩ : HermMat 2) =
    ∑ m, (Matrix.trace (phasePlus * tetraEffect m)).re • dual_frame qubitTetrahedron qubit_tetrahedron_ic_povm m :=
  (quantum_state_tomography qubitTetrahedron qubit_tetrahedron_ic_povm phasePlus phase_pair_density.1).2.2

private def mixed : Q 2 := (1 / 2 : ℂ) • (1 : Q 2)
private theorem mixed_density : QuantumNoBroadcastingMixed.IsDensityMatrix mixed := by
  refine ⟨Matrix.PosSemidef.one.smul (show (0 : ℂ) ≤ 1 / 2 by norm_num [Complex.nonneg_iff]), ?_⟩
  norm_num [mixed, Matrix.trace_smul, Matrix.trace_one]
example : (⟨mixed, mixed_density.1.isHermitian⟩ : HermMat 2) =
    ∑ m, (Matrix.trace (mixed * tetraEffect m)).re • dual_frame qubitTetrahedron qubit_tetrahedron_ic_povm m :=
  (quantum_state_tomography qubitTetrahedron qubit_tetrahedron_ic_povm mixed mixed_density).2.2
example (m : Fin 4) : (Matrix.trace (mixed * tetraEffect m)).re = 1 / 4 := by
  fin_cases m <;> norm_num [mixed, tetraEffect, blochEffect, Matrix.trace, Fin.sum_univ_succ] <;> ring
example : ¬ is_ic_povm (basisPOVM 2) := onb_measurement_not_ic (by norm_num) _
example : phasePlus ≠ phaseMinus := projective_phase_counterexample.1
example (m : Fin 2) : Matrix.trace (phasePlus * (basisPOVM 2).effects m) =
    Matrix.trace (phaseMinus * (basisPOVM 2).effects m) := projective_phase_counterexample.2 m
example : measurement qubitTetrahedron ⟨phasePlus, phase_pair_density.1.1.isHermitian⟩ ≠
    measurement qubitTetrahedron ⟨phaseMinus, phase_pair_density.2.1.isHermitian⟩ := by
  intro h
  exact projective_phase_counterexample.1 (congrArg val
    ((ic_povm_iff_injective _).mp qubit_tetrahedron_ic_povm h))
example : is_ic_povm (relabel qubitTetrahedron (Equiv.swap 0 3)) :=
  (relabel_ic _ _).mpr qubit_tetrahedron_ic_povm
example (X : HermMat 2) : frame_operator (relabel qubitTetrahedron (Equiv.swap 0 3)) X =
    frame_operator qubitTetrahedron X := relabel_frame _ _ _
example (m : Fin 4) :
    dual_frame (relabel qubitTetrahedron (Equiv.swap 0 3))
      ((relabel_ic _ _).mpr qubit_tetrahedron_ic_povm) m =
    dual_frame qubitTetrahedron qubit_tetrahedron_ic_povm ((Equiv.swap 0 3) m) :=
  relabel_dual _ _ _ _
