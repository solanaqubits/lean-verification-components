import Verification.QuantumNoCloningUnitary

open QuantumNoCloningUnitary
open scoped Kronecker

example : Unitary CNOT := cnot_unitary
example (M : Joint 2) : (CNOT*M*CNOT.conjTranspose).trace=M.trace := cnot_trace_preserving M
example : overlapSq zeroKet plusQubit=1/2 := bb84_zero_plus_overlap
example : overlapSq (basisKet (0 : Fin 2)) (basisKet (1 : Fin 2))=0 :=
  basis_overlap_orthogonal _ _ (by decide)
example : rho (-zeroKet)=rho zeroKet ∧ overlapSq zeroKet (-zeroKet)=1 :=
  minus_phase_regression _ (QuantumBB84ProtocolQBER.ket_normalized 0 0)
example (θ : ℝ) : rho (Complex.exp ((θ:ℂ)*Complex.I) • zeroKet)=rho zeroKet :=
  (phase_invariance_exp _ (QuantumBB84ProtocolQBER.ket_normalized 0 0) θ).1
example : VectorClones CNOT zeroKet zeroKet ∧ VectorClones CNOT zeroKet oneKet :=
  cnot_clones_computational_basis
example : CNOT*(plusQubit ⊗ₖ zeroKet)=bell ∧
    CNOT*(plusQubit ⊗ₖ zeroKet) ≠ plusQubit ⊗ₖ plusQubit := cnot_entangles_superposition
example (v w : Ket 2) : bell ≠ v ⊗ₖ w := bell_not_product v w
example {d : ℕ} (h : 2≤d) : ¬ ∃ (U : Joint d) (b : Ket d), Unitary U ∧ Normalized b ∧
    ∀ ψ, Normalized ψ → DensityClones U b ψ := no_universal_unitary_cloning h
example (U : Joint 2) (hU : Unitary U) (b : Ket 2) (hb : Normalized b) :
    ¬ ∀ basis bit, DensityClones U b (QuantumBB84ProtocolQBER.ket basis bit) :=
  bridge_to_bb84_unclonability U hU b hb
example (b ψ : Ket 3) (hb : Normalized b) (hψ : Normalized ψ) :
    ∃ U : Joint 3, Unitary U ∧ VectorClones U b ψ := single_state_cloner b ψ hb hψ
example (U : Joint 2) (hU : Unitary U) (b : Ket 2) (hb : Normalized b) :
    ¬ (VectorClones U b zeroKet ∧ VectorClones U b (-zeroKet)) :=
  opposite_vectors_not_both_cloned U hU b zeroKet hb (QuantumBB84ProtocolQBER.ket_normalized 0 0)
example : QuantumNoCloningUnitarySuite := quantum_no_cloning_unitary_master_suite
