import Verification.PhotonicsCPhaseGateUnitary
open PhotonicsCPhaseGateUnitary
open scoped BigOperators

example : PhotonicsCPhaseGateUnitarySuite := photonics_cphase_gate_master_suite
example : J.conjTranspose * J = 1 := encoding_isometry
example : ∀ k, AcceptedOccupation k ↔ ∃ i, k = compOccupation i := acceptance_exact
example (T : ℝ) (h : 0 ≤ T) (h' : T ≤ 1) :
    (U_two_photon_six T).conjTranspose * U_two_photon_six T = 1 := two_photon_six_unitary T h h'
example (A : ModeMatrix) (l : FockBasis) (x : SixModes → ℂ) :
    ∑ k, monomial k x * symmetricLift A k l = monomial l (A.transpose.mulVec x) :=
  symmetric_lift_substitution A l x
example : K (1/3) = (1/3:ℂ) • CZ := ralph_cphase_exact
example (ψ : CompBasis → ℂ) (h : normSquared ψ = 1) :
    normSquared ((K (1/3)).mulVec ψ) = 1/9 := cphase_success_prob_invariant ψ h
example : (K (1/3)).mulVec (basis 3) = (-1/3:ℂ) • basis 3 := by
  simpa using (reg_basis_states 3).1
example : normSquared ((K (1/3)).mulVec graphState) = 1/9 :=
  cphase_success_prob_invariant graphState graph_state_normalized
example : (K (1/2)).mulVec (basis 3) = 0 := reg_t_half_no_cz.2
example : K 1 = 1 := reg_t_one_identity
example : K 0 = Matrix.diagonal ![(0:ℂ),0,0,-1] := by
  simpa using postselected_kraus_exact 0 (by norm_num) (by norm_num)
example : K (1/4) = Matrix.diagonal ![(1/4:ℂ),1/4,1/4,-(1/2)] := by
  have h := postselected_kraus_exact (1/4) (by norm_num) (by norm_num)
  norm_num at h
  exact h
example (ρ : CompMatrix) (h : Matrix.trace ρ = 1) :
    Matrix.trace (K (1/3) * ρ * (K (1/3)).conjTranspose) = 1/9 := density_success_trace ρ h
example : ¬ PureSeparable graphState := graph_not_separable
example : PureSeparable plusPlus := plus_plus_separable
example : (tensor 1 Hadamard).mulVec graphState = bellState := graph_bell_local_equivalence
example : reducedA (pureDensity graphState) = (1/2:ℂ) • (1:QubitMatrix) := graph_reduced_states.1
example (u v : Fin 2 → ℂ) (hu : qubitNormSquared u = 1) (hv : qubitNormSquared v = 1) :
    Matrix.trace (reducedA (pureDensity (tensorState u v)) *
      reducedA (pureDensity (tensorState u v))) = 1 := product_reduced_purity u v hu hv
