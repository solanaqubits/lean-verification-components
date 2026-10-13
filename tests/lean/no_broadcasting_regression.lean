/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoBroadcastingMixed

open QuantumNoBroadcastingMixed
open scoped ComplexOrder Kronecker

-- Constructive channels, correlated outputs, and the unconditional converse.
example (ρ σ : Q 1) : CanBroadcast ρ σ := dimension_one_broadcasting ρ σ

example : CanBroadcast
    (Matrix.diagonal (![1, 0] : Fin 2 → ℂ))
    (Matrix.diagonal (![0, 1] : Fin 2 → ℂ)) := diagonal_pair_broadcasting _ _

example : CanBroadcast
    (Matrix.diagonal (![(1/3 : ℂ), 2/3] : Fin 2 → ℂ))
    (Matrix.diagonal (![(3/4 : ℂ), 1/4] : Fin 2 → ℂ)) := diagonal_pair_broadcasting _ _

example (ρ : Q 2) (hρ : IsDensityMatrix ρ) : CanBroadcast ρ ρ :=
  quantum_identical_states_broadcasting ρ hρ

example (ρ σ : Q 3) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (hc : ρ * σ = σ * ρ) : CanBroadcast ρ σ :=
  quantum_broadcasting_constructive_sufficiency ρ σ hρ hσ hc

-- A basis with complex phase; the complete positivity proof still handles arbitrary ancillas.
example (U : Matrix.unitaryGroup (Fin 2) ℂ) :
    CanBroadcast (conjugate U (Matrix.diagonal (![1, 0] : Fin 2 → ℂ)))
      (conjugate U (Matrix.diagonal (![(1/2 : ℂ), 1/2] : Fin 2 → ℂ))) :=
  jointly_diagonalized_broadcasting U _ _

example : let ρ : Q 2 := Matrix.diagonal (fun _ => (1/2 : ℂ))
    Broadcasts (diagonalChannel 2) ρ ∧ (diagonalChannel 2).toLinearMap ρ ≠ ρ ⊗ₖ ρ :=
  correlated_mixed_output

example (ψ φ : QuantumNoCloningUnitary.Ket 2) :
    CanBroadcast (QuantumNoCloningUnitary.rho ((-1 : ℂ) • ψ)) (QuantumNoCloningUnitary.rho φ) ↔
      CanBroadcast (QuantumNoCloningUnitary.rho ψ) (QuantumNoCloningUnitary.rho φ) :=
  phase_broadcasting_invariance ψ φ (-1) (by norm_num)

example : let P := QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.zeroKet
    let Q := QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.plusQubit
    P * Q ≠ Q * P := zero_plus_projectors_noncommuting

example (E : CPTPMap 2) (ρ : Q 2) (hρ : IsDensityMatrix ρ) :
    IsDensityMatrix (E.toLinearMap ρ) := E.density_preserved ρ hρ

example (E : CPTPMap 2) (a : ℕ) (X : Mat (Fin a × Fin 2)) (hX : X.PosSemidef) :
    (amplify E.toLinearMap a X).PosSemidef := E.completely_positive a X hX

-- No positive-definiteness or simple-spectrum assumptions appear in necessity.
example {d : ℕ} (ρ σ : Q d) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ)
    (E : CPTPMap d) (h₁ : Broadcasts E ρ) (h₂ : Broadcasts E σ) : ρ * σ = σ * ρ :=
  quantum_broadcasting_necessity ρ σ hρ hσ ⟨E, h₁, h₂⟩

example {d : ℕ} (ρ σ : Q d) (hρ : IsDensityMatrix ρ) (hσ : IsDensityMatrix σ) :
    CanBroadcast ρ σ ↔ ρ * σ = σ * ρ := quantum_no_broadcasting_theorem ρ σ hρ hσ

-- A nonzero common kernel and a repeated eigenvalue of ρ + σ.
example : let ρ : Q 3 := Matrix.diagonal (![1, 0, 0] : Fin 3 → ℂ)
    let σ : Q 3 := Matrix.diagonal (![0, 1, 0] : Fin 3 → ℂ)
    ∃ A : Q 3, A.IsHermitian ∧ A * (ρ + σ) + (ρ + σ) * A = (2 : ℂ) • ρ := by
  apply exists_symmetric_logarithmic_derivative
  all_goals
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num

example : ¬ CanBroadcast
    (QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.zeroKet)
    (QuantumNoCloningUnitary.rho QuantumNoCloningUnitary.plusQubit) :=
  zero_plus_not_broadcastable

example (ψ φ : QuantumNoCloningUnitary.Ket 3)
    (hψ : QuantumNoCloningUnitary.Normalized ψ) (hφ : QuantumNoCloningUnitary.Normalized φ) :
    CanBroadcast (QuantumNoCloningUnitary.rho ψ) (QuantumNoCloningUnitary.rho φ) ↔
      ψ.conjTranspose * φ = 0 ∨ ∃ z : ℂ, Complex.normSq z = 1 ∧ ψ = z • φ :=
  quantum_pure_state_phase_criterion ψ φ hψ hφ

example (E : CPTPMap 2) : ∃ K : (Fin 2 × (Fin 2 × Fin 2)) →
    Matrix (Fin 2 × Fin 2) (Fin 2) ℂ, E.toLinearMap = krausMap K := E.exists_kraus

example (U : Matrix.unitaryGroup (Fin 2 × Fin 2) ℂ)
    (b ψ φ : QuantumNoCloningUnitary.Ket 2)
    (hb : QuantumNoCloningUnitary.Normalized b)
    (hψ : QuantumNoCloningUnitary.Normalized ψ) (hφ : QuantumNoCloningUnitary.Normalized φ)
    (hcψ : QuantumNoCloningUnitary.DensityClones (U : Joint 2) b ψ)
    (hcφ : QuantumNoCloningUnitary.DensityClones (U : Joint 2) b φ) :
    ψ.conjTranspose * φ = 0 ∨ QuantumNoCloningUnitary.rho ψ = QuantumNoCloningUnitary.rho φ :=
  bridge_to_quantum_no_cloning U b ψ φ hb hψ hφ hcψ hcφ

example : QuantumNoBroadcastingMixedSuite := verification_suite
