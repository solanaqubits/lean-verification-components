import Verification.HopfObstruction
import Verification.HopfAlmostComplex

set_option linter.style.header false

namespace HopfIntegrabilityBarrier

open HopfObstruction HopfAlmostComplex

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Algebraic vanishing predicate; no equivalence with geometric integrability is proved here. -/
def IsIntegrable (ac : AlmostComplex V) (lb : LieBracket V) : Prop :=
  ∀ X Y : V, nijenhuis ac lb X Y = 0

/-- Existence of a nonzero value of the algebraic Nijenhuis expression. -/
def HasNijenhuisObstruction (ac : AlmostComplex V) (lb : LieBracket V) : Prop :=
  ∃ X Y : V, nijenhuis ac lb X Y ≠ 0

/-- A nonzero witness contradicts the vanishing predicate.
The supplied name is retained; the implication runs from obstruction to nonintegrability.
-/
theorem obstruction_of_not_integrable (ac : AlmostComplex V) (lb : LieBracket V)
    (h : HasNijenhuisObstruction ac lb) : ¬ IsIntegrable ac lb := by
  intro h_int
  rcases h with ⟨X, Y, h_ne⟩
  exact h_ne (h_int X Y)

/-- Positive scaling of the scalar energy model; no tensor-dependent scale is defined. -/
noncomputable def scaledSingularEnergy (C : ℝ) (ε : ℝ) : ℝ :=
  C * singularEnergy ε

/-- Positivity of the scaled scalar energy for the stated input range. -/
theorem scaled_energy_pos (C : ℝ) (ε : ℝ) (hC : 0 < C) (h_pos : 0 < ε) (h_lt1 : ε < 1) :
    0 < scaledSingularEnergy C ε := by
  exact mul_pos hC (singular_energy_pos ε h_pos h_lt1)

/-- Every positive threshold is exceeded somewhere in the cutoff interval. -/
theorem scaled_energy_divergence (C : ℝ) (hC : 0 < C) (K : ℝ) (hK : 0 < K) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ K < scaledSingularEnergy C ε := by
  rcases hopf_singular_obstruction_divergence (K / C) (div_pos hK hC) with
    ⟨ε, h_pos, h_lt1, h_div⟩
  refine ⟨ε, h_pos, h_lt1, ?_⟩
  have h_cancel : (K / C) * C = K := div_mul_cancel₀ K (ne_of_gt hC)
  dsimp [scaledSingularEnergy]
  nlinarith

/-- Selected algebraic identities and scalar unboundedness, parameterized by a real module.
No geometric nonexistence assertion or link between a bracket and the energy scale is included.
-/
structure HopfFormalSuite (V : Type*) [AddCommGroup V] [Module ℝ V] : Prop where
  h_no_real_eig : ∀ (ac : AlmostComplex V) (lam : ℝ) (v : V), v ≠ 0 → ac.J v ≠ lam • v
  h_skew : ∀ (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V),
    nijenhuis ac lb Y X = - nijenhuis ac lb X Y
  h_J_left : ∀ (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V),
    nijenhuis ac lb (ac.J X) Y = - ac.J (nijenhuis ac lb X Y)
  h_J_both : ∀ (ac : AlmostComplex V) (lb : LieBracket V) (X Y : V),
    nijenhuis ac lb (ac.J X) (ac.J Y) = - nijenhuis ac lb X Y
  h_obstruction : ∀ (ac : AlmostComplex V) (lb : LieBracket V),
    HasNijenhuisObstruction ac lb → ¬ IsIntegrable ac lb
  h_divergence : ∀ (C : ℝ), 0 < C → ∀ (K : ℝ), 0 < K →
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ K < scaledSingularEnergy C ε

/-- Assemble the stated algebraic and scalar guarantees for any real module. -/
theorem hopf_master_verification_suite : HopfFormalSuite V := {
  h_no_real_eig := no_real_eigenvalues
  h_skew := nijenhuis_skew
  h_J_left := nijenhuis_J_left
  h_J_both := nijenhuis_J_both
  h_obstruction := obstruction_of_not_integrable
  h_divergence := scaled_energy_divergence
}

#print axioms obstruction_of_not_integrable
#print axioms scaled_energy_divergence
#print axioms hopf_master_verification_suite

end HopfIntegrabilityBarrier
