/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PhotonicsBeamSplitterPhaseShift
import Verification.PhotonicsHongOuMandelInterference
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! A lossless six-mode network and its normalized two-boson lift. The logical
operation is a coincidence-postselected contraction, not a deterministic gate. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace PhotonicsCPhaseGateUnitary
abbrev CompBasis := Fin 4
abbrev SixModes := Fin 6
abbrev FockBasis := Fin 21
abbrev CompMatrix := Matrix CompBasis CompBasis ℂ
abbrev ModeMatrix := Matrix SixModes SixModes ℂ
abbrev FockMatrix := Matrix FockBasis FockBasis ℂ

/-- Lexicographic unordered mode pairs, including double occupancy. -/
def occupation : FockBasis → SixModes × SixModes :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (2,
    2), (2, 3), (2, 4), (2, 5), (3, 3), (3, 4), (3, 5), (4, 4), (4, 5), (5, 5)]

theorem fock_sector_dimension : Nat.choose (6 + 2 - 1) 2 = 21 := by decide

theorem occupation_bijection : Function.Injective occupation ∧
    ∀ i j : SixModes, i ≤ j → ∃ k, occupation k = (i,j) := by decide

/-- Normalized creation monomial: x_i²/√2 for double occupancy, x_i x_j otherwise. -/
def monomial (k : FockBasis) (x : SixModes → ℂ) : ℂ :=
  let p := occupation k
  x p.1 * x p.2 / (if p.1 = p.2 then (Real.sqrt 2 : ℂ) else 1)

/-- Coefficients obtained by multiplying the two transformed creation operators. -/
def symmetricLift (A : ModeMatrix) : FockMatrix := fun k l =>
  let o := occupation k
  let i := occupation l
  if i.1 = i.2 then
    if o.1 = o.2 then A o.1 i.1 ^ 2
    else (Real.sqrt 2 : ℂ) * A o.1 i.1 * A o.2 i.1
  else if o.1 = o.2 then (Real.sqrt 2 : ℂ) * A o.1 i.1 * A o.1 i.2
  else A o.1 i.1 * A o.2 i.2 + A o.1 i.2 * A o.2 i.1

private theorem sqrt_two_sq : (Real.sqrt 2 : ℂ)^2 = 2 := by
  norm_cast
  exact Real.sq_sqrt (by norm_num)
private theorem sqrt_two_ne : (Real.sqrt 2 : ℂ) ≠ 0 := by
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0:ℝ) < 2)))

private theorem sqrt_two_inv : (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ) / 2 := by
  apply inv_eq_of_mul_eq_one_right
  calc
    (Real.sqrt 2 : ℂ) * ((Real.sqrt 2 : ℂ) / 2) = (Real.sqrt 2 : ℂ)^2 / 2 := by ring
    _ = 1 := by rw [sqrt_two_sq]; norm_num

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
/-- The lift is derived from normalized bosonic polynomial substitution. -/
theorem symmetric_lift_substitution (A : ModeMatrix) (l : FockBasis) (x : SixModes → ℂ) :
    ∑ k, monomial k x * symmetricLift A k l =
      monomial l (A.transpose.mulVec x) := by
  fin_cases l <;>
    simp [monomial, symmetricLift, occupation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.transpose_apply] <;>
    simp only [div_eq_mul_inv, sqrt_two_inv] <;> ring_nf <;> simp only [sqrt_two_sq] <;> ring

/-- Pairs (a₀,v_a), (a₁,b₁), (b₀,v_b), all with the imported splitter. -/
def modePartner : SixModes → SixModes := ![4, 3, 5, 1, 0, 2]
def network (T : ℝ) : ModeMatrix := fun i j =>
  if i = j then PhotonicsBeamSplitterPhaseShift.splitter T 0 0
  else if modePartner i = j then PhotonicsBeamSplitterPhaseShift.splitter T 0 1 else 0

def U_two_photon_six (T : ℝ) : FockMatrix := symmetricLift (network T)

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
theorem network_unitary (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (network T).conjTranspose * network T = 1 := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply,
      network, modePartner, PhotonicsBeamSplitterPhaseShift.splitter] <;>
    ring_nf <;> simp [ht, hr, Complex.I_sq]

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_0 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 0 j = (1:FockMatrix) 0 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_1 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 1 j = (1:FockMatrix) 1 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_2 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 2 j = (1:FockMatrix) 2 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_3 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 3 j = (1:FockMatrix) 3 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_4 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 4 j = (1:FockMatrix) 4 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_5 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 5 j = (1:FockMatrix) 5 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_6 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 6 j = (1:FockMatrix) 6 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_7 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 7 j = (1:FockMatrix) 7 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_8 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 8 j = (1:FockMatrix) 8 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_9 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 9 j = (1:FockMatrix) 9 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_10 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 10 j = (1:FockMatrix) 10 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_11 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 11 j = (1:FockMatrix) 11 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_12 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 12 j = (1:FockMatrix) 12 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_13 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 13 j = (1:FockMatrix) 13 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_14 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 14 j = (1:FockMatrix) 14 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_15 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 15 j = (1:FockMatrix) 15 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_16 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 16 j = (1:FockMatrix) 16 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_17 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 17 j = (1:FockMatrix) 17 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_18 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 18 j = (1:FockMatrix) 18 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_19 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 19 j = (1:FockMatrix) 19 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, Complex.I_sq]
  all_goals ring

set_option maxHeartbeats 0 in
-- Explicit finite matrix expansion and polynomial normalization exceed the default tactic budget.
private theorem unitary_row_20 (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) (j : FockBasis) :
    ((U_two_photon_six T).conjTranspose * U_two_photon_six T) 20 j = (1:FockMatrix) 20 j := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  have ht4 : (Real.sqrt T : ℂ)^4 = (T:ℂ)^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, ht]
  have hr4 : (Real.sqrt (1-T) : ℂ)^4 = (1-(T:ℂ))^2 := by rw [show (4:ℕ)=2*2 by decide, pow_mul, hr]
  fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.conjTranspose_apply, Matrix.one_apply,
      U_two_photon_six, symmetricLift, occupation, network, modePartner,
      PhotonicsBeamSplitterPhaseShift.splitter]
  all_goals ring_nf
  all_goals simp [ht, hr, ht4, hr4, sqrt_two_sq, Complex.I_sq]
  all_goals ring

theorem two_photon_six_unitary (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    (U_two_photon_six T).conjTranspose * U_two_photon_six T = 1 := by
  ext i j : 2
  fin_cases i
  · exact unitary_row_0 T hT hT1 j
  · exact unitary_row_1 T hT hT1 j
  · exact unitary_row_2 T hT hT1 j
  · exact unitary_row_3 T hT hT1 j
  · exact unitary_row_4 T hT hT1 j
  · exact unitary_row_5 T hT hT1 j
  · exact unitary_row_6 T hT hT1 j
  · exact unitary_row_7 T hT hT1 j
  · exact unitary_row_8 T hT hT1 j
  · exact unitary_row_9 T hT hT1 j
  · exact unitary_row_10 T hT hT1 j
  · exact unitary_row_11 T hT hT1 j
  · exact unitary_row_12 T hT hT1 j
  · exact unitary_row_13 T hT hT1 j
  · exact unitary_row_14 T hT hT1 j
  · exact unitary_row_15 T hT hT1 j
  · exact unitary_row_16 T hT hT1 j
  · exact unitary_row_17 T hT hT1 j
  · exact unitary_row_18 T hT hT1 j
  · exact unitary_row_19 T hT hT1 j
  · exact unitary_row_20 T hT hT1 j

/-- |00>, |01>, |10>, |11> occupy (a₀,b₀), (a₀,b₁), (a₁,b₀), (a₁,b₁). -/
def compOccupation : CompBasis → FockBasis := ![2, 3, 7, 8]
def J : Matrix FockBasis CompBasis ℂ := fun k i => if k = compOccupation i then 1 else 0

theorem compression_entries (A : FockMatrix) (i j : CompBasis) :
    (J.conjTranspose * A * J) i j = A (compOccupation i) (compOccupation j) := by
  simp [Matrix.mul_apply, J, Matrix.conjTranspose_apply]

theorem encoding_isometry : J.conjTranspose * J = 1 := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, J, compOccupation, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ]

/-- The orthogonal projector onto the accepted dual-rail sector. -/
def successProjector : FockMatrix := J * J.conjTranspose

theorem success_projector_orthogonal : successProjector.conjTranspose = successProjector ∧
    successProjector * successProjector = successProjector := by
  constructor
  · simp [successProjector]
  · simp only [successProjector, Matrix.mul_assoc, ← Matrix.mul_assoc J.conjTranspose J,
      encoding_isometry, Matrix.one_mul]

def K (T : ℝ) : CompMatrix := J.conjTranspose * U_two_photon_six T * J

/-- This diagonal is a conclusion of mode scattering followed by postselection. -/
theorem postselected_kraus_exact (T : ℝ) (hT : 0 ≤ T) (hT1 : T ≤ 1) :
    K T = Matrix.diagonal ![(T:ℂ), T, T, 2*T-1] := by
  have ht : (Real.sqrt T : ℂ)^2 = T := by exact_mod_cast Real.sq_sqrt hT
  have hr : (Real.sqrt (1-T) : ℂ)^2 = 1-(T:ℂ) := by
    exact_mod_cast Real.sq_sqrt (by linarith : 0 ≤ 1-T)
  ext i j : 2
  change (J.conjTranspose * U_two_photon_six T * J) i j = _
  rw [compression_entries]
  fin_cases i <;> fin_cases j <;>
    simp [U_two_photon_six, symmetricLift, network, occupation, compOccupation,
      modePartner, PhotonicsBeamSplitterPhaseShift.splitter, Matrix.diagonal] <;>
    ring_nf <;> simp [ht, hr, Complex.I_sq]
  ring

def CZ : CompMatrix := Matrix.diagonal ![1, 1, 1, -1]

theorem ralph_cphase_exact : K (1/3) = (1/3 : ℂ) • CZ := by
  rw [postselected_kraus_exact (1/3) (by norm_num) (by norm_num)]
  ext i j : 2
  fin_cases i <;> fin_cases j <;> norm_num [CZ, Matrix.diagonal]

theorem cz_unitary_hermitian_involutive :
    CZ.conjTranspose * CZ = 1 ∧ CZ.conjTranspose = CZ ∧ CZ * CZ = 1 := by
  repeat' constructor
  all_goals ext i j : 2
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [CZ, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal,
      Fin.sum_univ_succ]

theorem success_effect : (K (1/3)).conjTranspose * K (1/3) = (1/9 : ℂ) • (1 : CompMatrix) := by
  rw [ralph_cphase_exact]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    cz_unitary_hermitian_involutive.1, smul_smul]
  norm_num

def normSquared (ψ : CompBasis → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)

theorem cphase_success_prob (ψ : CompBasis → ℂ) :
    normSquared ((K (1/3)).mulVec ψ) = (1/9) * normSquared ψ := by
  rw [ralph_cphase_exact]
  simp [normSquared, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, CZ, Matrix.diagonal,
    Complex.normSq_mul, Complex.normSq_neg]
  ring

theorem cphase_success_prob_invariant (ψ : CompBasis → ℂ) (hψ : normSquared ψ = 1) :
    normSquared ((K (1/3)).mulVec ψ) = 1/9 := by
  rw [cphase_success_prob, hψ, mul_one]

/-- Algebraic identity holds for all matrices, in particular density matrices. -/
theorem density_matrix_evolution (ρ : CompMatrix) :
    K (1/3) * ρ * (K (1/3)).conjTranspose =
      (1/9 : ℂ) • (CZ * ρ * CZ.conjTranspose) := by
  rw [ralph_cphase_exact]
  simp only [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

theorem normalized_success_action (ψ : CompBasis → ℂ) :
    (3 : ℂ) • (K (1/3)).mulVec ψ = CZ.mulVec ψ := by
  rw [ralph_cphase_exact, Matrix.smul_mulVec, smul_smul]
  norm_num

abbrev QubitMatrix := Matrix (Fin 2) (Fin 2) ℂ
def bitA : CompBasis → Fin 2 := ![0,0,1,1]
def bitB : CompBasis → Fin 2 := ![0,1,0,1]
def bitsIndex : Fin 2 → Fin 2 → CompBasis := ![![0,1],![2,3]]

theorem bit_index_inverse : (∀ a b, bitA (bitsIndex a b) = a ∧ bitB (bitsIndex a b) = b) ∧
    (∀ i, bitsIndex (bitA i) (bitB i) = i) := by decide

/-- Kronecker product with the explicitly fixed 00,01,10,11 ordering. -/
def tensor (A B : QubitMatrix) : CompMatrix :=
  fun i j => A (bitA i) (bitA j) * B (bitB i) (bitB j)
def tensorState (u v : Fin 2 → ℂ) : CompBasis → ℂ := fun i => u (bitA i) * v (bitB i)
def PauliX : QubitMatrix := ![![0,1],![1,0]]
def PauliZ : QubitMatrix := ![![1,0],![0,-1]]

theorem cz_pauli_conjugation :
    CZ * tensor PauliX 1 * CZ = tensor PauliX PauliZ ∧
    CZ * tensor 1 PauliX * CZ = tensor PauliZ PauliX ∧
    CZ * tensor PauliZ 1 * CZ = tensor PauliZ 1 ∧
    CZ * tensor 1 PauliZ * CZ = tensor 1 PauliZ := by
  repeat' constructor
  all_goals ext i j : 2
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [CZ, tensor, bitA, bitB, PauliX, PauliZ, Matrix.mul_apply,
      Matrix.diagonal, Matrix.one_apply, Fin.sum_univ_succ]

def plusPlus : CompBasis → ℂ := ![1/2,1/2,1/2,1/2]
def graphState : CompBasis → ℂ := ![1/2,1/2,1/2,-1/2]
def pureDensity (ψ : CompBasis → ℂ) : CompMatrix := fun i j => ψ i * star (ψ j)
def reducedA (ρ : CompMatrix) : QubitMatrix := fun a a' => ∑ b, ρ (bitsIndex a b) (bitsIndex a' b)
def reducedB (ρ : CompMatrix) : QubitMatrix := fun b b' => ∑ a, ρ (bitsIndex a b) (bitsIndex a b')

theorem cz_plus_plus : CZ.mulVec plusPlus = graphState := by
  ext i
  fin_cases i <;> norm_num [CZ, plusPlus, graphState, Matrix.mulVec, dotProduct,
    Matrix.diagonal, Matrix.one_apply, Fin.sum_univ_succ]

theorem graph_state_normalized : normSquared graphState = 1 := by
  norm_num [normSquared, graphState, Fin.sum_univ_succ]

theorem graph_reduced_states :
    reducedA (pureDensity graphState) = (1/2 : ℂ) • (1 : QubitMatrix) ∧
    reducedB (pureDensity graphState) = (1/2 : ℂ) • (1 : QubitMatrix) := by
  constructor <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    norm_num [reducedA, reducedB, pureDensity, graphState, bitsIndex, Matrix.cons_val_two,
      Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Complex.conj_ofNat, Fin.sum_univ_succ,
      Matrix.one_apply]

theorem graph_global_purity :
    pureDensity graphState * pureDensity graphState = pureDensity graphState ∧
    Matrix.trace (pureDensity graphState) = 1 := by
  constructor
  · ext i j : 2
    fin_cases i <;> fin_cases j <;>
      norm_num [pureDensity, graphState, Complex.conj_ofNat, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [Matrix.trace, pureDensity, graphState, Complex.conj_ofNat, Fin.sum_univ_succ]

/-- Hermitian squared norm of a local state. -/
def qubitNormSquared (u : Fin 2 → ℂ) : ℂ := ∑ i, u i * star (u i)

/-- Purity criterion for normalized pure product states, proved from the partial trace. -/
theorem product_reduced_purity (u v : Fin 2 → ℂ)
    (hu : qubitNormSquared u = 1) (hv : qubitNormSquared v = 1) :
    Matrix.trace (reducedA (pureDensity (tensorState u v)) *
      reducedA (pureDensity (tensorState u v))) = 1 := by
  have formula : Matrix.trace (reducedA (pureDensity (tensorState u v)) *
      reducedA (pureDensity (tensorState u v))) = qubitNormSquared u ^ 2 * qubitNormSquared v ^ 2
        := by
    simp [Matrix.trace, Matrix.mul_apply, reducedA, pureDensity, tensorState,
      qubitNormSquared, bitsIndex, bitA, bitB, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.tail_cons, Fin.sum_univ_succ]
    ring
  rw [formula, hu, hv]
  norm_num

theorem graph_reduced_purity :
    Matrix.trace (reducedA (pureDensity graphState) * reducedA (pureDensity graphState)) = (1/2:ℂ) ∧
    (1/2:ℝ) < 1 := by
  rw [graph_reduced_states.1]
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Pure-state separability: a tensor product of two local vectors. -/
def PureSeparable (ψ : CompBasis → ℂ) : Prop := ∃ u v, ψ = tensorState u v

theorem separable_determinant_zero (ψ : CompBasis → ℂ) (h : PureSeparable ψ) :
    ψ 0 * ψ 3 - ψ 1 * ψ 2 = 0 := by
  obtain ⟨u,v,rfl⟩ := h
  simp [tensorState, bitA, bitB]
  ring

theorem graph_not_separable : ¬ PureSeparable graphState := by
  intro h
  have hd := separable_determinant_zero graphState h
  norm_num [graphState, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons] at hd

def Hadamard : QubitMatrix := fun i j =>
  (1 / (Real.sqrt 2 : ℂ)) * (if i = 1 ∧ j = 1 then -1 else 1)
def bellState : CompBasis → ℂ := ![1/(Real.sqrt 2 : ℂ),0,0,1/(Real.sqrt 2 : ℂ)]

theorem graph_bell_local_equivalence : (tensor 1 Hadamard).mulVec graphState = bellState := by
  ext i
  fin_cases i <;>
    simp [tensor, Hadamard, graphState, bellState, bitA, bitB, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.one_apply] <;> ring

theorem hadamard_unitary : Hadamard.conjTranspose * Hadamard = 1 := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [Hadamard, Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_succ] <;>
    field_simp <;> ring_nf <;> simp [sqrt_two_sq]

theorem plus_plus_separable : PureSeparable plusPlus := by
  refine ⟨![1,1], ![1/2,1/2], ?_⟩
  ext i
  fin_cases i <;> norm_num [plusPlus, tensorState, bitA, bitB]

theorem cz_graph_state_entanglement :
    CZ.mulVec plusPlus = graphState ∧ normSquared graphState = 1 ∧
    reducedA (pureDensity graphState) = (1/2:ℂ) • (1:QubitMatrix) ∧
    reducedB (pureDensity graphState) = (1/2:ℂ) • (1:QubitMatrix) ∧
    Matrix.trace (reducedA (pureDensity graphState) * reducedA (pureDensity graphState)) = (1/2:ℂ) ∧
    ¬ PureSeparable graphState :=
  ⟨cz_plus_plus, graph_state_normalized, graph_reduced_states.1, graph_reduced_states.2,
    graph_reduced_purity.1, graph_not_separable⟩

def basis (i : CompBasis) : CompBasis → ℂ := fun j => if j = i then 1 else 0

theorem reg_basis_states (i : CompBasis) :
    (K (1/3)).mulVec (basis i) = (if i = 3 then (-1/3:ℂ) else 1/3) • basis i ∧
    normSquared ((K (1/3)).mulVec (basis i)) = 1/9 := by
  constructor
  · rw [ralph_cphase_exact]
    ext j
    fin_cases i <;> fin_cases j <;>
      norm_num [CZ, basis, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal] <;> decide
  · apply cphase_success_prob_invariant
    simp [normSquared, basis]

theorem reg_t_half_no_cz :
    K (1/2) = Matrix.diagonal ![(1/2:ℂ),1/2,1/2,0] ∧
    (K (1/2)).mulVec (basis 3) = 0 := by
  have hk := postselected_kraus_exact (1/2) (by norm_num) (by norm_num)
  norm_num at hk
  refine ⟨hk, ?_⟩
  rw [hk]
  ext i
  fin_cases i <;>
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.diagonal, basis] <;> decide

theorem reg_t_one_identity : K 1 = 1 := by
  rw [postselected_kraus_exact 1 (by norm_num) (by norm_num)]
  ext i j : 2
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.diagonal, Matrix.one_apply]

/-- In the sorted occupation basis, exactly one photon in each qubit pair. -/
def AcceptedOccupation (k : FockBasis) : Prop :=
  (occupation k).1 < 2 ∧ 2 ≤ (occupation k).2 ∧ (occupation k).2 < 4

theorem acceptance_exact : ∀ k, AcceptedOccupation k ↔ ∃ i, k = compOccupation i := by
  unfold AcceptedOccupation
  decide

theorem occupation_sorted : ∀ k, (occupation k).1 ≤ (occupation k).2 := by decide

/-- Success probability from the density-matrix trace, for any trace-one matrix. -/
theorem density_success_trace (ρ : CompMatrix) (hρ : Matrix.trace ρ = 1) :
    Matrix.trace (K (1/3) * ρ * (K (1/3)).conjTranspose) = 1/9 := by
  rw [density_matrix_evolution]
  have hc : Matrix.trace (CZ * ρ * CZ.conjTranspose) = Matrix.trace ρ := by
    rw [Matrix.trace_mul_cycle, cz_unitary_hermitian_involutive.1, Matrix.one_mul]
  rw [Matrix.trace_smul, hc, hρ]
  norm_num

structure PhotonicsCPhaseGateUnitarySuite : Prop where
  dimension : Nat.choose (6 + 2 - 1) 2 = 21
  occupations : Function.Injective occupation ∧ ∀ i j, i ≤ j → ∃ k, occupation k = (i,j)
  substitution : ∀ A l x, ∑ k, monomial k x * symmetricLift A k l = monomial l
    (A.transpose.mulVec x)
  encoding : J.conjTranspose * J = 1
  acceptance : ∀ k, AcceptedOccupation k ↔ ∃ i, k = compOccupation i
  network_unitarity : ∀ T, 0 ≤ T → T ≤ 1 → (network T).conjTranspose * network T = 1
  fock_unitarity : ∀ T, 0 ≤ T → T ≤ 1 → (U_two_photon_six T).conjTranspose * U_two_photon_six T = 1
  compression : ∀ T, 0 ≤ T → T ≤ 1 → K T = Matrix.diagonal ![(T:ℂ), T, T, 2*T-1]
  controlled_sign : K (1/3) = (1/3:ℂ) • CZ
  probability : ∀ ψ, normSquared ψ = 1 → normSquared ((K (1/3)).mulVec ψ) = 1/9
  density : ∀ ρ, K (1/3) * ρ * (K (1/3)).conjTranspose = (1/9:ℂ) • (CZ * ρ * CZ.conjTranspose)
  gate_algebra : CZ.conjTranspose * CZ = 1 ∧ CZ.conjTranspose = CZ ∧ CZ * CZ = 1
  pauli : CZ * tensor PauliX 1 * CZ = tensor PauliX PauliZ ∧
    CZ * tensor 1 PauliX * CZ = tensor PauliZ PauliX ∧
    CZ * tensor PauliZ 1 * CZ = tensor PauliZ 1 ∧ CZ * tensor 1 PauliZ * CZ = tensor 1 PauliZ
  entanglement : CZ.mulVec plusPlus = graphState ∧ normSquared graphState = 1 ∧
    reducedA (pureDensity graphState) = (1/2:ℂ) • (1:QubitMatrix) ∧
    reducedB (pureDensity graphState) = (1/2:ℂ) • (1:QubitMatrix) ∧
    Matrix.trace (reducedA (pureDensity graphState) * reducedA (pureDensity graphState)) = (1/2:ℂ) ∧
    ¬ PureSeparable graphState
  local_bell : (tensor 1 Hadamard).mulVec graphState = bellState
  basis_regression : ∀ i, (K (1/3)).mulVec (basis i) = (if i = 3 then (-1/3:ℂ) else 1/3) • basis i ∧
    normSquared ((K (1/3)).mulVec (basis i)) = 1/9
  half_regression : K (1/2) = Matrix.diagonal ![(1/2:ℂ),1/2,1/2,0] ∧ (K (1/2)).mulVec (basis 3) = 0
  one_regression : K 1 = 1

theorem photonics_cphase_gate_master_suite : PhotonicsCPhaseGateUnitarySuite where
  dimension := fock_sector_dimension
  occupations := occupation_bijection
  substitution := symmetric_lift_substitution
  encoding := encoding_isometry
  acceptance := acceptance_exact
  network_unitarity := network_unitary
  fock_unitarity := two_photon_six_unitary
  compression := postselected_kraus_exact
  controlled_sign := ralph_cphase_exact
  probability := cphase_success_prob_invariant
  density := density_matrix_evolution
  gate_algebra := cz_unitary_hermitian_involutive
  pauli := cz_pauli_conjugation
  entanglement := cz_graph_state_entanglement
  local_bell := graph_bell_local_equivalence
  basis_regression := reg_basis_states
  half_regression := reg_t_half_no_cz
  one_regression := reg_t_one_identity

end PhotonicsCPhaseGateUnitary
