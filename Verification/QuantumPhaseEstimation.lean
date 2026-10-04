/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact two-bit quantum phase estimation

The ordered control basis is 00, 01, 10, 11. The high control drives U²,
the low control drives U. Forward Fourier entries have positive phase;
the inverse uses negative phase. Measurement weights use squared complex norms.
-/
noncomputable section
namespace QuantumPhaseEstimation
open scoped BigOperators ComplexConjugate

structure DyadicPhase2 where
  b1 : Bool
  b2 : Bool
  deriving DecidableEq, Repr

def phaseIndex (p : DyadicPhase2) : Fin 4 :=
  ⟨2 * p.b1.toNat + p.b2.toNat, by rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide⟩

def phaseValue (p : DyadicPhase2) : ℝ :=
  (if p.b1 then 1 / 2 else 0) + (if p.b2 then 1 / 4 else 0)

theorem phaseValue_eq_index (p : DyadicPhase2) :
    phaseValue p = (phaseIndex p).val / 4 := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [phaseValue, phaseIndex]

theorem phaseValue_range (p : DyadicPhase2) : 0 ≤ phaseValue p ∧ phaseValue p < 1 := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> norm_num [phaseValue]

abbrev ControlState := Fin 4 → ℂ

def basis (j : Fin 4) : ControlState := fun k => if k = j then 1 else 0

def normSquared (v : ControlState) : ℝ := ∑ k, Complex.normSq (v k)

def fourierMatrix (j k : Fin 4) : ℂ := (1 / 2) * Complex.I ^ (j.val * k.val)

def inverseFourierMatrix (j k : Fin 4) : ℂ := conj (fourierMatrix k j)

def QFT (v : ControlState) : ControlState := fun j => ∑ k, fourierMatrix j k * v k

def QFT_inv (v : ControlState) : ControlState :=
  fun j => ∑ k, inverseFourierMatrix j k * v k

def qpePreState (p : DyadicPhase2) : ControlState := fun k =>
  (1 / 2) * Complex.exp (2 * Real.pi * Complex.I * (phaseValue p : ℂ) * k.val)

theorem exp_quarter_turn (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) / 4) = Complex.I ^ n := by
  have he := Complex.exp_nat_mul ((Real.pi : ℂ) / 2 * Complex.I) n
  rw [Complex.exp_pi_div_two_mul_I] at he
  convert he using 1
  congr 1
  ring

theorem fourier_exponential (j k : Fin 4) :
    fourierMatrix j k = (1 / 2) *
      Complex.exp (2 * Real.pi * Complex.I * j.val * k.val / 4) := by
  rw [fourierMatrix, ← exp_quarter_turn]
  push_cast
  congr 2
  ring

theorem qpe_pre_state_fourier (p : DyadicPhase2) (k : Fin 4) :
    qpePreState p k = fourierMatrix k (phaseIndex p) := by
  rw [qpePreState, phaseValue_eq_index, fourier_exponential]
  push_cast
  congr 2
  ring

theorem inverse_fourier_basis (j : Fin 4) :
    QFT_inv (fun k => fourierMatrix k j) = basis j := by
  funext k
  fin_cases j <;> fin_cases k <;>
    apply Complex.ext <;>
    norm_num [QFT_inv, inverseFourierMatrix, fourierMatrix, basis, Fin.sum_univ_succ,
      pow_succ, Complex.mul_re, Complex.mul_im]

theorem fourier_inverse (v : ControlState) : QFT_inv (QFT v) = v := by
  funext j
  fin_cases j <;>
    apply Complex.ext <;>
    simp [QFT_inv, QFT, inverseFourierMatrix, fourierMatrix, Fin.sum_univ_succ,
      pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem inverse_fourier_inverse (v : ControlState) : QFT (QFT_inv v) = v := by
  funext j
  fin_cases j <;>
    apply Complex.ext <;>
    simp [QFT_inv, QFT, inverseFourierMatrix, fourierMatrix, Fin.sum_univ_succ,
      pow_succ, Complex.mul_re, Complex.mul_im] <;> ring

theorem qpe_inverse_qft_exact (p : DyadicPhase2) :
    QFT_inv (qpePreState p) = basis (phaseIndex p) := by
  have he : qpePreState p = fun k => fourierMatrix k (phaseIndex p) :=
    funext (qpe_pre_state_fourier p)
  rw [he]
  exact inverse_fourier_basis (phaseIndex p)

theorem qpe_pre_state_normalized (p : DyadicPhase2) : normSquared (qpePreState p) = 1 := by
  simp_rw [normSquared, qpe_pre_state_fourier]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;>
    norm_num [phaseIndex, fourierMatrix, Fin.sum_univ_succ, pow_succ,
      Complex.normSq_apply, Complex.mul_re, Complex.mul_im]

theorem qpe_inverse_qft_exact_cancellation (p : DyadicPhase2) (j : Fin 4)
    (hj : j ≠ phaseIndex p) : QFT_inv (qpePreState p) j = 0 := by
  rw [qpe_inverse_qft_exact]
  simp [basis, hj]

def outcomeWeight (v : ControlState) (j : Fin 4) : ℝ := Complex.normSq (v j)

theorem qpe_deterministic_success (p : DyadicPhase2) :
    outcomeWeight (QFT_inv (qpePreState p)) (phaseIndex p) = 1 := by
  rw [qpe_inverse_qft_exact]
  simp [outcomeWeight, basis]

def decodeBits (j : Fin 4) : Bool × Bool := (decide (2 ≤ j.val), decide (j.val % 2 = 1))

theorem qpe_reconstructs_dyadic_bits (p : DyadicPhase2) :
    decodeBits (phaseIndex p) = (p.b1, p.b2) := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> decide

theorem inverse_fourier_exponential (j k : Fin 4) :
    inverseFourierMatrix j k = (1 / 2) *
      Complex.exp (-(2 * Real.pi * Complex.I * j.val * k.val / 4)) := by
  simp only [inverseFourierMatrix, fourier_exponential, map_mul, map_div₀, map_ofNat,
    map_one, ← Complex.exp_conj, map_natCast, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  ring

theorem fourier_norm_preserved (v : ControlState) : normSquared (QFT v) = normSquared v := by
  simp [normSquared, QFT, fourierMatrix, Fin.sum_univ_succ, pow_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

theorem inverse_fourier_norm_preserved (v : ControlState) :
    normSquared (QFT_inv v) = normSquared v := by
  have h := fourier_norm_preserved (QFT_inv v)
  rw [inverse_fourier_inverse] at h
  exact h.symm

/-- The tensor product of the two real Hadamard matrices in the fixed bit order. -/
def hadamardPairMatrix (j k : Fin 4) : ℂ :=
  (1 / 2) * (-1) ^ (j.val / 2 * (k.val / 2) + j.val % 2 * (k.val % 2))

def hadamardPair (v : ControlState) : ControlState :=
  fun j => ∑ k, hadamardPairMatrix j k * v k

theorem hadamard_prepares_uniform : hadamardPair (basis 0) = fun _ => (1 / 2 : ℂ) := by
  funext j
  fin_cases j <;> norm_num [hadamardPair, hadamardPairMatrix, basis, Fin.sum_univ_succ]

theorem hadamard_pair_norm_preserved (v : ControlState) :
    normSquared (hadamardPair v) = normSquared v := by
  simp [normSquared, hadamardPair, hadamardPairMatrix, Fin.sum_univ_succ,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

abbrev TargetState := Fin 2 → ℂ
abbrev JointState := Fin 4 → TargetState

def targetNormSquared (u : TargetState) : ℝ := ∑ t, Complex.normSq (u t)

def jointNormSquared (v : JointState) : ℝ := ∑ k, targetNormSquared (v k)

def phaseRoot (p : DyadicPhase2) : ℂ := Complex.I ^ (phaseIndex p).val

theorem phaseRoot_exponential (p : DyadicPhase2) :
    Complex.exp (2 * Real.pi * Complex.I * (phaseValue p : ℂ)) = phaseRoot p := by
  rw [phaseValue_eq_index, phaseRoot]
  push_cast
  convert exp_quarter_turn (phaseIndex p).val using 1
  congr 1
  ring

def highBit (k : Fin 4) : Bool := decide (2 ≤ k.val)
def lowBit (k : Fin 4) : Bool := decide (k.val % 2 = 1)

def prepareControl (u : TargetState) : JointState :=
  fun k => hadamardPair (basis 0) k • u

def controlled (U : TargetState →ₗ[ℂ] TargetState) (bit : Fin 4 → Bool)
    (v : JointState) : JointState := fun k => if bit k then U (v k) else v k

def runControlled (U : TargetState →ₗ[ℂ] TargetState) (u : TargetState) : JointState :=
  controlled (U.comp U) highBit (controlled U lowBit (prepareControl u))

theorem controlled_preserves_norm (U : TargetState →ₗ[ℂ] TargetState)
    (hU : ∀ u, targetNormSquared (U u) = targetNormSquared u)
    (bit : Fin 4 → Bool) (v : JointState) :
    jointNormSquared (controlled U bit v) = jointNormSquared v := by
  apply Finset.sum_congr rfl
  intro k _
  simp only [controlled]
  split <;> simp_all

/-- Phase kickback is derived from the two controlled linear maps. -/
theorem controlled_powers_kickback (p : DyadicPhase2)
    (U : TargetState →ₗ[ℂ] TargetState) (u : TargetState)
    (hu : U u = phaseRoot p • u) :
    runControlled U u = fun k => qpePreState p k • u := by
  funext k
  rw [qpe_pre_state_fourier]
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> fin_cases k <;>
    simp [runControlled, controlled, highBit, lowBit, prepareControl,
      hadamard_prepares_uniform, LinearMap.comp_apply, map_smul, hu,
      fourierMatrix, phaseRoot, phaseIndex, pow_succ, smul_smul, mul_assoc,
      Complex.I_mul_I]

def inverseControl (v : JointState) : JointState :=
  fun j t => ∑ k, inverseFourierMatrix j k * v k t

theorem inverse_on_product (v : ControlState) (u : TargetState) :
    inverseControl (fun k => v k • u) = fun j => QFT_inv v j • u := by
  funext j t
  simp [inverseControl, QFT_inv, Finset.sum_mul, mul_assoc]

def runQPE (U : TargetState →ₗ[ℂ] TargetState) (u : TargetState) : JointState :=
  inverseControl (runControlled U u)

theorem qpe_joint_exact (p : DyadicPhase2) (U : TargetState →ₗ[ℂ] TargetState)
    (u : TargetState) (hu : U u = phaseRoot p • u) :
    runQPE U u = fun j => basis (phaseIndex p) j • u := by
  rw [runQPE, controlled_powers_kickback p U u hu, inverse_on_product,
    qpe_inverse_qft_exact]

def marginalWeight (v : JointState) (j : Fin 4) : ℝ := targetNormSquared (v j)

/-- A norm-preserving complex-linear target operator and a normalized exact eigenstate. -/
structure UnitaryEigenInput (p : DyadicPhase2) where
  operator : TargetState →ₗ[ℂ] TargetState
  target : TargetState
  preserves_norm : ∀ u, targetNormSquared (operator u) = targetNormSquared u
  normalized : targetNormSquared target = 1
  eigenstate : operator target = phaseRoot p • target

theorem qpe_joint_distribution (p : DyadicPhase2) (e : UnitaryEigenInput p) (j : Fin 4) :
    marginalWeight (runQPE e.operator e.target) j = if j = phaseIndex p then 1 else 0 := by
  rw [qpe_joint_exact p e.operator e.target e.eigenstate]
  by_cases h : j = phaseIndex p
  · simp [marginalWeight, basis, h, e.normalized]
  · simp [marginalWeight, basis, h, targetNormSquared]

theorem prepare_control_norm (u : TargetState) :
    jointNormSquared (prepareControl u) = targetNormSquared u := by
  simp [jointNormSquared, targetNormSquared, prepareControl, hadamard_prepares_uniform,
    Fin.sum_univ_succ, Complex.normSq_mul]
  ring

theorem inverse_control_norm (v : JointState) :
    jointNormSquared (inverseControl v) = jointNormSquared v := by
  calc
    _ = ∑ t, normSquared (QFT_inv (fun k => v k t)) := by
      simp only [jointNormSquared, targetNormSquared, inverseControl, normSquared, QFT_inv]
      exact Finset.sum_comm
    _ = ∑ t, normSquared (fun k => v k t) := by
      simp_rw [inverse_fourier_norm_preserved]
    _ = jointNormSquared v := by
      simp only [jointNormSquared, targetNormSquared, normSquared]
      exact Finset.sum_comm

theorem qpe_circuit_normalized (p : DyadicPhase2) (e : UnitaryEigenInput p) :
    jointNormSquared (runQPE e.operator e.target) = 1 := by
  rw [runQPE, inverse_control_norm, runControlled]
  rw [controlled_preserves_norm _ (by intro u; simp [LinearMap.comp_apply, e.preserves_norm])]
  rw [controlled_preserves_norm _ e.preserves_norm, prepare_control_norm, e.normalized]

theorem phase_root_norm (p : DyadicPhase2) : Complex.normSq (phaseRoot p) = 1 := by
  simp [phaseRoot, map_pow]

theorem target_norm_smul (z : ℂ) (u : TargetState) :
    targetNormSquared (z • u) = Complex.normSq z * targetNormSquared u := by
  simp [targetNormSquared, Complex.normSq_mul]
  ring

/-- A possible observed control value decodes to the supplied exact phase bits. -/
theorem qpe_observed_bits (p : DyadicPhase2) (e : UnitaryEigenInput p) (j : Fin 4)
    (hj : 0 < marginalWeight (runQPE e.operator e.target) j) :
    decodeBits j = (p.b1, p.b2) := by
  rw [qpe_joint_distribution] at hj
  by_cases he : j = phaseIndex p
  · subst j
    exact qpe_reconstructs_dyadic_bits p
  · simp [he] at hj

structure QuantumPhaseEstimationSuite : Prop where
  phase_range : ∀ p, 0 ≤ phaseValue p ∧ phaseValue p < 1
  fourier_inverse : ∀ v, QFT_inv (QFT v) = v
  inverse_fourier_inverse : ∀ v, QFT (QFT_inv v) = v
  fourier_norm : ∀ v, normSquared (QFT v) = normSquared v
  pre_normalized : ∀ p, normSquared (qpePreState p) = 1
  exact_interference : ∀ p, QFT_inv (qpePreState p) = basis (phaseIndex p)
  success : ∀ p, outcomeWeight (QFT_inv (qpePreState p)) (phaseIndex p) = 1
  decoded_bits : ∀ p, decodeBits (phaseIndex p) = (p.b1, p.b2)
  controlled_kickback : ∀ p U u, U u = phaseRoot p • u →
    runControlled U u = fun k => qpePreState p k • u
  joint_distribution : ∀ p (e : UnitaryEigenInput p) j,
    marginalWeight (runQPE e.operator e.target) j = if j = phaseIndex p then 1 else 0
  circuit_normalized : ∀ p (e : UnitaryEigenInput p),
    jointNormSquared (runQPE e.operator e.target) = 1

theorem quantum_phase_estimation_master_suite : QuantumPhaseEstimationSuite := {
  phase_range := phaseValue_range
  fourier_inverse := fourier_inverse
  inverse_fourier_inverse := inverse_fourier_inverse
  fourier_norm := fourier_norm_preserved
  pre_normalized := qpe_pre_state_normalized
  exact_interference := qpe_inverse_qft_exact
  success := qpe_deterministic_success
  decoded_bits := qpe_reconstructs_dyadic_bits
  controlled_kickback := controlled_powers_kickback
  joint_distribution := qpe_joint_distribution
  circuit_normalized := qpe_circuit_normalized
}

end QuantumPhaseEstimation
