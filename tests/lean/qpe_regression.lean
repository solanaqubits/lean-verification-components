import Verification.QuantumPhaseEstimation

noncomputable section
open QuantumPhaseEstimation

example : phaseValue ⟨false, false⟩ = 0 := by norm_num [phaseValue]
example : phaseValue ⟨false, true⟩ = 1 / 4 := by norm_num [phaseValue]
example : phaseValue ⟨true, false⟩ = 1 / 2 := by norm_num [phaseValue]
example : phaseValue ⟨true, true⟩ = 3 / 4 := by norm_num [phaseValue]

example : phaseIndex ⟨false, true⟩ = 1 := rfl
example : phaseIndex ⟨true, false⟩ = 2 := rfl
example : phaseIndex ⟨true, true⟩ = 3 := rfl

example (p : DyadicPhase2) : QFT_inv (qpePreState p) = basis (phaseIndex p) :=
  qpe_inverse_qft_exact p

example : qpePreState ⟨false, true⟩ =
    ![(1 / 2 : ℂ), Complex.I / 2, -1 / 2, -Complex.I / 2] := by
  funext k
  rw [qpe_pre_state_fourier]
  fin_cases k <;> apply Complex.ext <;>
    norm_num [fourierMatrix, phaseIndex, pow_succ, Complex.mul_re, Complex.mul_im]

-- Wrong Fourier sign produces index 3, not 1, for theta = 1/4.
example : QFT (qpePreState ⟨false, true⟩) 3 = 1 := by
  simp only [QFT, qpe_pre_state_fourier]
  apply Complex.ext <;>
    norm_num [fourierMatrix, phaseIndex, Fin.sum_univ_succ, pow_succ,
      Complex.mul_re, Complex.mul_im]

example : outcomeWeight (QFT_inv (qpePreState ⟨false, true⟩)) 3 = 0 := by
  rw [qpe_inverse_qft_exact]
  norm_num [outcomeWeight, basis, phaseIndex, Fin.ext_iff]

-- A normalized target with two nonzero complex coordinates, not a basis-state shortcut.
def testTarget : TargetState := ![(3 / 5 : ℂ), (4 / 5 : ℂ) * Complex.I]

theorem testTarget_norm : targetNormSquared testTarget = 1 := by
  norm_num [targetNormSquared, testTarget, Fin.sum_univ_succ, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]

def testInput (p : DyadicPhase2) : UnitaryEigenInput p where
  operator := phaseRoot p • LinearMap.id
  target := testTarget
  preserves_norm := by
    intro u
    change targetNormSquared (phaseRoot p • u) = targetNormSquared u
    rw [target_norm_smul, phase_root_norm, one_mul]
  normalized := testTarget_norm
  eigenstate := rfl

example (p : DyadicPhase2) (j : Fin 4) :
    marginalWeight (runQPE (testInput p).operator testTarget) j =
      if j = phaseIndex p then 1 else 0 := qpe_joint_distribution p (testInput p) j

example (p : DyadicPhase2) :
    jointNormSquared (runQPE (testInput p).operator testTarget) = 1 :=
  qpe_circuit_normalized p (testInput p)

example (p : DyadicPhase2) (j : Fin 4)
    (h : 0 < marginalWeight (runQPE (testInput p).operator testTarget) j) :
    decodeBits j = (p.b1, p.b2) := qpe_observed_bits p (testInput p) j h

-- Reversing the powers changes the pre-Fourier amplitude for the same concrete input.
def reversedPowers : JointState :=
  controlled ((testInput ⟨false, true⟩).operator.comp (testInput ⟨false, true⟩).operator)
    lowBit (controlled (testInput ⟨false, true⟩).operator highBit (prepareControl testTarget))

example : reversedPowers 1 0 = -(3 / 10 : ℂ) := by
  norm_num [reversedPowers, controlled, highBit, lowBit, prepareControl,
    hadamard_prepares_uniform, testInput, testTarget, phaseRoot, phaseIndex,
    LinearMap.comp_apply, smul_smul, Complex.ext_iff, Complex.mul_re, Complex.mul_im]

example : runControlled (testInput ⟨false, true⟩).operator testTarget 1 0 =
    (3 / 10 : ℂ) * Complex.I := by
  have he : (testInput ⟨false, true⟩).operator testTarget =
      phaseRoot ⟨false, true⟩ • testTarget := rfl
  rw [controlled_powers_kickback ⟨false, true⟩ _ _ he]
  change qpePreState ⟨false, true⟩ 1 * testTarget 0 = (3 / 10 : ℂ) * Complex.I
  rw [qpe_pre_state_fourier]
  apply Complex.ext <;>
    norm_num [fourierMatrix, phaseIndex, testTarget, Complex.mul_re, Complex.mul_im]

example : ¬ targetNormSquared (0 : TargetState) = 1 := by
  norm_num [targetNormSquared]

example (p : DyadicPhase2) (U : TargetState →ₗ[ℂ] TargetState) (u : TargetState)
    (h : U u = Complex.exp (2 * Real.pi * Complex.I * (phaseValue p : ℂ)) • u) :
    runQPE U u = fun j => basis (phaseIndex p) j • u := by
  rw [phaseRoot_exponential] at h
  exact qpe_joint_exact p U u h

example : QuantumPhaseEstimationSuite := quantum_phase_estimation_master_suite
