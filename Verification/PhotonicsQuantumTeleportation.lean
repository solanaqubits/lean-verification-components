/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PhotonicsBellStateAnalyzer
import Verification.QuantumTeleportationProtocol
import Mathlib.Analysis.Matrix.Order

/-! Conditional optical teleportation from the actual ten detector amplitudes.
The Bell resource is supplied, and detection and classical feed-forward are ideal. -/
set_option maxRecDepth 4096
noncomputable section
open scoped BigOperators Kronecker
namespace PhotonicsQuantumTeleportation
open PhotonicsBellStateAnalyzer
abbrev Qubit := Fin 2
abbrev QMatrix := Matrix Qubit Qubit ℂ
abbrev Sector := Fin 10 × Qubit
def TeleportSpaceDim : ℕ := 20

theorem sector_dimension : Fintype.card Sector = TeleportSpaceDim := by decide

def resourceEmbedding : Matrix Sector Qubit ℂ := fun kc a =>
  rootTwo / 2 * J kc.1 (finProdFinEquiv (a, kc.2))
def embedding_state (ψ : Qubit → ℂ) : Fin 20 → ℂ :=
  fun j => resourceEmbedding.mulVec ψ (finProdFinEquiv.symm j)
def localEvolution : Matrix Sector Sector ℂ := U₂ ⊗ₖ (1 : QMatrix)
def opticalTransfer : Matrix Sector Qubit ℂ := localEvolution * resourceEmbedding

theorem local_evolution_unitary : localEvolution.conjTranspose * localEvolution = 1 := by
  simp only [localEvolution, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    ← Matrix.mul_kronecker_mul, two_photon_unitary, mul_one, Matrix.one_kronecker_one]

theorem resource_embedding_isometry : resourceEmbedding.conjTranspose * resourceEmbedding = 1 := by
  ext a b : 2
  change (∑ k, star (resourceEmbedding k a) * resourceEmbedding k b) = if a = b then 1 else 0
  fin_cases a <;> fin_cases b <;>
    simp +decide [resourceEmbedding, Fintype.sum_prod_type, Fin.sum_univ_succ,
      J, encodingIndex, finProdFinEquiv] <;> ring_nf <;> norm_num

/-- The remote photon keeps its polarization index; only Alice's sector evolves. -/
theorem optical_transfer_entry (k : Fin 10) (c a : Qubit) :
    opticalTransfer (k,c) a = rootTwo / 2 * transfer k (finProdFinEquiv (a,c)) := by
  change (∑ lc : Sector, (U₂ k lc.1 * (if c = lc.2 then 1 else 0)) *
    (rootTwo / 2 * J lc.1 (finProdFinEquiv (a,lc.2)))) = _
  simp only [Fintype.sum_prod_type, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  change (∑ l, U₂ k l * (rootTwo / 2 * J l (finProdFinEquiv (a,c)))) =
    rootTwo / 2 * ∑ l, U₂ k l * J l (finProdFinEquiv (a,c))
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  ring

def kraus_op (k : Fin 10) : QMatrix := fun c a => opticalTransfer (k,c) a

lemma qmul (A B : QMatrix) (i j : Qubit) :
    (A*B) i j = A i 0 * B 0 j + A i 1 * B 1 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_two]
lemma qstar (A : QMatrix) (i j : Qubit) : A.conjTranspose i j = star (A j i) := rfl
lemma qsmul (z : ℂ) (A : QMatrix) (i j : Qubit) : (z • A) i j = z * A i j := rfl
lemma qadd (A B : QMatrix) (i j : Qubit) : (A+B) i j = A i j + B i j := rfl

def X : QMatrix := !![0,1;1,0]
def Z : QMatrix := !![1,0;0,-1]
def P0 : QMatrix := !![1,0;0,0]
def P1 : QMatrix := !![0,0;0,1]

/-- Includes the opposite signs of the two singlet detector amplitudes. -/
def krausTable (k : Fin 10) : QMatrix := match k.val with
  | 0 => !![Complex.I/2,0;0,0]
  | 1 => !![0,Complex.I*rootTwo/4;Complex.I*rootTwo/4,0]
  | 3 => !![0,-rootTwo/4;rootTwo/4,0]
  | 4 => !![0,0;0,Complex.I/2]
  | 5 => !![0,rootTwo/4;-rootTwo/4,0]
  | 7 => !![Complex.I/2,0;0,0]
  | 8 => !![0,Complex.I*rootTwo/4;Complex.I*rootTwo/4,0]
  | 9 => !![0,0;0,Complex.I/2]
  | _ => 0

theorem kraus_exact (k : Fin 10) : kraus_op k = krausTable k := by
  ext c a : 2
  simp only [kraus_op, optical_transfer_entry]
  fin_cases k <;> fin_cases c <;> fin_cases a <;>
    norm_num [krausTable, transfer_exact, finProdFinEquiv] <;>
    ring_nf <;> norm_num <;> ring

set_option maxHeartbeats 2000000 in
-- Expanding ten detector outcomes exceeds the default elaboration budget.
theorem kraus_completeness : ∑ k : Fin 10, (kraus_op k).conjTranspose * kraus_op k = 1 := by
  ext a b : 2
  change (∑ k, ∑ l, star (kraus_op k l a) * kraus_op k l b) = if a = b then 1 else 0
  fin_cases a <;> fin_cases b <;>
    norm_num [kraus_exact, krausTable, Fin.sum_univ_succ, map_ofNat] <;> ring_nf <;> norm_num

def branch (o : DetectorOutcome) (ρ : QMatrix) : QMatrix :=
  ∑ k, if classify k = o then kraus_op k * ρ * (kraus_op k).conjTranspose else 0

def branchFormula (o : DetectorOutcome) (ρ : QMatrix) : QMatrix := match o with
  | .psiMinus => (1/4 : ℂ) • ((X*Z) * ρ * (X*Z).conjTranspose)
  | .psiPlus => (1/4 : ℂ) • (X * ρ * X.conjTranspose)
  | .inconclusive => (1/2 : ℂ) • (P0 * ρ * P0 + P1 * ρ * P1)

set_option maxHeartbeats 4000000 in
-- Expanding all three detector branches exceeds the default elaboration budget.
theorem branch_exact (o : DetectorOutcome) (ρ : QMatrix) : branch o ρ = branchFormula o ρ := by
  cases o <;> ext a b : 2 <;>
    simp only [branch, branchFormula, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, qmul, qstar] <;>
    fin_cases a <;> fin_cases b <;>
    simp +decide [detector_classifier_spec, kraus_exact, krausTable, X, Z, P0, P1,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply, map_ofNat,
      Fin.sum_univ_succ] <;> ring_nf <;> norm_num <;> ring

theorem branch_psi_minus_exact (ρ : QMatrix) : branch .psiMinus ρ =
    (1/4 : ℂ) • ((X*Z) * ρ * (X*Z).conjTranspose) := branch_exact _ _
theorem branch_psi_plus_exact (ρ : QMatrix) : branch .psiPlus ρ =
    (1/4 : ℂ) • (X * ρ * X.conjTranspose) := branch_exact _ _

def correction : DetectorOutcome → QMatrix
  | .psiMinus => Z*X
  | .psiPlus => X
  | .inconclusive => 1

def corrected (o : DetectorOutcome) (ρ : QMatrix) :=
  correction o * branch o ρ * (correction o).conjTranspose
def successful (ρ : QMatrix) := corrected .psiMinus ρ + corrected .psiPlus ρ

theorem corrections_unitary (o : DetectorOutcome) :
    (correction o).conjTranspose * correction o = 1 := by
  ext a b : 2
  cases o <;> fin_cases a <;> fin_cases b <;>
    norm_num [correction, X, Z, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Matrix.add_apply, Matrix.vecMul, dotProduct, Matrix.one_apply,
      Fin.sum_univ_succ]

theorem pauli_corrections_exact (ρ : QMatrix) :
    corrected .psiMinus ρ = (1/4 : ℂ) • ρ ∧ corrected .psiPlus ρ = (1/4 : ℂ) • ρ := by
  constructor <;> ext a b : 2 <;> fin_cases a <;> fin_cases b <;>
    norm_num [corrected, correction, branch_exact, branchFormula, X, Z,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_succ]

theorem successful_channel_exact (ρ : QMatrix) : successful ρ = (1/2 : ℂ) • ρ := by
  rw [successful, (pauli_corrections_exact ρ).1, (pauli_corrections_exact ρ).2, ← add_smul]
  norm_num

def total (ρ : QMatrix) := branch .psiMinus ρ + branch .psiPlus ρ + branch .inconclusive ρ

theorem total_exact (ρ : QMatrix) : total ρ = (ρ.trace / 2) • (1 : QMatrix) := by
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    norm_num [total, branch_exact, branchFormula, X, Z, P0, P1,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.trace, Matrix.vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

theorem no_signalling_theorem (ρ : QMatrix) (hρ : ρ.trace = 1) :
    total ρ = (1/2 : ℂ) • (1 : QMatrix) := by rw [total_exact, hρ]

theorem branch_trace (o : DetectorOutcome) (ρ : QMatrix) :
    (branch o ρ).trace = (if o = .inconclusive then 1/2 else 1/4) * ρ.trace := by
  cases o <;> norm_num +decide [branch_exact, branchFormula, X, Z, P0, P1,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.trace, Matrix.vecMul, dotProduct, Matrix.one_apply, Fin.sum_univ_succ] <;> ring

theorem branch_probabilities_invariant (ρ : QMatrix) (hρ : ρ.trace = 1) :
    (branch .psiMinus ρ).trace = 1/4 ∧ (branch .psiPlus ρ).trace = 1/4 ∧
    (branch .inconclusive ρ).trace = 1/2 ∧
    (branch .psiMinus ρ + branch .psiPlus ρ).trace = 1/2 := by
  simp only [branch_trace, Matrix.trace_add, hρ]
  norm_num +decide

def normalizedOutput (ρ : QMatrix) :=
  ((branch .psiMinus ρ + branch .psiPlus ρ).trace)⁻¹ • successful ρ

theorem teleportation_exact (ρ : QMatrix) (hρ : ρ.trace = 1) : normalizedOutput ρ = ρ := by
  simp [normalizedOutput, (branch_probabilities_invariant ρ hρ).2.2.2,
    successful_channel_exact, smul_smul]

/-- Discarding Alice's detector record is the partial trace over her Fock sector. -/
def partialTrace (D : Matrix Sector Sector ℂ) : QMatrix :=
  fun c d => ∑ k : Fin 10, D (k,c) (k,d)

theorem total_as_kraus_sum (ρ : QMatrix) :
    total ρ = ∑ k : Fin 10, kraus_op k * ρ * (kraus_op k).conjTranspose := by
  simp only [total, branch, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  cases classify k <;> simp

theorem optical_partial_trace (ρ : QMatrix) :
    partialTrace (opticalTransfer * ρ * opticalTransfer.conjTranspose) = total ρ := by
  rw [total_as_kraus_sum]
  ext c d : 2
  change (∑ k, ∑ a : Qubit, (∑ b : Qubit, opticalTransfer (k,c) b * ρ b a) *
    star (opticalTransfer (k,d) a)) =
    ∑ k, ∑ a : Qubit, (∑ b : Qubit, kraus_op k c b * ρ b a) * star (kraus_op k d a)
  rfl

theorem resource_partial_trace (ρ : QMatrix) :
    partialTrace (resourceEmbedding * ρ * resourceEmbedding.conjTranspose) =
      (ρ.trace / 2) • (1 : QMatrix) := by
  ext c d : 2
  change (∑ k, ∑ a : Qubit, (∑ b : Qubit, resourceEmbedding (k,c) b * ρ b a) *
    star (resourceEmbedding (k,d) a)) = (ρ.trace / 2) * (if c = d then 1 else 0)
  fin_cases c <;> fin_cases d <;>
    norm_num +decide [resourceEmbedding, J, encodingIndex, finProdFinEquiv,
      Matrix.trace, Fin.sum_univ_succ] <;> ring_nf <;> norm_num <;> ring

theorem no_signalling_partial_trace (ρ : QMatrix) :
    partialTrace (opticalTransfer * ρ * opticalTransfer.conjTranspose) =
    partialTrace (resourceEmbedding * ρ * resourceEmbedding.conjTranspose) := by
  rw [optical_partial_trace, resource_partial_trace, total_exact]

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-- Squared Uhlmann fidelity, including genuinely mixed density operators. -/
def fidelity (ρ σ : QMatrix) : ℝ :=
  Complex.normSq (CFC.sqrt (CFC.sqrt ρ * σ * CFC.sqrt ρ)).trace

def IsDensity (ρ : QMatrix) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

theorem fidelity_self (ρ : QMatrix) (hp : ρ.PosSemidef) (ht : ρ.trace = 1) :
    fidelity ρ ρ = 1 := by
  have hs := CFC.sqrt_mul_sqrt_self ρ hp.nonneg
  have h : CFC.sqrt ρ * ρ * CFC.sqrt ρ = ρ * ρ := by
    calc
      _ = CFC.sqrt ρ * (CFC.sqrt ρ * CFC.sqrt ρ) * CFC.sqrt ρ :=
        congrArg (fun t => CFC.sqrt ρ * t * CFC.sqrt ρ) hs.symm
      _ = (CFC.sqrt ρ * CFC.sqrt ρ) * (CFC.sqrt ρ * CFC.sqrt ρ) := by
        simp only [mul_assoc]
      _ = ρ * ρ := by rw [hs]
  simp only [fidelity, h, CFC.sqrt_mul_self ρ hp.nonneg, ht]
  norm_num

theorem teleportation_fidelity_one (ρ : QMatrix) (hρ : IsDensity ρ) :
    normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1 := by
  rw [teleportation_exact ρ hρ.2]
  exact ⟨rfl, fidelity_self ρ hρ.1 hρ.2⟩

theorem branch_positive (o : DetectorOutcome) (ρ : QMatrix) (hρ : ρ.PosSemidef) :
    (branch o ρ).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k hk
  split_ifs
  · exact hρ.mul_mul_conjTranspose_same (kraus_op k)
  · exact Matrix.PosSemidef.zero

theorem full_instrument_trace_preserving (ρ : QMatrix) : (total ρ).trace = ρ.trace := by
  rw [total_exact]
  norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply]
  ring

/-- Ideal Bell contraction of the supplied resource, before detector grouping. -/
def bellContraction (b : BellState) : QMatrix := fun c a =>
  ∑ k : Fin 10, star (input b k) * resourceEmbedding (k,c) a

def oldOutcome : BellState → QuantumTeleportationProtocol.BellMeasurement
  | .psiMinus => .psiMinus
  | .psiPlus => .psiPlus
  | .phiPlus => .phiPlus
  | .phiMinus => .phiMinus

def stateVector (s : QuantumTeleportationProtocol.QubitState) : Qubit → ℂ :=
  ![s.alpha, s.beta]

set_option maxHeartbeats 2000000 in
-- Four Bell contractions require expansion of the ten-dimensional embedding.
theorem bridge_to_quantum_teleportation_protocol
    (b : BellState) (ψ : QuantumTeleportationProtocol.QubitState) :
    (bellContraction b).mulVec (stateVector ψ) =
    (1/2 : ℂ) • stateVector (QuantumTeleportationProtocol.bobReceivedState (oldOutcome b) ψ) := by
  funext c
  cases b <;> fin_cases c <;>
    norm_num +decide [bellContraction, input, resourceEmbedding, J, encodingIndex, bellVector,
      oldOutcome, stateVector, QuantumTeleportationProtocol.bobReceivedState,
      Matrix.mulVec, dotProduct, finProdFinEquiv, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num <;> ring

set_option maxHeartbeats 2000000 in
-- Four detector identities require finite expansion of the Bell contractions.
theorem optical_bell_branch_bridge :
    kraus_op 3 = (rootTwo/2) • bellContraction .psiMinus ∧
    kraus_op 5 = (-rootTwo/2) • bellContraction .psiMinus ∧
    kraus_op 1 = (Complex.I*rootTwo/2) • bellContraction .psiPlus ∧
    kraus_op 8 = (Complex.I*rootTwo/2) • bellContraction .psiPlus := by
  repeat' constructor
  all_goals
    ext c a : 2
    fin_cases c <;> fin_cases a <;>
      norm_num +decide [kraus_exact, krausTable, bellContraction, input, resourceEmbedding, J,
        encodingIndex, bellVector, Matrix.mulVec, dotProduct, finProdFinEquiv,
        Fin.sum_univ_succ] <;> ring_nf <;> norm_num <;> ring

def pureDensity (ψ : Qubit → ℂ) : QMatrix := fun a b => ψ a * star (ψ b)
def ket0 : Qubit → ℂ := ![1,0]
def ket1 : Qubit → ℂ := ![0,1]
def ketPlus : Qubit → ℂ := ![rootTwo/2,rootTwo/2]
def ketPlusI : Qubit → ℂ := ![rootTwo/2,Complex.I*rootTwo/2]

theorem pure_density_positive (ψ : Qubit → ℂ) : (pureDensity ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ

theorem regression_density_states :
    IsDensity (pureDensity ket0) ∧ IsDensity (pureDensity ket1) ∧
    IsDensity (pureDensity ketPlus) ∧ IsDensity (pureDensity ketPlusI) := by
  refine ⟨⟨pure_density_positive _, ?_⟩, ⟨pure_density_positive _, ?_⟩,
    ⟨pure_density_positive _, ?_⟩, ⟨pure_density_positive _, ?_⟩⟩
  all_goals norm_num [pureDensity, ket0, ket1, ketPlus, ketPlusI, Matrix.trace,
        Fin.sum_univ_succ] <;> ring_nf <;> norm_num

theorem reg_teleportation_states :
    normalizedOutput (pureDensity ket0) = pureDensity ket0 ∧
    normalizedOutput (pureDensity ket1) = pureDensity ket1 ∧
    normalizedOutput (pureDensity ketPlus) = pureDensity ketPlus ∧
    normalizedOutput (pureDensity ketPlusI) = pureDensity ketPlusI :=
  ⟨teleportation_exact _ regression_density_states.1.2,
   teleportation_exact _ regression_density_states.2.1.2,
   teleportation_exact _ regression_density_states.2.2.1.2,
   teleportation_exact _ regression_density_states.2.2.2.2⟩

/-- Incorrect feed-forward, normalized by the singlet probability 1/4. -/
def wrongCorrection (ρ : QMatrix) := (4 : ℂ) • (Z * branch .psiMinus ρ * Z.conjTranspose)

theorem wrong_correction_residual (ρ : QMatrix) : wrongCorrection ρ = X * ρ * X.conjTranspose := by
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    norm_num [wrongCorrection, branch_exact, branchFormula, X, Z,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;> ring

theorem wrong_correction_zero : wrongCorrection (pureDensity ket0) = pureDensity ket1 := by
  rw [wrong_correction_residual]
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    norm_num [pureDensity, ket0, ket1, X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-- The originally suggested |+> example does not witness failure: X|+> = |+>. -/
theorem wrong_correction_plus_unchanged :
    wrongCorrection (pureDensity ketPlus) = pureDensity ketPlus := by
  rw [wrong_correction_residual]
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    norm_num [pureDensity, ketPlus, X, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem counterexample_wrong_phase_correction :
    fidelity (pureDensity ket0) (wrongCorrection (pureDensity ket0)) = 0 ∧
    fidelity (pureDensity ket0) (wrongCorrection (pureDensity ket0)) < 1 := by
  have hi : pureDensity ket0 * pureDensity ket0 = pureDensity ket0 := by
    ext a b : 2
    fin_cases a <;> fin_cases b <;>
      norm_num [pureDensity, ket0, Matrix.mul_apply, Fin.sum_univ_succ]
  have hz : pureDensity ket0 * pureDensity ket1 * pureDensity ket0 = 0 := by
    ext a b : 2
    fin_cases a <;> fin_cases b <;>
      norm_num [pureDensity, ket0, ket1, Matrix.mul_apply, Fin.sum_univ_succ]
  have hs : CFC.sqrt (pureDensity ket0) = pureDensity ket0 :=
    CFC.sqrt_unique hi (pure_density_positive ket0).nonneg
  rw [wrong_correction_zero]
  simp only [fidelity, hs, hz]
  norm_num

/-- There are four inconclusive double occupations and two identically dark outcomes. -/
theorem reg_dark_outcomes : kraus_op 2 = 0 ∧ kraus_op 6 = 0 := by
  norm_num [kraus_exact, krausTable]

def ketMinusI : Qubit → ℂ := ![rootTwo/2,-Complex.I*rootTwo/2]

theorem wrong_correction_plus_i :
    wrongCorrection (pureDensity ketPlusI) = pureDensity ketMinusI := by
  rw [wrong_correction_residual]
  ext a b : 2
  fin_cases a <;> fin_cases b <;>
    norm_num [pureDensity, ketPlusI, ketMinusI, X, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ] <;> ring_nf <;> simp <;> ring

theorem counterexample_wrong_relative_phase :
    fidelity (pureDensity ketPlusI) (wrongCorrection (pureDensity ketPlusI)) = 0 := by
  have hi : pureDensity ketPlusI * pureDensity ketPlusI = pureDensity ketPlusI := by
    ext a b : 2
    fin_cases a <;> fin_cases b <;>
      norm_num [pureDensity, ketPlusI, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring_nf <;> simp <;> ring
  have hz : pureDensity ketPlusI * pureDensity ketMinusI * pureDensity ketPlusI = 0 := by
    ext a b : 2
    fin_cases a <;> fin_cases b <;>
      norm_num [pureDensity, ketPlusI, ketMinusI, Matrix.mul_apply, Fin.sum_univ_succ] <;>
      ring_nf <;> simp <;> ring
  have hs : CFC.sqrt (pureDensity ketPlusI) = pureDensity ketPlusI :=
    CFC.sqrt_unique hi (pure_density_positive ketPlusI).nonneg
  rw [wrong_correction_plus_i]
  simp only [fidelity, hs, hz]
  norm_num

def matrixOfOld (M : QuantumTeleportationProtocol.CMat2) : QMatrix :=
  !![M.a11,M.a12;M.a21,M.a22]

theorem correction_protocol_bridge :
    correction .psiMinus = matrixOfOld (QuantumTeleportationProtocol.bobCorrectionOp .psiMinus) ∧
    correction .psiPlus = matrixOfOld (QuantumTeleportationProtocol.bobCorrectionOp .psiPlus) := by
  constructor <;> ext a b : 2 <;> fin_cases a <;> fin_cases b <;>
    norm_num [correction, X, Z, matrixOfOld, QuantumTeleportationProtocol.bobCorrectionOp,
      QuantumTeleportationProtocol.pauliZX, QuantumTeleportationProtocol.pauliX,
      Matrix.mul_apply, Fin.sum_univ_succ]

/-- Mixed-state regression: fidelity is not the purity Tr(ρ²). -/
theorem reg_maximally_mixed :
    let ρ : QMatrix := (1/2 : ℂ) • 1
    normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1 ∧ (ρ*ρ).trace = 1/2 := by
  dsimp only
  have hp : ((1/2 : ℂ) • (1 : QMatrix)).PosSemidef := by
    have h : (1/2 : ℂ) • (1 : QMatrix) = Matrix.diagonal (fun _ : Qubit => (1/2 : ℂ)) := by
      ext a b : 2
      fin_cases a <;> fin_cases b <;> norm_num [Matrix.one_apply, Matrix.diagonal]
    rw [h]
    exact Matrix.posSemidef_diagonal_iff.mpr (by intro i; norm_num [Complex.nonneg_iff])
  have ht : ((1/2 : ℂ) • (1 : QMatrix)).trace = 1 := by
    norm_num [Matrix.trace, Fin.sum_univ_succ, Matrix.one_apply]
  refine ⟨teleportation_exact _ ht, (teleportation_fidelity_one _ ⟨hp,ht⟩).2, ?_⟩
  norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-- Exported contract connects physical construction, probabilities, recovery and scope checks. -/
structure PhotonicsQuantumTeleportationSuite : Prop where
  dimension : Fintype.card Sector = TeleportSpaceDim
  resource_isometry : resourceEmbedding.conjTranspose * resourceEmbedding = 1
  local_unitary : localEvolution.conjTranspose * localEvolution = 1
  derived_kraus : ∀ k, kraus_op k = krausTable k
  complete : ∑ k : Fin 10, (kraus_op k).conjTranspose * kraus_op k = 1
  branch_maps : ∀ o ρ, branch o ρ = branchFormula o ρ
  positive : ∀ o ρ, ρ.PosSemidef → (branch o ρ).PosSemidef
  probabilities : ∀ ρ, ρ.trace = 1 →
    (branch .psiMinus ρ).trace = 1/4 ∧ (branch .psiPlus ρ).trace = 1/4 ∧
    (branch .inconclusive ρ).trace = 1/2 ∧
    (branch .psiMinus ρ + branch .psiPlus ρ).trace = 1/2
  unitary_corrections : ∀ o, (correction o).conjTranspose * correction o = 1
  corrected_maps : ∀ ρ, corrected .psiMinus ρ = (1/4 : ℂ) • ρ ∧
    corrected .psiPlus ρ = (1/4 : ℂ) • ρ
  successful_map : ∀ ρ, successful ρ = (1/2 : ℂ) • ρ
  recovery : ∀ ρ, IsDensity ρ → normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1
  nonselective : ∀ ρ, total ρ = (ρ.trace / 2) • (1 : QMatrix)
  partial_trace : ∀ ρ, partialTrace (opticalTransfer * ρ * opticalTransfer.conjTranspose) = total ρ
  no_signalling : ∀ ρ, partialTrace (opticalTransfer * ρ * opticalTransfer.conjTranspose) =
    partialTrace (resourceEmbedding * ρ * resourceEmbedding.conjTranspose)
  trace_preserving : ∀ ρ, (total ρ).trace = ρ.trace
  protocol_bridge : ∀ b ψ, (bellContraction b).mulVec (stateVector ψ) =
    (1/2 : ℂ) • stateVector (QuantumTeleportationProtocol.bobReceivedState (oldOutcome b) ψ)
  optical_bridge : kraus_op 3 = (rootTwo/2) • bellContraction .psiMinus ∧
    kraus_op 5 = (-rootTwo/2) • bellContraction .psiMinus ∧
    kraus_op 1 = (Complex.I*rootTwo/2) • bellContraction .psiPlus ∧
    kraus_op 8 = (Complex.I*rootTwo/2) • bellContraction .psiPlus
  wrong_phase : fidelity (pureDensity ketPlusI) (wrongCorrection (pureDensity ketPlusI)) = 0
  plus_not_counterexample : wrongCorrection (pureDensity ketPlus) = pureDensity ketPlus
  basis_regressions : normalizedOutput (pureDensity ket0) = pureDensity ket0 ∧
    normalizedOutput (pureDensity ket1) = pureDensity ket1 ∧
    normalizedOutput (pureDensity ketPlus) = pureDensity ketPlus ∧
    normalizedOutput (pureDensity ketPlusI) = pureDensity ketPlusI
  mixed_regression : let ρ : QMatrix := (1/2 : ℂ) • 1
    normalizedOutput ρ = ρ ∧ fidelity ρ (normalizedOutput ρ) = 1 ∧ (ρ*ρ).trace = 1/2

theorem photonics_quantum_teleportation_master_suite : PhotonicsQuantumTeleportationSuite := {
  dimension := sector_dimension
  resource_isometry := resource_embedding_isometry
  local_unitary := local_evolution_unitary
  derived_kraus := kraus_exact
  complete := kraus_completeness
  branch_maps := branch_exact
  positive := branch_positive
  probabilities := branch_probabilities_invariant
  unitary_corrections := corrections_unitary
  corrected_maps := pauli_corrections_exact
  successful_map := successful_channel_exact
  recovery := teleportation_fidelity_one
  nonselective := total_exact
  partial_trace := optical_partial_trace
  no_signalling := no_signalling_partial_trace
  trace_preserving := full_instrument_trace_preserving
  protocol_bridge := bridge_to_quantum_teleportation_protocol
  optical_bridge := optical_bell_branch_bridge
  wrong_phase := counterexample_wrong_relative_phase
  plus_not_counterexample := wrong_correction_plus_unchanged
  basis_regressions := reg_teleportation_states
  mixed_regression := reg_maximally_mixed
}

#print axioms photonics_quantum_teleportation_master_suite

end PhotonicsQuantumTeleportation
