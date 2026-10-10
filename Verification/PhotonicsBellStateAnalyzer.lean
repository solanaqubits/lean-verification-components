/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.PhotonicsBeamSplitterPhaseShift
import Verification.PhotonicsHongOuMandelInterference
import Verification.PhotonicsCPhaseGateUnitary

/-! A concrete lossless Bell analyzer with ideal number-resolving detection.
The two-boson lift and compressed detector effects are derived from scattering.
This is not a bound over all linear-optical networks. -/
noncomputable section
-- Finite ten-mode expansions need a deeper expression traversal.
set_option maxRecDepth 4096
open scoped BigOperators ComplexConjugate
namespace PhotonicsBellStateAnalyzer
abbrev OpticalModes := Fin 4
abbrev FockBasis := Fin 10
abbrev CompBasis := Fin 4
abbrev ModeMatrix := Matrix OpticalModes OpticalModes ℂ
abbrev FockMatrix := Matrix FockBasis FockBasis ℂ
abbrev CompMatrix := Matrix CompBasis CompBasis ℂ

def rootTwo : ℂ := (Real.sqrt 2 : ℂ)
@[simp] theorem rootTwo_sq : rootTwo ^ 2 = 2 := by
  unfold rootTwo
  norm_cast
  exact Real.sq_sqrt (by norm_num)
@[simp] theorem rootTwo_cube : rootTwo ^ 3 = 2 * rootTwo := by
  rw [pow_succ, rootTwo_sq]
@[simp] theorem rootTwo_four : rootTwo ^ 4 = 4 := by
  rw [show (4:ℕ) = 2*2 by decide, pow_mul, rootTwo_sq]; norm_num
@[simp] theorem rootTwo_conj : (starRingEnd ℂ) rootTwo = rootTwo := by simp [rootTwo]
@[simp] theorem conj_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by exact Complex.conj_ofReal 2
theorem rootTwo_ne : rootTwo ≠ 0 := by
  unfold rootTwo
  exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))
theorem rootTwo_inv : rootTwo⁻¹ = rootTwo / 2 := by
  apply inv_eq_of_mul_eq_one_right
  calc rootTwo * (rootTwo / 2) = rootTwo ^ 2 / 2 := by ring
       _ = 1 := by rw [rootTwo_sq]; norm_num

/-- All unordered pairs, with double occupancy included. -/
def occupation : FockBasis → OpticalModes × OpticalModes :=
  ![(0,0), (0,1), (0,2), (0,3), (1,1), (1,2), (1,3), (2,2), (2,3), (3,3)]
theorem fock_sector_dimension : Nat.choose (4+2-1) 2 = 10 := by decide
theorem occupation_bijection : Function.Injective occupation ∧
    ∀ i j : OpticalModes, i ≤ j → ∃ k, occupation k = (i,j) := by decide

def monomial (k : FockBasis) (x : OpticalModes → ℂ) : ℂ :=
  let p := occupation k
  x p.1 * x p.2 / (if p.1 = p.2 then rootTwo else 1)

def symmetricLift (A : ModeMatrix) : FockMatrix := fun k l =>
  let o := occupation k
  let i := occupation l
  if i.1 = i.2 then
    if o.1 = o.2 then A o.1 i.1 ^ 2
    else rootTwo * A o.1 i.1 * A o.2 i.1
  else if o.1 = o.2 then rootTwo * A o.1 i.1 * A o.1 i.2
  else A o.1 i.1 * A o.2 i.2 + A o.1 i.2 * A o.2 i.1

set_option maxHeartbeats 2000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
/-- Polynomial substitution proves the normalized bosonic coefficient formula. -/
theorem symmetric_lift_substitution (A : ModeMatrix) (l : FockBasis) (x : OpticalModes → ℂ) :
    ∑ k, monomial k x * symmetricLift A k l = monomial l (A.transpose.mulVec x) := by
  fin_cases l <;>
    simp [monomial, symmetricLift, occupation, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, Matrix.transpose_apply] <;>
    simp only [div_eq_mul_inv, rootTwo_inv] <;> ring_nf <;> simp only [rootTwo_sq] <;> ring

/-- Identical imported splitters mix H with H and V with V, never H with V. -/
def U₁ : ModeMatrix :=
  let b := PhotonicsBeamSplitterPhaseShift.splitter (1/2)
  ![![b 0 0, 0, b 0 1, 0], ![0, b 0 0, 0, b 0 1],
    ![b 1 0, 0, b 1 1, 0], ![0, b 1 0, 0, b 1 1]]
theorem network_exact : U₁ =
    ![![rootTwo/2, 0, Complex.I*rootTwo/2, 0],
      ![0, rootTwo/2, 0, Complex.I*rootTwo/2],
      ![Complex.I*rootTwo/2, 0, rootTwo/2, 0],
      ![0, Complex.I*rootTwo/2, 0, rootTwo/2]] := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [U₁, PhotonicsBeamSplitterPhaseShift.splitter, rootTwo] <;>
    rw [show (Real.sqrt 2 : ℂ)⁻¹ = (Real.sqrt 2 : ℂ)/2 from rootTwo_inv] <;> ring

def U₂ : FockMatrix := symmetricLift U₁

theorem network_unitary : U₁.conjTranspose * U₁ = 1 := by
  ext i j : 2
  change (∑ k, star (U₁ k i) * U₁ k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;>
    norm_num [network_exact, Fin.sum_univ_succ] <;> ring_nf <;> norm_num

/-- Expanded form is a theorem about the lift, not its definition. -/
def expandedLift : FockMatrix :=
  ![![1/2, 0, 1*rootTwo*Complex.I/2, 0, 0, 0, 0, -1/2, 0, 0],
    ![0, 1/2, 0, 1*Complex.I/2, 0, 1*Complex.I/2, 0, 0, -1/2, 0],
    ![1*rootTwo*Complex.I/2, 0, 0, 0, 0, 0, 0, 1*rootTwo*Complex.I/2, 0, 0],
    ![0, 1*Complex.I/2, 0, 1/2, 0, -1/2, 0, 0, 1*Complex.I/2, 0],
    ![0, 0, 0, 0, 1/2, 0, 1*rootTwo*Complex.I/2, 0, 0, -1/2],
    ![0, 1*Complex.I/2, 0, -1/2, 0, 1/2, 0, 0, 1*Complex.I/2, 0],
    ![0, 0, 0, 0, 1*rootTwo*Complex.I/2, 0, 0, 0, 0, 1*rootTwo*Complex.I/2],
    ![-1/2, 0, 1*rootTwo*Complex.I/2, 0, 0, 0, 0, 1/2, 0, 0],
    ![0, -1/2, 0, 1*Complex.I/2, 0, 1*Complex.I/2, 0, 0, 1/2, 0],
    ![0, 0, 0, 0, -1/2, 0, 1*rootTwo*Complex.I/2, 0, 0, 1/2]]

set_option maxHeartbeats 4000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
theorem lift_exact : U₂ = expandedLift := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    simp [U₂, symmetricLift, network_exact, occupation, expandedLift] <;>
    ring_nf <;> norm_num <;> ring

set_option maxHeartbeats 4000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
theorem two_photon_unitary : U₂.conjTranspose * U₂ = 1 := by
  ext i j : 2
  change (∑ k, star (U₂ k i) * U₂ k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_succ, lift_exact, expandedLift] <;>
    ring_nf <;> norm_num

/-- Dual-rail input: HH, HV, VH, VV. -/
def encodingIndex : CompBasis → FockBasis := ![2,3,5,6]
def J : Matrix FockBasis CompBasis ℂ := fun k j => if k = encodingIndex j then 1 else 0

theorem encoding_isometry : J.conjTranspose * J = 1 := by
  ext i j : 2
  change (∑ k, star (J k i) * J k j) = if i = j then 1 else 0
  fin_cases i <;> fin_cases j <;> simp +decide [Fin.sum_univ_succ, J, encodingIndex]

/-- The PBS routes each (port, polarization) to a distinct ideal detector. -/
def detectorChannel : OpticalModes → Fin 2 × Fin 2 := ![(0,0),(0,1),(1,0),(1,1)]
theorem pbs_channel_bijection : Function.Bijective detectorChannel := by decide

inductive BellState where
  | psiMinus | psiPlus | phiPlus | phiMinus
  deriving DecidableEq

instance : Fintype BellState := ⟨{.psiMinus, .psiPlus, .phiPlus, .phiMinus}, by
  intro b; cases b <;> simp⟩

def bellVector : BellState → CompBasis → ℂ
  | .psiMinus => ![0, rootTwo/2, -rootTwo/2, 0]
  | .psiPlus => ![0, rootTwo/2, rootTwo/2, 0]
  | .phiPlus => ![rootTwo/2, 0, 0, rootTwo/2]
  | .phiMinus => ![rootTwo/2, 0, 0, -rootTwo/2]
def input (b : BellState) : FockBasis → ℂ := J.mulVec (bellVector b)
def output (b : BellState) : FockBasis → ℂ := U₂.mulVec (input b)

def expectedOutput : BellState → FockBasis → ℂ
  | .psiMinus => ![0, 0, 0, rootTwo/2, 0, -rootTwo/2, 0, 0, 0, 0]
  | .psiPlus => ![0, Complex.I*rootTwo/2, 0, 0, 0, 0, 0, 0, Complex.I*rootTwo/2, 0]
  | .phiPlus => ![Complex.I/2, 0, 0, 0, Complex.I/2, 0, 0, Complex.I/2, 0, Complex.I/2]
  | .phiMinus => ![Complex.I/2, 0, 0, 0, -Complex.I/2, 0, 0, Complex.I/2, 0, -Complex.I/2]

set_option maxHeartbeats 4000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
theorem bell_output_exact (b : BellState) : output b = expectedOutput b := by
  funext k
  cases b <;> fin_cases k <;>
    simp [output, input, lift_exact, expandedLift, J, encodingIndex, bellVector,
      expectedOutput, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
    ring_nf <;> norm_num <;> ring

theorem psi_minus_output_exact : output .psiMinus =
    ![0, 0, 0, rootTwo/2, 0, -rootTwo/2, 0, 0, 0, 0] := bell_output_exact _
theorem psi_plus_output_exact : output .psiPlus =
    ![0, Complex.I*rootTwo/2, 0, 0, 0, 0, 0, 0, Complex.I*rootTwo/2, 0] := bell_output_exact _
theorem phi_pm_output_exact :
    output .phiPlus = expectedOutput .phiPlus ∧ output .phiMinus = expectedOutput .phiMinus :=
  ⟨bell_output_exact _, bell_output_exact _⟩

def outcomeProbability (b : BellState) (k : FockBasis) : ℝ := Complex.normSq (output b k)
def probabilityTable : BellState → FockBasis → ℝ
  | .psiMinus => ![0,0,0,1/2,0,1/2,0,0,0,0]
  | .psiPlus => ![0,1/2,0,0,0,0,0,0,1/2,0]
  | .phiPlus | .phiMinus => ![1/4,0,0,0,1/4,0,0,1/4,0,1/4]

theorem probabilities_exact (b : BellState) (k : FockBasis) :
    outcomeProbability b k = probabilityTable b k := by
  cases b <;> fin_cases k <;>
    norm_num [outcomeProbability, bell_output_exact, expectedOutput, probabilityTable,
      Complex.normSq_apply, rootTwo]

theorem output_normalized (b : BellState) : ∑ k, outcomeProbability b k = 1 := by
  simp only [probabilities_exact]
  cases b <;> norm_num [probabilityTable, Fin.sum_univ_succ]

theorem phi_pm_identical_distributions :
    outcomeProbability .phiPlus = outcomeProbability .phiMinus := by
  funext k
  simp only [probabilities_exact, probabilityTable]

inductive DetectorOutcome where
  | psiMinus | psiPlus | inconclusive
  deriving DecidableEq

/-- All ten outcomes are classified, including zero-probability HH/VV split-port events. -/
def classify (k : FockBasis) : DetectorOutcome :=
  let a := detectorChannel (occupation k).1
  let b := detectorChannel (occupation k).2
  if a.2 ≠ b.2 then (if a.1 ≠ b.1 then .psiMinus else .psiPlus) else .inconclusive

theorem detector_classifier_spec : classify =
    ![.inconclusive, .psiPlus, .inconclusive, .psiMinus, .inconclusive,
      .psiMinus, .inconclusive, .inconclusive, .psiPlus, .inconclusive] := by decide

def classifiedProbability (b : BellState) (o : DetectorOutcome) : ℝ :=
  ∑ k, if classify k = o then outcomeProbability b k else 0

theorem classification_exact (b : BellState) (o : DetectorOutcome) :
    classifiedProbability b o =
      if (b = .psiMinus ∧ o = .psiMinus) ∨ (b = .psiPlus ∧ o = .psiPlus) ∨
        ((b = .phiPlus ∨ b = .phiMinus) ∧ o = .inconclusive) then 1 else 0 := by
  cases b <;> cases o <;>
    simp +decide [classifiedProbability, detector_classifier_spec, probabilities_exact,
      probabilityTable, Fin.sum_univ_succ] <;> norm_num

theorem psi_pm_perfect_discrimination : classifiedProbability .psiMinus .psiMinus = 1 ∧
    classifiedProbability .psiPlus .psiPlus = 1 := by simp [classification_exact]

theorem no_false_identification (b : BellState) :
    (b ≠ .psiMinus → classifiedProbability b .psiMinus = 0) ∧
    (b ≠ .psiPlus → classifiedProbability b .psiPlus = 0) := by
  cases b <;> simp [classification_exact]

/-- Optical transfer from the dual-rail input subspace to all detector modes. -/
def transfer : Matrix FockBasis CompBasis ℂ := U₂ * J

theorem transfer_exact : transfer =
    ![![rootTwo*Complex.I/2,0,0,0], ![0,Complex.I/2,Complex.I/2,0],
      ![0,0,0,0], ![0,1/2,-1/2,0], ![0,0,0,rootTwo*Complex.I/2],
      ![0,-1/2,1/2,0], ![0,0,0,0], ![rootTwo*Complex.I/2,0,0,0],
      ![0,Complex.I/2,Complex.I/2,0], ![0,0,0,rootTwo*Complex.I/2]] := by
  ext k j : 2
  change (∑ i, U₂ k i * J i j) = _
  fin_cases k <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_succ, lift_exact, expandedLift, J, encodingIndex]

/-- Orthogonal projectors for the three exhaustive groups of detector outcomes. -/
def detectorProjector (o : DetectorOutcome) : FockMatrix :=
  Matrix.diagonal (fun k => if classify k = o then 1 else 0)

def effect (o : DetectorOutcome) : CompMatrix :=
  transfer.conjTranspose * detectorProjector o * transfer

theorem effect_entry (o : DetectorOutcome) (i j : CompBasis) :
    effect o i j = ∑ k, if classify k = o then star (transfer k i) * transfer k j else 0 := by
  change (∑ k, (∑ l, star (transfer l i) *
    (if l = k then (if classify l = o then 1 else 0) else 0)) * transfer k j) = _
  simp

def bellProjector (b : BellState) : CompMatrix :=
  Matrix.vecMulVec (bellVector b) (star (bellVector b))

set_option maxHeartbeats 4000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
theorem effects_exact (o : DetectorOutcome) : effect o = match o with
    | .psiMinus => bellProjector .psiMinus
    | .psiPlus => bellProjector .psiPlus
    | .inconclusive => bellProjector .phiPlus + bellProjector .phiMinus := by
  ext i j : 2
  rw [effect_entry]
  cases o <;> fin_cases i <;> fin_cases j <;>
    simp +decide [Fin.sum_univ_succ, transfer_exact, detector_classifier_spec,
      bellProjector, bellVector, Matrix.vecMulVec] <;>
    ring_nf <;> norm_num

theorem povm_completeness : effect .psiMinus + effect .psiPlus + effect .inconclusive = 1 := by
  simp only [effects_exact]
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [bellProjector, bellVector, Matrix.vecMulVec] <;>
    ring_nf <;> norm_num

/-- The quadratic form uses the Euclidean/Born inner product, not the Pi sup norm. -/
def quadratic (A : CompMatrix) (ψ : CompBasis → ℂ) : ℂ :=
  ∑ i, ∑ j, star (ψ i) * A i j * ψ j

theorem projector_quadratic (b : BellState) (ψ : CompBasis → ℂ) :
    quadratic (bellProjector b) ψ =
    (Complex.normSq (∑ i, star (bellVector b i) * ψ i) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [quadratic, bellProjector, Matrix.vecMulVec, Pi.star_apply,
    map_sum, map_mul, starRingEnd_apply, star_star, Finset.sum_mul, Finset.mul_sum, Matrix.of_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem quadratic_add (A B : CompMatrix) (ψ : CompBasis → ℂ) :
    quadratic (A + B) ψ = quadratic A ψ + quadratic B ψ := by
  simp [quadratic, mul_add, add_mul, Finset.sum_add_distrib]

theorem effect_positive (o : DetectorOutcome) (ψ : CompBasis → ℂ) :
    0 ≤ (quadratic (effect o) ψ).re := by
  cases o <;> simp only [effects_exact, quadratic_add, projector_quadratic, Complex.add_re,
    Complex.ofReal_re]
  · exact Complex.normSq_nonneg _
  · exact Complex.normSq_nonneg _
  · exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- Explicit Hermiticity, together with effect_positive, certifies positive effects. -/
theorem effect_hermitian (o : DetectorOutcome) : (effect o).conjTranspose = effect o := by
  have h (b : BellState) : (bellProjector b).conjTranspose = bellProjector b := by
    ext i j : 2
    change star (bellVector b j * star (bellVector b i)) = bellVector b i * star (bellVector b j)
    simp [mul_comm]
  cases o <;> simp only [effects_exact, Matrix.conjTranspose_add, h]

/-- A stochastic postprocessing kernel cannot distinguish identical input laws. -/
theorem phi_postprocessing_equal {β : Type} (kernel : FockBasis → β → ℝ) (y : β) :
    (∑ k, outcomeProbability .phiPlus k * kernel k y) =
    ∑ k, outcomeProbability .phiMinus k * kernel k y := by
  rw [phi_pm_identical_distributions]

/-- No deterministic rule on the recorded outcome separates the two Phi states. -/
theorem phi_indistinguishability_classical (rule : FockBasis → Bool) :
    ¬ ((∀ k, 0 < outcomeProbability .phiPlus k → rule k = true) ∧
       (∀ k, 0 < outcomeProbability .phiMinus k → rule k = false)) := by
  intro h
  have hp : 0 < outcomeProbability .phiPlus 0 := by
    norm_num [probabilities_exact, probabilityTable]
  have hm : 0 < outcomeProbability .phiMinus 0 := by
    norm_num [probabilities_exact, probabilityTable]
  have ht := h.1 0 hp
  have hf := h.2 0 hm
  rw [ht] at hf
  cases hf

/-- For equal priors, even randomized binary guessing succeeds exactly half the time.
The identity holds for arbitrary real q; physical randomized rules additionally have 0 ≤ q ≤ 1. -/
theorem phi_equal_prior_guessing (q : FockBasis → ℝ) :
    (1/2 : ℝ) * (∑ k, outcomeProbability .phiPlus k * q k) +
      (1/2 : ℝ) * (∑ k, outcomeProbability .phiMinus k * (1 - q k)) = 1/2 := by
  simp [probabilities_exact, probabilityTable, Fin.sum_univ_succ]
  ring

lemma sum_bell (f : BellState → ℝ) : ∑ b, f b =
    f .psiMinus + f .psiPlus + f .phiPlus + f .phiMinus := by
  have h : (Finset.univ : Finset BellState) =
      {.psiMinus, .psiPlus, .phiPlus, .phiMinus} := by decide
  rw [h]
  simp
  ring

structure Prior where
  weight : BellState → ℝ
  nonnegative : ∀ b, 0 ≤ weight b
  total : ∑ b, weight b = 1

def successProbability (p : Prior) : ℝ := ∑ b, p.weight b *
  (classifiedProbability b .psiMinus + classifiedProbability b .psiPlus)

theorem success_probability_exact (p : Prior) :
    successProbability p = p.weight .psiMinus + p.weight .psiPlus := by
  simp [successProbability, sum_bell, classification_exact]

def uniformPrior : Prior where
  weight := fun _ => 1/4
  nonnegative := by intro b; norm_num
  total := by rw [sum_bell]; norm_num

theorem success_probability_uniform : successProbability uniformPrior = 1/2 := by
  norm_num [success_probability_exact, uniformPrior]

theorem success_probability_psi_only (p : Prior)
    (hplus : p.weight .phiPlus = 0) (hminus : p.weight .phiMinus = 0) :
    successProbability p = 1 := by
  have h := p.total
  simpa [sum_bell, hplus, hminus, success_probability_exact] using h

theorem psi_outputs_orthogonal :
    (∑ k, star (output .psiMinus k) * output .psiPlus k) = 0 := by
  simp [bell_output_exact, expectedOutput, Fin.sum_univ_succ]

set_option maxHeartbeats 4000000 in
-- Finite matrix expansion and polynomial normalization exceed the default tactic budget.
/-- Born probabilities computed at the detectors equal the compressed input effects. -/
theorem detector_born_rule (o : DetectorOutcome) (ψ : CompBasis → ℂ) :
    quadratic (effect o) ψ =
    ∑ k, if classify k = o then (Complex.normSq (transfer.mulVec ψ k) : ℂ) else 0 := by
  cases o <;>
    simp +decide [effects_exact, quadratic_add, projector_quadratic,
      Complex.normSq_eq_conj_mul_self, transfer_exact, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, detector_classifier_spec, bellVector, map_add, map_mul] <;>
    ring_nf <;> norm_num <;> ring

theorem classified_probability_normalized (b : BellState) :
    classifiedProbability b .psiMinus + classifiedProbability b .psiPlus +
      classifiedProbability b .inconclusive = 1 := by
  cases b <;> simp [classification_exact]

theorem zero_probability_unused_outcomes (b : BellState) :
    outcomeProbability b 2 = 0 ∧ outcomeProbability b 6 = 0 := by
  simp only [probabilities_exact]
  cases b <;> constructor <;> rfl

structure PhotonicsBellStateAnalyzerSuite : Prop where
  dimension : Nat.choose (4+2-1) 2 = 10
  occupation_complete : Function.Injective occupation ∧
    ∀ i j : OpticalModes, i ≤ j → ∃ k, occupation k = (i,j)
  substitution : ∀ (A : ModeMatrix) l x,
    ∑ k, monomial k x * symmetricLift A k l = monomial l (A.transpose.mulVec x)
  one_photon_unitary : U₁.conjTranspose * U₁ = 1
  two_photon_unitary : U₂.conjTranspose * U₂ = 1
  encoding : J.conjTranspose * J = 1
  pbs : Function.Bijective detectorChannel
  amplitudes : ∀ b, output b = expectedOutput b
  probabilities : ∀ b k, outcomeProbability b k = probabilityTable b k
  normalization : ∀ b, ∑ k, outcomeProbability b k = 1
  perfect_discrimination : classifiedProbability .psiMinus .psiMinus = 1 ∧
    classifiedProbability .psiPlus .psiPlus = 1
  no_false_results : ∀ b,
    (b ≠ .psiMinus → classifiedProbability b .psiMinus = 0) ∧
    (b ≠ .psiPlus → classifiedProbability b .psiPlus = 0)
  identical_phi : outcomeProbability .phiPlus = outcomeProbability .phiMinus
  effects : ∀ o, effect o = match o with
    | .psiMinus => bellProjector .psiMinus
    | .psiPlus => bellProjector .psiPlus
    | .inconclusive => bellProjector .phiPlus + bellProjector .phiMinus
  completeness : effect .psiMinus + effect .psiPlus + effect .inconclusive = 1
  positive : ∀ o ψ, 0 ≤ (quadratic (effect o) ψ).re
  hermitian : ∀ o, (effect o).conjTranspose = effect o
  born : ∀ o ψ, quadratic (effect o) ψ =
    ∑ k, if classify k = o then (Complex.normSq (transfer.mulVec ψ k) : ℂ) else 0
  success : ∀ p, successProbability p = p.weight .psiMinus + p.weight .psiPlus
  uniform_success : successProbability uniformPrior = 1/2
  psi_only_success : ∀ p, p.weight .phiPlus = 0 → p.weight .phiMinus = 0 →
    successProbability p = 1
  classical_indistinguishability : ∀ rule : FockBasis → Bool,
    ¬ ((∀ k, 0 < outcomeProbability .phiPlus k → rule k = true) ∧
       (∀ k, 0 < outcomeProbability .phiMinus k → rule k = false))
  randomized_guessing : ∀ q : FockBasis → ℝ,
    (1/2 : ℝ) * (∑ k, outcomeProbability .phiPlus k * q k) +
      (1/2 : ℝ) * (∑ k, outcomeProbability .phiMinus k * (1 - q k)) = 1/2

theorem photonics_bell_state_analyzer_master_suite : PhotonicsBellStateAnalyzerSuite where
  dimension := fock_sector_dimension
  occupation_complete := occupation_bijection
  substitution := symmetric_lift_substitution
  one_photon_unitary := network_unitary
  two_photon_unitary := two_photon_unitary
  encoding := encoding_isometry
  pbs := pbs_channel_bijection
  amplitudes := bell_output_exact
  probabilities := probabilities_exact
  normalization := output_normalized
  perfect_discrimination := psi_pm_perfect_discrimination
  no_false_results := no_false_identification
  identical_phi := phi_pm_identical_distributions
  effects := effects_exact
  completeness := povm_completeness
  positive := effect_positive
  hermitian := effect_hermitian
  born := detector_born_rule
  success := success_probability_exact
  uniform_success := success_probability_uniform
  psi_only_success := success_probability_psi_only
  classical_indistinguishability := phi_indistinguishability_classical
  randomized_guessing := phi_equal_prior_guessing

end PhotonicsBellStateAnalyzer
