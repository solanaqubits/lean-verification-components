/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBB84Protocol
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Ideal BB84 measurement and independent intercept-resend experiments.
Born measurement is a modeling postulate; its probabilities are calculated below. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace QuantumBB84ProtocolQBER
abbrev BB84Basis := Fin 2
abbrev BB84Bit := Fin 2
namespace BB84Basis
def Z : BB84Basis := 0
def X : BB84Basis := 1
end BB84Basis
namespace BB84Bit
def zero : BB84Bit := 0
def one : BB84Bit := 1
end BB84Bit
abbrev QMatrix := Matrix (Fin 2) (Fin 2) ℂ

def rootTwo : ℂ := (Real.sqrt 2 : ℂ)
@[simp] theorem rootTwo_sq : rootTwo ^ 2 = 2 := by
  unfold rootTwo
  norm_cast
  exact Real.sq_sqrt (by norm_num)
@[simp] theorem rootTwo_star : (starRingEnd ℂ) rootTwo = rootTwo := by simp [rootTwo]

def ket (b : BB84Basis) (x : BB84Bit) : Matrix (Fin 2) (Fin 1) ℂ :=
  fun i _ => if b = 0 then (if i = x then 1 else 0)
    else if i = 0 then rootTwo / 2 else if x = 0 then rootTwo / 2 else -rootTwo / 2

def P (b : BB84Basis) (x : BB84Bit) : QMatrix := ket b x * (ket b x).conjTranspose

def projectorTable (b : BB84Basis) (x : BB84Bit) : QMatrix :=
  if b = 0 then (if x = 0 then !![1,0;0,0] else !![0,0;0,1])
  else if x = 0 then !![1/2,1/2;1/2,1/2] else !![1/2,-1/2;-1/2,1/2]

theorem projector_exact (b : BB84Basis) (x : BB84Bit) : P b x = projectorTable b x := by
  ext i j : 2
  fin_cases b <;> fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [P, ket, projectorTable, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, map_ofNat] <;> ring_nf <;> norm_num

theorem ket_normalized (b : BB84Basis) (x : BB84Bit) :
    (ket b x).conjTranspose * ket b x = 1 := by
  ext i j : 2
  fin_cases i; fin_cases j
  fin_cases b <;> fin_cases x <;>
    norm_num [ket, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
      map_ofNat] <;> ring_nf <;> norm_num

theorem projector_positive (b : BB84Basis) (x : BB84Bit) : (P b x).PosSemidef :=
  Matrix.posSemidef_self_mul_conjTranspose _

theorem projector_hermitian (b : BB84Basis) (x : BB84Bit) : (P b x).conjTranspose = P b x :=
  (projector_positive b x).isHermitian.eq

theorem projector_orthogonal (b : BB84Basis) (x y : BB84Bit) :
    P b x * P b y = if x = y then P b x else 0 := by
  ext i j : 2
  fin_cases b <;> fin_cases x <;> fin_cases y <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector_exact, projectorTable, Matrix.mul_apply, Fin.sum_univ_two]

theorem projector_complete (b : BB84Basis) : P b 0 + P b 1 = 1 := by
  fin_cases b <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector_exact, projectorTable]

/-- Born's rule is the interpretation of a projector measurement. -/
def born (b : BB84Basis) (y : BB84Bit) (ρ : QMatrix) : ℝ := ((P b y * ρ).trace).re

def transition (a b : BB84Basis) (x y : BB84Bit) : ℝ := born b y (P a x)

theorem transition_exact (a b : BB84Basis) (x y : BB84Bit) :
    transition a b x y = if a = b then (if x = y then 1 else 0) else 1/2 := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [transition, born, projector_exact, projectorTable, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem born_rule_same_basis (b : BB84Basis) (x y : BB84Bit) :
    transition b b x y = if x = y then 1 else 0 := by simp [transition_exact]
theorem born_rule_diff_basis (a b : BB84Basis) (h : a ≠ b) (x y : BB84Bit) :
    transition a b x y = 1/2 := by simp [transition_exact, h]
theorem transition_nonneg (a b : BB84Basis) (x y : BB84Bit) : 0 ≤ transition a b x y := by
  rw [transition_exact]; split_ifs <;> norm_num
theorem transition_normalized (a b : BB84Basis) (x : BB84Bit) : ∑ y, transition a b x y = 1 := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> norm_num [transition_exact, Fin.sum_univ_two]

/-- Uniform choice of two complete measurements: the prefactor is 1/2, not 1/4. -/
def E_IR (ρ : QMatrix) : QMatrix := (1/2 : ℂ) •
  (P 0 0 * ρ * P 0 0 + P 0 1 * ρ * P 0 1 + P 1 0 * ρ * P 1 0 + P 1 1 * ρ * P 1 1)

theorem intercept_channel_exact (ρ : QMatrix) : E_IR ρ =
    !![(3*ρ 0 0 + ρ 1 1)/4, (ρ 0 1 + ρ 1 0)/4;
       (ρ 0 1 + ρ 1 0)/4, (ρ 0 0 + 3*ρ 1 1)/4] := by
  ext i j : 2
  fin_cases i <;> fin_cases j <;>
    norm_num [E_IR, projector_exact, projectorTable, Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;> ring

theorem intercept_channel_trace (ρ : QMatrix) : (E_IR ρ).trace = ρ.trace := by
  simp [intercept_channel_exact, Matrix.trace, Fin.sum_univ_two]; ring

/-- Marginalizing the actual outcome of Eve's measurement and re-preparation. -/
def attackedTransition (a b e : BB84Basis) (x y : BB84Bit) : ℝ :=
  ∑ z : BB84Bit, transition a e x z * transition e b z y

theorem measurement_channel_bridge (a b : BB84Basis) (x y : BB84Bit) :
    born b y (E_IR (P a x)) = (∑ e, attackedTransition a b e x y) / 2 := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [born, intercept_channel_exact, projector_exact, projectorTable,
      Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two, attackedTransition, transition_exact]

theorem attacked_same_basis (a e : BB84Basis) (x y : BB84Bit) :
    attackedTransition a a e x y = if e = a then (if x = y then 1 else 0) else 1/2 := by
  fin_cases a <;> fin_cases e <;> fin_cases x <;> fin_cases y <;>
    norm_num [attackedTransition, transition_exact, Fin.sum_univ_two]

/-- Finite real probability weights, with an explicit bridge to Mathlib PMF. -/
structure FiniteLaw (Ω : Type) [Fintype Ω] where
  weight : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ weight ω
  normalized : ∑ ω, weight ω = 1

namespace FiniteLaw
variable {Ω : Type} [Fintype Ω]
def probability (L : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  ∑ ω, if E ω then L.weight ω else 0

def toPMF (L : FiniteLaw Ω) : PMF Ω :=
  PMF.ofFintype (fun ω => ENNReal.ofReal (L.weight ω)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun ω _ => L.nonneg ω), L.normalized]
    simp)

theorem probability_pmf (L : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    ENNReal.ofReal (L.probability E) = ∑ ω, if E ω then L.toPMF ω else 0 := by
  unfold probability
  rw [ENNReal.ofReal_sum_of_nonneg (fun ω _ => by
    split_ifs
    · exact L.nonneg ω
    · rfl)]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : E ω <;> simp [h, toPMF]

theorem probability_complement (L : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] :
    L.probability (fun ω => ¬ E ω) = 1 - L.probability E := by
  have h : L.probability E + L.probability (fun ω => ¬ E ω) = 1 := by
    rw [probability, probability, ← Finset.sum_add_distrib, ← L.normalized]
    apply Finset.sum_congr rfl
    intro ω _; by_cases h : E ω <;> simp [h]
  linarith

/-- Product law: independence is in the construction, not an extra event axiom. -/
def independent (L : FiniteLaw Ω) (m : ℕ) : FiniteLaw (Fin m → Ω) where
  weight ω := ∏ i, L.weight (ω i)
  nonneg ω := Finset.prod_nonneg (fun i _ => L.nonneg (ω i))
  normalized := by rw [← Fintype.sum_pow, L.normalized, one_pow]

theorem independent_all (L : FiniteLaw Ω) (m : ℕ) (E : Ω → Prop) [DecidablePred E] :
    (L.independent m).probability (fun ω => ∀ i, E (ω i)) = (L.probability E)^m := by
  classical
  unfold probability
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro ω _
  change (if ∀ i, E (ω i) then ∏ i, L.weight (ω i) else 0) =
    ∏ i, if E (ω i) then L.weight (ω i) else 0
  by_cases h : ∀ i, E (ω i)
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [if_neg h]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
end FiniteLaw

/-- (Alice bit, Alice basis, Bob basis, Eve basis, Eve result, Bob result). -/
abbrev Round := BB84Bit × BB84Basis × BB84Basis × BB84Basis × BB84Bit × BB84Bit

def honestWeight (ω : Round) : ℝ :=
  (1/16) * (if ω.2.2.2.2.1 = 0 then 1 else 0) *
    transition ω.2.1 ω.2.2.1 ω.1 ω.2.2.2.2.2

def attackWeight (ω : Round) : ℝ := (1/16) *
  transition ω.2.1 ω.2.2.2.1 ω.1 ω.2.2.2.2.1 *
    transition ω.2.2.2.1 ω.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2

def Sifted (ω : Round) : Prop := ω.2.1 = ω.2.2.1
def Error (ω : Round) : Prop := ω.1 ≠ ω.2.2.2.2.2
instance : DecidablePred Sifted := fun _ => inferInstanceAs (Decidable (_ = _))
instance : DecidablePred Error := fun _ => inferInstanceAs (Decidable (_ ≠ _))

lemma honest_nonneg (ω : Round) : 0 ≤ honestWeight ω := by
  unfold honestWeight
  apply mul_nonneg
  · positivity
  · exact transition_nonneg _ _ _ _
lemma attack_nonneg (ω : Round) : 0 ≤ attackWeight ω := by
  unfold attackWeight
  exact mul_nonneg (mul_nonneg (by norm_num) (transition_nonneg _ _ _ _))
    (transition_nonneg _ _ _ _)

lemma honest_normalized : ∑ ω, honestWeight ω = 1 := by
  norm_num [honestWeight, transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]
lemma attack_normalized : ∑ ω, attackWeight ω = 1 := by
  norm_num [attackWeight, transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

def honestLaw : FiniteLaw Round := ⟨honestWeight, honest_nonneg, honest_normalized⟩
def attackLaw : FiniteLaw Round := ⟨attackWeight, attack_nonneg, attack_normalized⟩

/-- The four choices are independent uniform bits: each joint prior has mass 1/16. -/
theorem attack_prior_uniform (a : BB84Bit) (A B E : BB84Basis) :
    (∑ e : BB84Bit, ∑ y : BB84Bit, attackWeight (a,A,B,E,e,y)) = 1/16 := by
  fin_cases a <;> fin_cases A <;> fin_cases B <;> fin_cases E <;>
    norm_num [attackWeight, transition_exact, Fin.sum_univ_two]

/-- Explicit equality of the optical-channel Born probability and the experiment marginal. -/
theorem round_channel_bridge (a : BB84Bit) (A B : BB84Basis) (y : BB84Bit) :
    (∑ E : BB84Basis, ∑ e : BB84Bit, attackWeight (a,A,B,E,e,y)) =
      (1/8) * born B y (E_IR (P A a)) := by
  rw [measurement_channel_bridge]
  simp only [attackWeight, attackedTransition]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem sifting_probability_half : attackLaw.probability Sifted = 1/2 := by
  norm_num [FiniteLaw.probability, attackLaw, attackWeight, Sifted,
    transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem honest_sifting_probability_half : honestLaw.probability Sifted = 1/2 := by
  norm_num [FiniteLaw.probability, honestLaw, honestWeight, Sifted,
    transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem intercept_resend_joint_error_sifting :
    attackLaw.probability (fun ω => Error ω ∧ Sifted ω) = 1/8 := by
  norm_num [FiniteLaw.probability, attackLaw, attackWeight, Sifted, Error,
    transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem honest_joint_error_sifting :
    honestLaw.probability (fun ω => Error ω ∧ Sifted ω) = 0 := by
  norm_num [FiniteLaw.probability, honestLaw, honestWeight, Sifted, Error,
    transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Conditional probability: the positive conditioning mass is proved separately. -/
def qber (L : FiniteLaw Round) : ℝ :=
  L.probability (fun ω => Error ω ∧ Sifted ω) / L.probability Sifted

theorem intercept_resend_error_exact : qber attackLaw = 1/4 := by
  norm_num [qber, intercept_resend_joint_error_sifting, sifting_probability_half]

/-- The mixing coin is independent of every choice in the round. -/
def partialLaw (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) : FiniteLaw Round where
  weight ω := (1-f) * honestWeight ω + f * attackWeight ω
  nonneg ω := add_nonneg (mul_nonneg (sub_nonneg.mpr hf1) (honest_nonneg ω))
    (mul_nonneg hf (attack_nonneg ω))
  normalized := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      honest_normalized, attack_normalized]
    ring

theorem partial_probability (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (E : Round → Prop) [DecidablePred E] :
    (partialLaw f hf hf1).probability E =
      (1-f) * honestLaw.probability E + f * attackLaw.probability E := by
  unfold FiniteLaw.probability
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ω _; by_cases h : E ω <;> simp [h, partialLaw, honestLaw, attackLaw]

theorem partial_sifting_probability (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    (partialLaw f hf hf1).probability Sifted = 1/2 := by
  rw [partial_probability, honest_sifting_probability_half, sifting_probability_half]; ring

theorem partial_intercept_qber (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1) :
    qber (partialLaw f hf hf1) = f/4 := by
  rw [qber, partial_sifting_probability, partial_probability,
    honest_joint_error_sifting, intercept_resend_joint_error_sifting]
  ring

/-- The full joint experiment conditioned on successful sifting. -/
def siftedLaw : FiniteLaw Round where
  weight ω := if Sifted ω then 2 * attackWeight ω else 0
  nonneg ω := by
    split_ifs
    · exact mul_nonneg (by norm_num) (attack_nonneg ω)
    · rfl
  normalized := by
    have h := sifting_probability_half
    unfold FiniteLaw.probability attackLaw at h
    calc
      _ = 2 * (∑ ω, if Sifted ω then attackWeight ω else 0) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl
        intro ω _; split_ifs <;> ring
      _ = 1 := by rw [h]; norm_num

theorem sifted_is_conditioning (ω : Round) : siftedLaw.weight ω =
    (if Sifted ω then attackLaw.weight ω else 0) / attackLaw.probability Sifted := by
  rw [sifting_probability_half]
  change (if Sifted ω then 2 * attackWeight ω else 0) =
    (if Sifted ω then attackWeight ω else 0) / (1/2)
  by_cases h : Sifted ω
  · simp [h]; ring
  · simp [h]

theorem sifted_error_probability : siftedLaw.probability Error = 1/4 := by
  norm_num [FiniteLaw.probability, siftedLaw, Sifted, Error, attackWeight,
    transition_exact, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem sifted_no_error_probability : siftedLaw.probability (fun ω => ¬ Error ω) = 3/4 := by
  rw [FiniteLaw.probability_complement, sifted_error_probability]; norm_num

def sampleLaw (m : ℕ) : FiniteLaw (Fin m → Round) := siftedLaw.independent m

theorem sample_evasion_probability (m : ℕ) :
    (sampleLaw m).probability (fun ω => ∀ i, ¬ Error (ω i)) = (3/4 : ℝ)^m := by
  exact (siftedLaw.independent_all m (fun ω => ¬ Error ω)).trans
    (by rw [sifted_no_error_probability])

theorem sample_detection_probability (m : ℕ) :
    (sampleLaw m).probability (fun ω => ∃ i, Error (ω i)) = 1 - (3/4 : ℝ)^m := by
  have h := (sampleLaw m).probability_complement (fun ω => ∀ i, ¬ Error (ω i))
  simp only [not_forall, not_not] at h
  rw [h, sample_evasion_probability]

theorem evasion_probability_positive (m : ℕ) :
    0 < (sampleLaw m).probability (fun ω => ∀ i, ¬ Error (ω i)) := by
  rw [sample_evasion_probability]; positivity

theorem bridge_to_quantum_bb84_protocol :
    qber attackLaw = QuantumBB84Protocol.eveErrorProbabilityPerBit := by
  rw [intercept_resend_error_exact]; rfl

theorem reg_no_intercept : qber (partialLaw 0 (by norm_num) (by norm_num)) = 0 := by
  rw [partial_intercept_qber]; norm_num
theorem reg_full_intercept : qber (partialLaw 1 (by norm_num) (by norm_num)) = 1/4 := by
  rw [partial_intercept_qber]
theorem reg_empty_sample :
    (sampleLaw 0).probability (fun ω => ∃ i, Error (ω i)) = 0 := by
  rw [sample_detection_probability]; norm_num
theorem reg_two_sample :
    (sampleLaw 2).probability (fun ω => ∃ i, Error (ω i)) = 7/16 := by
  rw [sample_detection_probability]; norm_num

/-- A counterexample to deterministic detection on a finite sample. -/
theorem finite_sample_not_certain (m : ℕ) :
    (sampleLaw m).probability (fun ω => ∃ i, Error (ω i)) < 1 := by
  rw [sample_detection_probability]
  have h : (0 : ℝ) < (3/4 : ℝ)^m := by positivity
  linarith

/-- The erroneous quarter-prefactor in the draft would halve the trace. -/
theorem counterexample_quarter_channel :
    ((1/2 : ℂ) • E_IR (P 0 0)).trace = 1/2 ∧ (P 0 0).trace = 1 := by
  norm_num [intercept_channel_exact, projector_exact, projectorTable, Matrix.trace,
    Fin.sum_univ_two]

theorem intercept_channel_positive (ρ : QMatrix) (hρ : ρ.PosSemidef) :
    (E_IR ρ).PosSemidef := by
  have h (b : BB84Basis) (x : BB84Bit) : (P b x * ρ * P b x).PosSemidef := by
    simpa only [projector_hermitian] using hρ.mul_mul_conjTranspose_same (P b x)
  exact (((h 0 0).add (h 0 1)).add (h 1 0) |>.add (h 1 1)).smul
    (by norm_num [Complex.nonneg_iff] : (0:ℂ) ≤ 1/2)

theorem born_trace_exact (a b : BB84Basis) (x y : BB84Bit) :
    (P b y * P a x).trace = (transition a b x y : ℂ) := by
  fin_cases a <;> fin_cases b <;> fin_cases x <;> fin_cases y <;>
    norm_num [transition_exact, projector_exact, projectorTable, Matrix.trace,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem mutually_unbiased (x y : BB84Bit) : (P 0 x * P 1 y).trace = 1/2 := by
  rw [born_trace_exact]; norm_num [transition_exact]

/-- Rank-one projective measurement is exactly measurement followed by re-preparation. -/
theorem measure_prepare_exact (ρ : QMatrix) (b : BB84Basis) (x : BB84Bit) :
    P b x * ρ * P b x = (P b x * ρ).trace • P b x := by
  ext i j : 2
  fin_cases b <;> fin_cases x <;> fin_cases i <;> fin_cases j <;>
    norm_num [projector_exact, projectorTable, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.trace, Fin.sum_univ_two] <;> ring

theorem born_nonneg (ρ : QMatrix) (hρ : ρ.PosSemidef) (b : BB84Basis) (x : BB84Bit) :
    0 ≤ born b x ρ := by
  have hp : (P b x * ρ * P b x).PosSemidef := by
    simpa only [projector_hermitian] using hρ.mul_mul_conjTranspose_same (P b x)
  have ht : (P b x * ρ * P b x).trace = (P b x * ρ).trace := by
    rw [Matrix.trace_mul_cycle, projector_orthogonal]
    simp
  have hn := (Complex.nonneg_iff.mp hp.trace_nonneg).1
  rw [ht] at hn
  exact hn

/-- For physical inputs the complex Born trace is real, so taking re loses nothing. -/
theorem born_complex_eq (ρ : QMatrix) (hρ : ρ.PosSemidef) (b : BB84Basis) (x : BB84Bit) :
    (born b x ρ : ℂ) = (P b x * ρ).trace := by
  have hp : (P b x * ρ * P b x).PosSemidef := by
    simpa only [projector_hermitian] using hρ.mul_mul_conjTranspose_same (P b x)
  have ht : (P b x * ρ * P b x).trace = (P b x * ρ).trace := by
    rw [Matrix.trace_mul_cycle, projector_orthogonal]
    simp
  have hi := (Complex.nonneg_iff.mp hp.trace_nonneg).2
  rw [ht] at hi
  apply Complex.ext
  · rfl
  · exact hi

theorem born_normalized (ρ : QMatrix) (ht : ρ.trace = 1) (b : BB84Basis) :
    ∑ x : BB84Bit, born b x ρ = 1 := by
  simp only [Fin.sum_univ_two, born, ← Complex.add_re, ← Matrix.trace_add,
    ← Matrix.add_mul, projector_complete, one_mul, ht, Complex.one_re]

/-- The full detector law for any density operator, not only BB84 preparations. -/
def measurementLaw (ρ : QMatrix) (hρ : ρ.PosSemidef) (ht : ρ.trace = 1)
    (b : BB84Basis) : FiniteLaw BB84Bit :=
  ⟨fun x => born b x ρ, born_nonneg ρ hρ b, born_normalized ρ ht b⟩

def partialChannel (f : ℝ) (ρ : QMatrix) : QMatrix :=
  ((1-f : ℝ) : ℂ) • ρ + (f : ℂ) • E_IR ρ

theorem partial_channel_trace (f : ℝ) (ρ : QMatrix) : (partialChannel f ρ).trace = ρ.trace := by
  simp [partialChannel, Matrix.trace_add, Matrix.trace_smul, intercept_channel_trace]
  ring

theorem partial_channel_positive (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (ρ : QMatrix) (hρ : ρ.PosSemidef) : (partialChannel f ρ).PosSemidef := by
  exact (hρ.smul (by exact_mod_cast sub_nonneg.mpr hf1 : (0:ℂ) ≤ ((1-f:ℝ):ℂ))).add
    ((intercept_channel_positive ρ hρ).smul (by exact_mod_cast hf : (0:ℂ) ≤ (f:ℂ)))

theorem partial_channel_born (f : ℝ) (ρ : QMatrix) (b : BB84Basis) (y : BB84Bit) :
    born b y (partialChannel f ρ) = (1-f) * born b y ρ + f * born b y (E_IR ρ) := by
  simp [born, partialChannel, Matrix.mul_add, Matrix.trace_add,
    Matrix.trace_smul, Complex.mul_re]

lemma born_prepared (a b : BB84Basis) (x y : BB84Bit) :
    born b y (P a x) = transition a b x y := rfl

/-- Marginal of the independent mixing experiment agrees with the partial optical channel. -/
theorem partial_round_channel_bridge (f : ℝ) (hf : 0 ≤ f) (hf1 : f ≤ 1)
    (a : BB84Bit) (A B : BB84Basis) (y : BB84Bit) :
    (∑ E : BB84Basis, ∑ e : BB84Bit, (partialLaw f hf hf1).weight (a,A,B,E,e,y)) =
      (1/8) * born B y (partialChannel f (P A a)) := by
  rw [partial_channel_born, measurement_channel_bridge]
  fin_cases a <;> fin_cases A <;> fin_cases B <;> fin_cases y <;>
    norm_num [partialLaw, honestWeight, attackWeight, attackedTransition, born_prepared,
      transition_exact, Fin.sum_univ_two] <;> ring

structure QuantumBB84ProtocolQBERSuite : Prop where
  normalized_kets : ∀ b x, (ket b x).conjTranspose * ket b x = 1
  positive_projectors : ∀ b x, (P b x).PosSemidef
  orthogonal_projectors : ∀ b x y, P b x * P b y = if x = y then P b x else 0
  complete_projectors : ∀ b, P b 0 + P b 1 = 1
  born_table : ∀ a b x y,
    transition a b x y = if a = b then (if x = y then 1 else 0) else 1/2
  real_born_trace : ∀ ρ : QMatrix, ρ.PosSemidef → ∀ b x,
    (born b x ρ : ℂ) = (P b x * ρ).trace
  born_normalization : ∀ ρ : QMatrix, ρ.trace = 1 → ∀ b, ∑ x, born b x ρ = 1
  measure_prepare : ∀ ρ b x, P b x * ρ * P b x = (P b x * ρ).trace • P b x
  channel_trace : ∀ ρ, (E_IR ρ).trace = ρ.trace
  channel_positive : ∀ ρ : QMatrix, ρ.PosSemidef → (E_IR ρ).PosSemidef
  uniform_prior : ∀ a A B E, (∑ e, ∑ y, attackWeight (a,A,B,E,e,y)) = 1/16
  channel_bridge : ∀ a A B y, (∑ E, ∑ e, attackWeight (a,A,B,E,e,y)) =
    (1/8) * born B y (E_IR (P A a))
  sifting : attackLaw.probability Sifted = 1/2
  joint_error : attackLaw.probability (fun ω => Error ω ∧ Sifted ω) = 1/8
  conditional_error : qber attackLaw = 1/4
  partial_error : ∀ f hf hf1, qber (partialLaw f hf hf1) = f/4
  conditional_law : ∀ ω, siftedLaw.weight ω =
    (if Sifted ω then attackLaw.weight ω else 0) / attackLaw.probability Sifted
  detection : ∀ m, (sampleLaw m).probability (fun ω => ∃ i, Error (ω i)) = 1-(3/4:ℝ)^m
  evasion : ∀ m, 0 < (sampleLaw m).probability (fun ω => ∀ i, ¬ Error (ω i))
  old_bridge : qber attackLaw = QuantumBB84Protocol.eveErrorProbabilityPerBit
  two_rounds : (sampleLaw 2).probability (fun ω => ∃ i, Error (ω i)) = 7/16

theorem quantum_bb84_protocol_qber_master_suite : QuantumBB84ProtocolQBERSuite where
  normalized_kets := ket_normalized
  positive_projectors := projector_positive
  orthogonal_projectors := projector_orthogonal
  complete_projectors := projector_complete
  born_table := transition_exact
  real_born_trace := born_complex_eq
  born_normalization := born_normalized
  measure_prepare := measure_prepare_exact
  channel_trace := intercept_channel_trace
  channel_positive := intercept_channel_positive
  uniform_prior := attack_prior_uniform
  channel_bridge := round_channel_bridge
  sifting := sifting_probability_half
  joint_error := intercept_resend_joint_error_sifting
  conditional_error := intercept_resend_error_exact
  partial_error := partial_intercept_qber
  conditional_law := sifted_is_conditioning
  detection := sample_detection_probability
  evasion := evasion_probability_positive
  old_bridge := bridge_to_quantum_bb84_protocol
  two_rounds := reg_two_sample

end QuantumBB84ProtocolQBER
