/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumE91ProtocolBellCHSH
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Qubit depolarization with total nonidentity Pauli probability p.
The physical parameter interval is [0,1]. No channel capacity or key security claim. -/
noncomputable section
open scoped BigOperators ComplexOrder Kronecker
namespace QuantumDepolarizingChannel
open QuantumE91ProtocolBellCHSH
abbrev Q := Matrix (Fin 2) (Fin 2) ℂ
abbrev PairQ := Matrix (Fin 4) (Fin 4) ℂ
abbrev BlochVector := EuclideanSpace ℝ (Fin 3)

def PauliX : Q := QuantumE91ProtocolBellCHSH.PauliX
def PauliY : Q := !![0,-Complex.I;Complex.I,0]
def PauliZ : Q := QuantumE91ProtocolBellCHSH.PauliZ
def pauli (j : Fin 4) : Q := ![1,PauliX,PauliY,PauliZ] j
def amplitude (p : ℝ) (j : Fin 4) : ℝ :=
  if j=0 then Real.sqrt (1-p) else Real.sqrt (p/3)
def K (p : ℝ) (j : Fin 4) : Q := (amplitude p j : ℂ) • pauli j
def Physical (p : ℝ) : Prop := 0 ≤ p ∧ p ≤ 1
def shrink (p : ℝ) : ℝ := 1-4*p/3

theorem pauli_hermitian (j : Fin 4) : (pauli j).conjTranspose = pauli j := by
  fin_cases j <;> ext a b : 2 <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,PauliX,PauliY,PauliZ,
      QuantumE91ProtocolBellCHSH.PauliX,QuantumE91ProtocolBellCHSH.PauliZ,
      Matrix.conjTranspose_apply]

theorem pauli_square (j : Fin 4) : pauli j * pauli j = 1 := by
  fin_cases j <;> ext a b : 2 <;> fin_cases a <;> fin_cases b <;>
    norm_num [pauli,PauliX,PauliY,PauliZ,
      QuantumE91ProtocolBellCHSH.PauliX,QuantumE91ProtocolBellCHSH.PauliZ,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem amplitude_sq (p : ℝ) (hp : Physical p) (j : Fin 4) :
    (amplitude p j : ℂ)^2 = if j=0 then (1-p:ℝ) else (p/3:ℝ) := by
  unfold amplitude
  split_ifs <;> rw [← Complex.ofReal_pow,Real.sq_sqrt] <;> linarith [hp.1,hp.2]

theorem kraus_hermitian (p : ℝ) (j : Fin 4) : (K p j).conjTranspose = K p j := by
  simp [K,Matrix.conjTranspose_smul,pauli_hermitian]

theorem kraus_completeness (p : ℝ) (hp : Physical p) :
    ∑ j : Fin 4, (K p j).conjTranspose * K p j = 1 := by
  have h (j : Fin 4) : (K p j).conjTranspose * K p j =
      (if j=0 then ((1-p:ℝ):ℂ) else ((p/3:ℝ):ℂ)) • (1:Q) := by
    rw [kraus_hermitian]
    simp only [K,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
    rw [← pow_two,amplitude_sq p hp,pauli_square]
    split_ifs <;> rfl
  simp only [h]
  norm_num [Fin.sum_univ_succ,← add_smul]
  ext a b : 2; fin_cases a <;> fin_cases b <;> norm_num [Matrix.ofNat_apply]

def depolarizingChannel (p : ℝ) (M : Q) : Q :=
  ∑ j : Fin 4, K p j * M * (K p j).conjTranspose

theorem kraus_branch (p : ℝ) (hp : Physical p) (j : Fin 4) (M : Q) :
    K p j * M * (K p j).conjTranspose =
      (if j=0 then ((1-p:ℝ):ℂ) else ((p/3:ℝ):ℂ)) • (pauli j * M * pauli j) := by
  simp only [kraus_hermitian]
  simp only [K,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two,
    amplitude_sq p hp]
  split_ifs <;> rfl

theorem weighted_pauli (p : ℝ) (hp : Physical p) (M : Q) :
    depolarizingChannel p M = ((1-p:ℝ):ℂ) • M + ((p/3:ℝ):ℂ) •
      (PauliX*M*PauliX + PauliY*M*PauliY + PauliZ*M*PauliZ) := by
  simp [depolarizingChannel,kraus_branch p hp,Fin.sum_univ_succ,pauli,smul_add]
  abel

theorem depolarizing_exact (p : ℝ) (hp : Physical p) (M : Q) :
    depolarizingChannel p M = (shrink p:ℂ) • M + ((2*p/3:ℝ):ℂ) • (M.trace • (1:Q)) := by
  rw [weighted_pauli p hp]
  ext a b : 2; fin_cases a <;> fin_cases b <;>
    norm_num [PauliX,PauliY,PauliZ,
      QuantumE91ProtocolBellCHSH.PauliX,QuantumE91ProtocolBellCHSH.PauliZ,
      Matrix.mul_apply,Matrix.trace,
      Fin.sum_univ_two,Matrix.vecMul,Matrix.vecHead,Matrix.vecTail,dotProduct,shrink] <;>
    ring_nf <;> norm_num <;> ring

theorem trace_preserving (p : ℝ) (hp : Physical p) (M : Q) :
    (depolarizingChannel p M).trace = M.trace := by
  rw [depolarizing_exact p hp]
  simp [Matrix.trace_add,Matrix.trace_smul,shrink]
  ring

theorem channel_add (p : ℝ) (hp : Physical p) (M N : Q) :
    depolarizingChannel p (M+N) = depolarizingChannel p M + depolarizingChannel p N := by
  simp [depolarizing_exact p hp,Matrix.trace_add,smul_add,add_smul]; abel

theorem channel_smul (p : ℝ) (hp : Physical p) (a : ℂ) (M : Q) :
    depolarizingChannel p (a • M) = a • depolarizingChannel p M := by
  ext i j : 2
  simp [depolarizing_exact p hp,Matrix.trace_smul,smul_smul]
  ring

/-- Matrix-block definition of id_d tensor D_p, independent of the lifted Kraus sum. -/
def extension (d : ℕ) (p : ℝ)
    (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ := fun a b =>
  depolarizingChannel p (Matrix.of fun i j => R (a.1,i) (b.1,j)) a.2 b.2

theorem extension_kraus (d : ℕ) (p : ℝ)
    (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    extension d p R = ∑ j : Fin 4,
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ K p j) * R *
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ K p j).conjTranspose := by
  ext a b : 2
  simp [extension,depolarizingChannel,Matrix.sum_apply,Matrix.mul_apply,
    Matrix.conjTranspose_apply,Fintype.sum_prod_type,Matrix.one_apply,
    apply_ite (starRingEnd ℂ),mul_ite,Finset.sum_add_distrib]

theorem completely_positive (d : ℕ) (p : ℝ)
    (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) (hR : R.PosSemidef) :
    (extension d p R).PosSemidef := by
  rw [extension_kraus]
  exact Matrix.posSemidef_sum _ fun j _ => hR.mul_mul_conjTranspose_same _

theorem positive (p : ℝ) (M : Q) (hM : M.PosSemidef) :
    (depolarizingChannel p M).PosSemidef :=
  Matrix.posSemidef_sum _ fun _ _ => hM.mul_mul_conjTranspose_same _

theorem density_preserved (p : ℝ) (hp : Physical p) (ρ : Q)
    (hρ : ρ.PosSemidef ∧ ρ.trace = 1) :
    (depolarizingChannel p ρ).PosSemidef ∧ (depolarizingChannel p ρ).trace=1 :=
  ⟨positive p ρ hρ.1, (trace_preserving p hp ρ).trans hρ.2⟩

def bloch (r : BlochVector) : Q := (1/2:ℂ) •
  (1+(r 0:ℂ) • PauliX+(r 1:ℂ) • PauliY+(r 2:ℂ) • PauliZ)

theorem bloch_trace (r : BlochVector) : (bloch r).trace=1 := by
  norm_num [bloch,PauliX,PauliY,PauliZ,
      QuantumE91ProtocolBellCHSH.PauliX,QuantumE91ProtocolBellCHSH.PauliZ,
      Matrix.trace,Fin.sum_univ_two]
  ring

theorem bloch_action_exact (p : ℝ) (hp : Physical p) (r : BlochVector) :
    depolarizingChannel p (bloch r) = bloch (shrink p • r) := by
  rw [depolarizing_exact p hp,bloch_trace]
  ext a b : 2; fin_cases a <;> fin_cases b <;>
    norm_num [bloch,PauliX,PauliY,PauliZ,
      QuantumE91ProtocolBellCHSH.PauliX,QuantumE91ProtocolBellCHSH.PauliZ,shrink] <;> ring

theorem bloch_length (p : ℝ) (r : BlochVector) :
    ‖shrink p • r‖ = |shrink p| * ‖r‖ := by rw [norm_smul,Real.norm_eq_abs]

theorem complete_depolarization (M : Q) :
    depolarizingChannel (3/4) M = (M.trace/2) • (1:Q) := by
  rw [depolarizing_exact _ (by constructor <;> norm_num)]
  norm_num [shrink,smul_smul,div_eq_mul_inv,mul_comm]

def composeParameter (p q : ℝ) : ℝ := p+q-4*p*q/3

theorem composition_physical (p q : ℝ) (hp : Physical p) (hq : Physical q) :
    Physical (composeParameter p q) := by
  unfold Physical composeParameter
  have h1 := mul_nonneg hp.1 (sub_nonneg.mpr hq.2)
  have h2 := mul_nonneg hq.1 (sub_nonneg.mpr hp.2)
  have h3 := mul_nonneg hp.1 hq.1
  have h4 := mul_nonneg (sub_nonneg.mpr hp.2) (sub_nonneg.mpr hq.2)
  constructor <;> nlinarith

theorem shrink_composition (p q : ℝ) :
    shrink (composeParameter p q) = shrink p * shrink q := by
  unfold shrink composeParameter; ring

theorem channel_composition (p q : ℝ) (hp : Physical p) (hq : Physical q) (M : Q) :
    depolarizingChannel p (depolarizingChannel q M) =
      depolarizingChannel (composeParameter p q) M := by
  rw [depolarizing_exact p hp,trace_preserving q hq,depolarizing_exact q hq,
    depolarizing_exact _ (composition_physical p q hp hq)]
  ext a b : 2
  simp [shrink,composeParameter,smul_add,smul_smul]
  ring


def pairIndex (a : Fin 2 × Fin 2) : Fin 4 := ⟨2*a.1.val+a.2.val, by omega⟩
def splitIndex (a : Fin 4) : Fin 2 × Fin 2 :=
  (⟨a.val/2,by omega⟩,⟨a.val%2,by omega⟩)
def singletInput : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  rho_minus.submatrix pairIndex pairIndex
def noisySinglet (p : ℝ) : PairQ :=
  (extension 2 p singletInput).submatrix splitIndex splitIndex

theorem singlet_depolarization_exact (p : ℝ) (hp : Physical p) :
    noisySinglet p = (shrink p:ℂ) • rho_minus +
      (((1-shrink p)/4:ℝ):ℂ) • (1:PairQ) := by
  ext a b : 2
  change depolarizingChannel p
    (Matrix.of fun i j => singletInput ((splitIndex a).1,i) ((splitIndex b).1,j))
      (splitIndex a).2 (splitIndex b).2 = _
  rw [depolarizing_exact p hp]
  fin_cases a <;> fin_cases b <;>
    norm_num [singletInput,pairIndex,splitIndex,Matrix.submatrix_apply,
      rho_exact,Matrix.trace,Matrix.of_apply,Fin.sum_univ_two,shrink] <;> ring

theorem singlet_positive (p : ℝ) : (noisySinglet p).PosSemidef :=
  (completely_positive 2 p singletInput (singlet_density.1.submatrix pairIndex)).submatrix
    splitIndex

theorem singlet_trace (p : ℝ) (hp : Physical p) : (noisySinglet p).trace=1 := by
  rw [singlet_depolarization_exact p hp]
  simp [Matrix.trace_add,Matrix.trace_smul,singlet_density.2]

theorem chsh_linear (a b : ℝ) (R T : PairQ) :
    S ((a:ℂ) • R+(b:ℂ) • T) = a*S R+b*S T := by
  simp [S,Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul]
  ring

theorem chsh_identity : S (1:PairQ)=0 := by
  norm_num [S,tensor,A,B,obs,ax,az,bx,bz,
    Matrix.trace,Fin.sum_univ_succ]

theorem chsh_damping (p : ℝ) (hp : Physical p) :
    S (noisySinglet p) = -2*Real.sqrt 2*shrink p ∧
    |S (noisySinglet p)| = 2*Real.sqrt 2*|shrink p| := by
  rw [singlet_depolarization_exact p hp,chsh_linear,chsh_quantum_exact,chsh_identity]
  constructor
  · ring
  · simp [abs_mul,abs_of_nonneg (Real.sqrt_nonneg (2:ℝ))]; ring

def noisyProbability (p : ℝ) (i j : Setting) (a b : Outcome) : ℝ :=
  ((tensor (proj (A i) (sign a)) (proj (B j) (sign b)) *
    noisySinglet p).trace).re

theorem identity_born_trace (x z u v a b : ℝ) :
    (tensor (proj (obs x z) a) (proj (obs u v) b)).trace = 1 := by
  norm_num [tensor,proj,obs,Matrix.trace,Fin.sum_univ_succ]
  ring

theorem noisy_probability_exact (p : ℝ) (hp : Physical p)
    (i j : Setting) (a b : Outcome) :
    noisyProbability p i j a b = shrink p*probability i j a b+(1-shrink p)/4 := by
  unfold noisyProbability
  rw [singlet_depolarization_exact p hp]
  simp [Matrix.mul_add,Matrix.trace_add,Matrix.trace_smul,
    probability,A,
    B,identity_born_trace]

theorem e91_correlator_damping (p : ℝ) (hp : Physical p) (i j : Setting) :
    (∑ a,∑ b,sign a*sign b*noisyProbability p i j a b) =
      shrink p*correlator i j := by
  simp [noisy_probability_exact p hp,correlator,sign,Fin.sum_univ_two]
  ring

def keyQBER (p : ℝ) (i j : Setting) : ℝ := ∑ a,noisyProbability p i j a a

theorem e91_key_qber (p : ℝ) (hp : Physical p) (i j : Setting) (hk : IsKey i j) :
    keyQBER p i j = 2*p/3 := by
  simp [keyQBER,noisy_probability_exact p hp,
    (key_generation_perfect_anticorrelation i j hk).2,shrink]
  ring

theorem noisy_normalized (p : ℝ) (hp : Physical p) (i j : Setting) :
    ∑ a,∑ b,noisyProbability p i j a b = 1 := by
  simp [noisy_probability_exact p hp,probability_exact,sign,Fin.sum_univ_two]
  ring

theorem noisy_nonnegative (p : ℝ) (hp : Physical p) (i j : Setting)
    (a b : Outcome) : 0 ≤ noisyProbability p i j a b := by
  have he := probability_nonneg i j a b
  have hu : probability i j a b ≤ 1/2 := by
    rw [probability_exact]
    fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
      norm_num [corrTable,sign] <;> nlinarith [r_nonneg,r_le_one]
  rw [noisy_probability_exact p hp]
  have hh := mul_nonneg hp.1 he
  have hh' := mul_nonneg (sub_nonneg.mpr hp.2) he
  have hh'' := mul_nonneg hp.1 (sub_nonneg.mpr hu)
  unfold shrink
  nlinarith

def withoutTrace (p : ℝ) (M : Q) : Q :=
  (shrink p:ℂ) • M+((2*p/3:ℝ):ℂ) • ((1/2:ℂ) • (1:Q))

theorem counterexample_nonlinear_without_trace (p : ℝ) (hp : p ≠ 0) :
    withoutTrace p 0 = ((p/3:ℝ):ℂ) • (1:Q) ∧ withoutTrace p 0 ≠ 0 := by
  have hc : ((2*p/3:ℝ):ℂ)*(1/2:ℂ) = ((p/3:ℝ):ℂ) := by push_cast; ring
  have h : withoutTrace p 0 = ((p/3:ℝ):ℂ) • (1:Q) := by
    simp only [withoutTrace,smul_zero,zero_add,smul_smul,hc]
  refine ⟨h,?_⟩
  rw [h]
  intro hz
  have hh := congrArg (fun M : Q => M 0 0) hz
  norm_num at hh
  exact hp hh

theorem identity_channel (M : Q) : depolarizingChannel 0 M = M := by
  rw [depolarizing_exact _ (by constructor <;> norm_num)]; norm_num [shrink]

theorem maximal_error_channel (M : Q) :
    depolarizingChannel 1 M = (-1/3:ℂ) • M+(2/3:ℂ) • (M.trace • (1:Q)) := by
  rw [depolarizing_exact _ (by constructor <;> norm_num)]; norm_num [shrink]

theorem maximally_mixed_fixed (p : ℝ) (hp : Physical p) :
    depolarizingChannel p ((1/2:ℂ) • (1:Q)) = (1/2:ℂ) • (1:Q) := by
  rw [depolarizing_exact p hp]
  ext a b : 2; fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.trace,Fin.sum_univ_two,shrink] <;> ring

theorem pure_state_regressions (p : ℝ) (hp : Physical p) :
    depolarizingChannel p !![1,0;0,0] =
      !![1-2*(p:ℂ)/3,0;0,2*(p:ℂ)/3] ∧
    depolarizingChannel p !![1/2,1/2;1/2,1/2] =
      !![1/2,(shrink p:ℂ)/2;(shrink p:ℂ)/2,1/2] ∧
    depolarizingChannel p !![1/2,-Complex.I/2;Complex.I/2,1/2] =
      !![1/2,-Complex.I*(shrink p:ℂ)/2;Complex.I*(shrink p:ℂ)/2,1/2] := by
  refine ⟨?_,?_,?_⟩ <;> rw [depolarizing_exact p hp] <;>
    ext a b : 2 <;> fin_cases a <;> fin_cases b <;>
    norm_num [Matrix.trace,Fin.sum_univ_two,shrink] <;> ring



theorem extension_trace_preserving (d : ℕ) (p : ℝ) (hp : Physical p)
    (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ) :
    (extension d p R).trace = R.trace := by
  unfold Matrix.trace
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  exact trace_preserving p hp (Matrix.of fun i j => R (a,i) (a,j))

theorem extension_on_tensor (d : ℕ) (p : ℝ) (hp : Physical p)
    (A : Matrix (Fin d) (Fin d) ℂ) (M : Q) :
    extension d p (A ⊗ₖ M) = A ⊗ₖ depolarizingChannel p M := by
  ext a b : 2
  change depolarizingChannel p ((A a.1 b.1) • M) a.2 b.2 =
    A a.1 b.1 * depolarizingChannel p M a.2 b.2
  rw [channel_smul p hp]; rfl

theorem shrink_range (p : ℝ) (hp : Physical p) : -1/3 ≤ shrink p ∧ shrink p ≤ 1 := by
  unfold shrink; constructor <;> linarith [hp.1,hp.2]

theorem shrink_negative (p : ℝ) : shrink p < 0 ↔ 3/4 < p := by
  unfold shrink; constructor <;> intro h <;> linarith

theorem bloch_contraction (p : ℝ) (hp : Physical p) (r : BlochVector) :
    ‖shrink p • r‖ ≤ ‖r‖ := by
  rw [bloch_length]
  have h : |shrink p| ≤ 1 := abs_le.mpr ⟨by linarith [(shrink_range p hp).1],
    (shrink_range p hp).2⟩
  exact mul_le_of_le_one_left (norm_nonneg r) h

theorem normalized_complete_depolarization (ρ : Q) (hρ : ρ.trace = 1) :
    depolarizingChannel (3/4) ρ = (1/2:ℂ) • (1:Q) := by rw [complete_depolarization,hρ]

def noisyOutcomeLaw (p : ℝ) (hp : Physical p) (i j : Setting) :
    QuantumBB84ProtocolQBER.FiniteLaw
      (Outcome × Outcome) where
  weight ab := noisyProbability p i j ab.1 ab.2
  nonneg ab := noisy_nonnegative p hp i j ab.1 ab.2
  normalized := by rw [Fintype.sum_prod_type]; exact noisy_normalized p hp i j

theorem qber_is_corrected_error (p : ℝ) (hp : Physical p)
    (i j : Setting) :
    (noisyOutcomeLaw p hp i j).probability (fun ab =>
      sign ab.1 ≠ -sign ab.2) =
        keyQBER p i j := by
  simp [QuantumBB84ProtocolQBER.FiniteLaw.probability,noisyOutcomeLaw,
    bob_flip_error_iff,Fintype.sum_prod_type,keyQBER]

theorem maximal_error_regression : shrink 1 = -1/3 ∧
    keyQBER 1 1 0 = 2/3 ∧ keyQBER (3/4) 2 1 = 1/2 := by
  refine ⟨by norm_num [shrink],?_,?_⟩
  · simpa using e91_key_qber 1 (by constructor <;> norm_num) 1 0 (by simp [IsKey])
  · rw [e91_key_qber (3/4) (by constructor <;> norm_num) 2 1
      (by simp [IsKey])]; norm_num

structure QuantumDepolarizingChannelSuite : Prop where
  complete : ∀ p, Physical p → ∑ j : Fin 4,(K p j).conjTranspose*K p j = 1
  exact_form : ∀ p, Physical p → ∀ M,
    depolarizingChannel p M = (shrink p:ℂ) • M+((2*p/3:ℝ):ℂ) • (M.trace • (1:Q))
  trace : ∀ p, Physical p → ∀ M,(depolarizingChannel p M).trace=M.trace
  additive : ∀ p, Physical p → ∀ M N,
    depolarizingChannel p (M+N)=depolarizingChannel p M+depolarizingChannel p N
  homogeneous : ∀ p, Physical p → ∀ (a : ℂ) M,
    depolarizingChannel p (a • M)=a • depolarizingChannel p M
  cp : ∀ d p (R : Matrix (Fin d × Fin 2) (Fin d × Fin 2) ℂ),
    R.PosSemidef → (extension d p R).PosSemidef
  extension_trace : ∀ d p, Physical p → ∀ R,(extension d p R).trace=R.trace
  density : ∀ p, Physical p → ∀ ρ, ρ.PosSemidef ∧ ρ.trace = 1 →
    (depolarizingChannel p ρ).PosSemidef ∧ (depolarizingChannel p ρ).trace=1
  bloch_action : ∀ p, Physical p → ∀ r,depolarizingChannel p (bloch r)=bloch (shrink p • r)
  length : ∀ (p : ℝ) (r : BlochVector),‖shrink p • r‖=|shrink p| *‖r‖
  depolarized : ∀ M,depolarizingChannel (3/4) M=(M.trace/2) • (1:Q)
  parameter_closed : ∀ p q,Physical p → Physical q → Physical (composeParameter p q)
  composition : ∀ p q,Physical p → Physical q → ∀ M,
    depolarizingChannel p (depolarizingChannel q M)=depolarizingChannel (composeParameter p q) M
  singlet : ∀ p,Physical p → noisySinglet p=(shrink p:ℂ) • rho_minus+
    (((1-shrink p)/4:ℝ):ℂ) • (1:PairQ)
  singlet_density : ∀ p,Physical p → (noisySinglet p).PosSemidef ∧ (noisySinglet p).trace=1
  chsh : ∀ p,Physical p → S (noisySinglet p)=-2*Real.sqrt 2*shrink p ∧
    |S (noisySinglet p)|=2*Real.sqrt 2*|shrink p|
  probabilities : ∀ p,Physical p → ∀ i j,
    (∀ a b,0 ≤ noisyProbability p i j a b) ∧ (∑ a,∑ b,noisyProbability p i j a b)=1
  qber : ∀ p,Physical p → ∀ i j,IsKey i j → keyQBER p i j=2*p/3
  nonlinear : ∀ p,p ≠ 0 → withoutTrace p 0 ≠ 0
  identity : ∀ M,depolarizingChannel 0 M=M
  endpoint : ∀ M,depolarizingChannel 1 M=(-1/3:ℂ) • M+(2/3:ℂ) • (M.trace • (1:Q))

theorem quantum_depolarizing_channel_master_suite : QuantumDepolarizingChannelSuite := {
  complete := kraus_completeness
  exact_form := depolarizing_exact
  trace := trace_preserving
  additive := channel_add
  homogeneous := channel_smul
  cp := completely_positive
  extension_trace := extension_trace_preserving
  density := density_preserved
  bloch_action := bloch_action_exact
  length := bloch_length
  depolarized := complete_depolarization
  parameter_closed := composition_physical
  composition := channel_composition
  singlet := singlet_depolarization_exact
  singlet_density := fun p hp => ⟨singlet_positive p,singlet_trace p hp⟩
  chsh := chsh_damping
  probabilities := fun p hp i j => ⟨noisy_nonnegative p hp i j,noisy_normalized p hp i j⟩
  qber := e91_key_qber
  nonlinear := fun p hp => (counterexample_nonlinear_without_trace p hp).2
  identity := identity_channel
  endpoint := maximal_error_channel
}

end QuantumDepolarizingChannel
