/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumBellCHSH
import Verification.PhotonicsBellStateAnalyzer
import Verification.QuantumBB84ProtocolQBER
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination

/-! Ideal E91: Born probabilities, classical mixtures and explicit measure/prepare attacks.
Born's rule is a physical modeling postulate, not derived from algebra.
No universal Tsirelson bound, finite-sample security or secrecy theorem is claimed. -/
noncomputable section
open scoped BigOperators ComplexOrder
namespace QuantumE91ProtocolBellCHSH
abbrev Q := Matrix (Fin 2) (Fin 2) ℂ
abbrev PairQ := Matrix (Fin 4) (Fin 4) ℂ
abbrev Setting := Fin 3
abbrev Outcome := Fin 2
@[simp] theorem setting_two_ne_zero : (2:Setting) ≠ 0 := by decide
@[simp] theorem setting_two_ne_one : (2:Setting) ≠ 1 := by decide
@[simp] theorem setting_zero_ne_two : (0:Setting) ≠ 2 := by decide
@[simp] theorem setting_one_ne_two : (1:Setting) ≠ 2 := by decide

def sign (a : Outcome) : ℝ := if a = 0 then 1 else -1
def r : ℝ := Real.sqrt 2 / 2
@[simp] theorem r_sq : r ^ 2 = 1/2 := by
  dsimp [r]; nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
theorem r_nonneg : 0 ≤ r := by unfold r; positivity
theorem r_le_one : r ≤ 1 := by nlinarith [r_sq, r_nonneg]
def c : ℂ := (r : ℂ)
@[simp] theorem c_sq : c ^ 2 = 1/2 := by
  unfold c
  rw [← Complex.ofReal_pow, r_sq]
  norm_num
@[simp] theorem c_star : star c = c := by simp [c]

def PauliX : Q := !![0,1;1,0]
def PauliZ : Q := !![1,0;0,-1]
def obs (x z : ℝ) : Q := !![(z:ℂ),(x:ℂ);(x:ℂ),-(z:ℂ)]
def proj (O : Q) (a : ℝ) : Q := (1/2:ℂ) • (1 + (a:ℂ) • O)
def tensor (A B : Q) : PairQ := fun i j =>
  A ⟨i.val / 2, by omega⟩ ⟨j.val / 2, by omega⟩ *
    B ⟨i.val % 2, by omega⟩ ⟨j.val % 2, by omega⟩
def psi_minus : Matrix (Fin 4) (Fin 1) ℂ := fun i _ => ![0,c,-c,0] i
def rho_minus : PairQ := psi_minus * psi_minus.conjTranspose

theorem rho_exact : rho_minus = !![0,0,0,0;0,1/2,-1/2,0;0,-1/2,1/2,0;0,0,0,0] := by
  ext i j : 2; fin_cases i <;> fin_cases j <;>
    norm_num [rho_minus, psi_minus, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ] <;> ring_nf <;> norm_num

theorem singlet_density : rho_minus.PosSemidef ∧ rho_minus.trace = 1 := by
  refine ⟨Matrix.posSemidef_self_mul_conjTranspose _, ?_⟩
  norm_num [rho_exact, Matrix.trace, Fin.sum_univ_succ]

theorem obs_hermitian (x z : ℝ) : (obs x z).conjTranspose = obs x z := by
  ext i j : 2; fin_cases i <;> fin_cases j <;> simp [obs, Matrix.conjTranspose_apply]

theorem obs_involution (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) : obs x z * obs x z = 1 := by
  have hc : (x:ℂ)^2+(z:ℂ)^2=1 := by exact_mod_cast h
  ext i j : 2; fin_cases i <;> fin_cases j <;>
    norm_num [obs, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (solve | ring) | (solve | linear_combination hc)

theorem projector_complete (O : Q) : proj O 1 + proj O (-1) = 1 := by
  ext i j : 2; simp [proj]; ring

theorem projector_properties (x z a : ℝ) (h : x ^ 2 + z ^ 2 = 1) (ha : a = 1 ∨ a = -1) :
    (proj (obs x z) a).conjTranspose = proj (obs x z) a ∧
    proj (obs x z) a * proj (obs x z) a = proj (obs x z) a := by
  have hc : (x:ℂ)^2+(z:ℂ)^2=1 := by exact_mod_cast h
  constructor
  · ext i j : 2; fin_cases i <;> fin_cases j <;>
      simp [proj, obs, Matrix.conjTranspose_apply] <;> ring
  · rcases ha with rfl | rfl <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
      norm_num [proj, obs, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | (solve | ring) | (solve | linear_combination hc) | (solve | linear_combination hc / 4)

theorem projector_positive (x z a : ℝ) (h : x ^ 2 + z ^ 2 = 1) (ha : a = 1 ∨ a = -1) :
    (proj (obs x z) a).PosSemidef := by
  have hp := Matrix.posSemidef_self_mul_conjTranspose (proj (obs x z) a)
  rw [(projector_properties x z a h ha).1, (projector_properties x z a h ha).2] at hp
  exact hp

def ax (i : Setting) : ℝ := if i=0 then 0 else if i=1 then r else 1
def az (i : Setting) : ℝ := if i=0 then 1 else if i=1 then r else 0
def bx (i : Setting) : ℝ := if i=1 then 1 else r
def bz (i : Setting) : ℝ := if i=0 then r else if i=1 then 0 else -r
def A (i : Setting) := obs (ax i) (az i)
def B (j : Setting) := obs (bx j) (bz j)
theorem directions_unit (i : Setting) : ax i ^ 2 + az i ^ 2 = 1 ∧ bx i ^ 2 + bz i ^ 2 = 1 := by
  fin_cases i <;> norm_num [ax, az, bx, bz, neg_sq]
theorem settings_spec : A 0 = PauliZ ∧ A 1 = (c:ℂ) • (PauliZ+PauliX) ∧ A 2 = PauliX ∧
    B 0 = A 1 ∧ B 1 = A 2 ∧ B 2 = (c:ℂ) • (PauliX-PauliZ) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> ext i j : 2 <;> fin_cases i <;> fin_cases j <;>
    simp [A,B,obs,ax,az,bx,bz,PauliX,PauliZ,c]

/-- The real part is paired below with a theorem that the complex trace is real. -/
def probability (i j : Setting) (a b : Outcome) : ℝ :=
  ((tensor (proj (A i) (sign a)) (proj (B j) (sign b)) * rho_minus).trace).re
def corrTable : Matrix Setting Setting ℝ := fun i j =>
  if i = 0 then (if j = 0 then -r else if j = 1 then 0 else r)
  else if i = 1 then (if j = 0 then -1 else if j = 1 then -r else 0)
  else if j = 1 then -1 else -r

theorem born_trace_general (x z u v a b : ℝ) :
    (tensor (proj (obs x z) a) (proj (obs u v) b) * rho_minus).trace =
      (((1-a*b*(x*u+z*v))/4 : ℝ):ℂ) := by
  norm_num [tensor, proj, obs, rho_exact, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]
  ring

theorem dot_table (i j : Setting) : -(ax i * bx j + az i * bz j) = corrTable i j := by
  fin_cases i <;> fin_cases j <;> norm_num [ax,az,bx,bz,corrTable]; all_goals nlinarith [r_sq]

theorem probability_exact (i j : Setting) (a b : Outcome) :
    probability i j a b = (1 + sign a * sign b * corrTable i j)/4 := by
  unfold probability A B
  rw [born_trace_general]
  simp only [Complex.ofReal_re]
  rw [← dot_table]; ring

theorem probability_nonneg (i j : Setting) (a b : Outcome) : 0 ≤ probability i j a b := by
  rw [probability_exact]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [sign,corrTable] <;> nlinarith [r_nonneg,r_le_one]

theorem probability_normalized (i j : Setting) : ∑ a, ∑ b, probability i j a b = 1 := by
  simp [probability_exact, sign, Fin.sum_univ_two]; ring

theorem uniform_marginals (i j : Setting) (a : Outcome) :
    (∑ b, probability i j a b) = 1/2 ∧ (∑ b, probability i j b a) = 1/2 := by
  fin_cases a <;> norm_num [probability_exact, sign, Fin.sum_univ_two] <;> ring

def correlator (i j : Setting) : ℝ := ∑ a, ∑ b, sign a * sign b * probability i j a b

theorem correlator_table (i j : Setting) : correlator i j = corrTable i j := by
  simp [correlator, probability_exact, sign, Fin.sum_univ_two]; ring

theorem correlator_exact (i j : Setting) :
    (correlator i j : ℂ) = (tensor (A i) (B j) * rho_minus).trace := by
  rw [correlator_table, ← dot_table]
  norm_num [tensor, A,B,obs,rho_exact, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_succ]
  ring

def S (ρ : PairQ) : ℝ := ((tensor (A 0) (B 0) * ρ).trace -
  (tensor (A 0) (B 2) * ρ).trace + (tensor (A 2) (B 0) * ρ).trace +
  (tensor (A 2) (B 2) * ρ).trace).re

theorem chsh_correlation_exact : correlator 0 0 = -r ∧ correlator 0 2 = r ∧
    correlator 2 0 = -r ∧ correlator 2 2 = -r := by
  norm_num [correlator_table,corrTable, Matrix.cons_val]
theorem chsh_quantum_exact : S rho_minus = -2 * Real.sqrt 2 := by
  simp only [S, ← correlator_exact, correlator_table]
  norm_num [corrTable, r, Matrix.cons_val]; ring

theorem chsh_quantum_violation : |S rho_minus| = 2 * Real.sqrt 2 ∧ 2 < |S rho_minus| := by
  rw [chsh_quantum_exact, abs_of_nonpos
    (by nlinarith [Real.sqrt_nonneg (2:ℝ)] : -2*Real.sqrt 2 ≤ 0)]
  constructor
  · ring
  · have h := QuantumBellCHSH.quantum_violates_classical_bound
    dsimp [QuantumBellCHSH.tsirelsonBound] at h; linarith


def IsKey (i j : Setting) : Prop := (i=1 ∧ j=0) ∨ (i=2 ∧ j=1)
def IsTest (i j : Setting) : Prop := (i=0 ∨ i=2) ∧ (j=0 ∨ j=2)
instance (i j : Setting) : Decidable (IsKey i j) := inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))
instance (i j : Setting) : Decidable (IsTest i j) := inferInstanceAs (Decidable ((_ ∨ _) ∧ (_ ∨ _)))

theorem key_generation_perfect_anticorrelation (i j : Setting) (h : IsKey i j) :
    correlator i j = -1 ∧ ∀ a b, probability i j a b = if a = b then 0 else 1/2 := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  all_goals constructor
  all_goals try { norm_num [correlator_table,corrTable] }
  all_goals intro a b; fin_cases a <;> fin_cases b <;> norm_num [probability_exact,corrTable,sign]

def qber (i j : Setting) : ℝ := ∑ a, probability i j a a

theorem key_qber_zero (i j : Setting) (h : IsKey i j) : qber i j = 0 := by
  simp [qber,(key_generation_perfect_anticorrelation i j h).2]

def settingLaw : QuantumBB84ProtocolQBER.FiniteLaw (Setting × Setting) where
  weight _ := 1/9
  nonneg _ := by norm_num
  normalized := by norm_num [Fintype.card_prod]

theorem round_routing_probabilities :
    settingLaw.probability (fun ij => IsKey ij.1 ij.2) = 2/9 ∧
    settingLaw.probability (fun ij => IsTest ij.1 ij.2) = 4/9 ∧
    settingLaw.probability (fun ij => ¬IsKey ij.1 ij.2 ∧ ¬IsTest ij.1 ij.2) = 1/3 := by
  norm_num [QuantumBB84ProtocolQBER.FiniteLaw.probability, settingLaw, IsKey, IsTest,
    Fintype.sum_prod_type, Fin.sum_univ_succ]

def chsh (a c b d : ℝ) := a*b-a*d+c*b+c*d

theorem chsh_interval_bound (a c b d : ℝ) (ha : |a| ≤ 1) (hc : |c| ≤ 1)
    (hb : |b| ≤ 1) (hd : |d| ≤ 1) : |chsh a c b d| ≤ 2 := by
  have hbd : |b-d|+|b+d| ≤ 2 := by
    rcases abs_le.mp hb with ⟨hb0,hb1⟩
    rcases abs_le.mp hd with ⟨hd0,hd1⟩
    rcases le_total 0 (b-d) with h | h <;> rcases le_total 0 (b+d) with k | k
    · rw [abs_of_nonneg h,abs_of_nonneg k]; linarith
    · rw [abs_of_nonneg h,abs_of_nonpos k]; linarith
    · rw [abs_of_nonpos h,abs_of_nonneg k]; linarith
    · rw [abs_of_nonpos h,abs_of_nonpos k]; linarith
  calc
    |chsh a c b d| = |a*(b-d)+c*(b+d)| := by congr 1; unfold chsh; ring
    _ ≤ |a*(b-d)|+|c*(b+d)| := abs_add_le _ _
    _ ≤ |b-d|+|b+d| := by
      rw [abs_mul,abs_mul]
      exact add_le_add (by nlinarith [abs_nonneg (b-d)]) (by nlinarith [abs_nonneg (b+d)])
    _ ≤ 2 := hbd

theorem convex_abs_bound {ι : Type} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ k, 0 ≤ w k) (hs : ∑ k, w k = 1) (hf : ∀ k, |f k| ≤ 2) :
    |∑ k, w k * f k| ≤ 2 := by
  calc
    |∑ k, w k * f k| ≤ ∑ k, |w k * f k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k, w k * 2 := by
      apply Finset.sum_le_sum
      intro k _; rw [abs_mul,abs_of_nonneg (hw k)]
      exact mul_le_mul_of_nonneg_left (hf k) (hw k)
    _ = 2 := by rw [← Finset.sum_mul,hs]; ring

/-- One common law for all settings enforces independence of the hidden variable from settings. -/
theorem lhv_classical_bound {ι : Type} [Fintype ι]
    (L : QuantumBB84ProtocolQBER.FiniteLaw ι) (a c b d : ι → Outcome) :
    |∑ k, L.weight k * chsh (sign (a k)) (sign (c k)) (sign (b k)) (sign (d k))| ≤ 2 := by
  apply convex_abs_bound _ _ L.nonneg L.normalized
  intro k
  apply chsh_interval_bound <;> simp [sign] <;> split_ifs <;> norm_num

/-- Physical one-qubit density operators. -/
def IsDensity (ρ : Q) : Prop := ρ.PosSemidef ∧ ρ.trace = 1

theorem projector_trace (x z a : ℝ) : (proj (obs x z) a).trace = 1 := by
  norm_num [proj,obs,Matrix.trace,Fin.sum_univ_two]; ring

theorem projector_density (x z a : ℝ) (h : x ^ 2 + z ^ 2 = 1) (ha : a = 1 ∨ a = -1) :
    IsDensity (proj (obs x z) a) := ⟨projector_positive x z a h ha,projector_trace x z a⟩

def expectation (O ρ : Q) : ℝ := (O*ρ).trace.re

theorem projector_born_nonneg (x z a : ℝ) (h : x ^ 2 + z ^ 2 = 1) (ha : a = 1 ∨ a = -1)
    (ρ : Q) (hp : ρ.PosSemidef) : 0 ≤ (proj (obs x z) a * ρ).trace.re := by
  obtain ⟨hh,hi⟩ := projector_properties x z a h ha
  have hs := hp.mul_mul_conjTranspose_same (proj (obs x z) a)
  rw [hh] at hs
  have ht : (proj (obs x z) a * ρ * proj (obs x z) a).trace = (proj (obs x z) a * ρ).trace := by
    rw [Matrix.trace_mul_cycle,hi]
  have hn := hs.trace_nonneg
  rw [ht] at hn
  exact (Complex.nonneg_iff.mp hn).1

theorem expectation_bound (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) (ρ : Q) (hρ : IsDensity ρ) :
    |expectation (obs x z) ρ| ≤ 1 := by
  have hp := projector_born_nonneg x z 1 h (Or.inl rfl) ρ hρ.1
  have hm := projector_born_nonneg x z (-1) h (Or.inr rfl) ρ hρ.1
  simp only [proj,Matrix.smul_mul,Matrix.add_mul,Matrix.one_mul,Matrix.trace_smul,
    Matrix.trace_add,hρ.2] at hp hm
  norm_num [Complex.mul_re] at hp hm
  unfold expectation
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem expectation_real (x z : ℝ) (ρ : Q) (hρ : IsDensity ρ) :
    (expectation (obs x z) ρ : ℂ) = (obs x z * ρ).trace := by
  have ht : star (obs x z * ρ).trace = (obs x z * ρ).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,hρ.1.isHermitian.eq,
      obs_hermitian,Matrix.trace_mul_comm]
  apply Complex.ext
  · rfl
  · have := congrArg Complex.im ht
    simp at this
    simp only [Complex.ofReal_im]
    linarith

theorem tensor_trace (U V : Q) : (tensor U V).trace = U.trace * V.trace := by
  norm_num [tensor,Matrix.trace,Fin.sum_univ_succ]; ring

theorem tensor_trace_mul (A B U V : Q) :
    (tensor A B * tensor U V).trace = (A*U).trace * (B*V).trace := by
  norm_num [tensor,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_succ]; ring

theorem S_product (U V : Q) (hU : IsDensity U) (hV : IsDensity V) :
    S (tensor U V) = chsh (expectation (A 0) U) (expectation (A 2) U)
      (expectation (B 0) V) (expectation (B 2) V) := by
  simp only [S,tensor_trace_mul,A,B,← expectation_real _ _ U hU,← expectation_real _ _ V hV]
  simp [chsh]

theorem product_bound (U V : Q) (hU : IsDensity U) (hV : IsDensity V) :
    |S (tensor U V)| ≤ 2 := by
  rw [S_product U V hU hV]
  exact chsh_interval_bound _ _ _ _
    (expectation_bound _ _ (directions_unit 0).1 U hU)
    (expectation_bound _ _ (directions_unit 2).1 U hU)
    (expectation_bound _ _ (directions_unit 0).2 V hV)
    (expectation_bound _ _ (directions_unit 2).2 V hV)

def mixture {ι : Type} [Fintype ι] (w : ι → ℝ) (U V : ι → Q) : PairQ :=
  ∑ k, (w k : ℂ) • tensor (U k) (V k)

theorem S_mixture {ι : Type} [Fintype ι] (w : ι → ℝ) (U V : ι → Q) :
    S (mixture w U V) = ∑ k, w k * S (tensor (U k) (V k)) := by
  simp only [S,mixture,Matrix.mul_sum,Matrix.mul_smul,Matrix.trace_sum,Matrix.trace_smul,
    Complex.sub_re,Complex.add_re,Complex.re_sum]
  rw [← Finset.sum_sub_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _; simp [Complex.mul_re]; ring

theorem separable_state_chsh_bound {ι : Type} [Fintype ι]
    (L : QuantumBB84ProtocolQBER.FiniteLaw ι) (U V : ι → Q)
    (hU : ∀ k, IsDensity (U k)) (hV : ∀ k, IsDensity (V k)) :
    |S (mixture L.weight U V)| ≤ 2 := by
  rw [S_mixture]
  exact convex_abs_bound _ _ L.nonneg L.normalized (fun k => product_bound _ _ (hU k) (hV k))


def flat (a b : Fin 2) : Fin 4 := ⟨2*a.val+b.val,by omega⟩
def partialBob (ρ : PairQ) : Q := fun b d => ∑ a, ρ (flat a b) (flat a d)
def identity : Q := !![1,0;0,1]
theorem identity_eq : identity = 1 := by
  ext i j : 2; fin_cases i <;> fin_cases j <;> norm_num [identity]
def measuredBob (x z : ℝ) (a : Outcome) (ρ : PairQ) : Q :=
  partialBob (tensor (proj (obs x z) (sign a)) identity * ρ *
    (tensor (proj (obs x z) (sign a)) identity).conjTranspose)

/-- The conditional Bob state is derived from a local projective instrument. -/
theorem measured_singlet_exact (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1) (a : Outcome) :
    measuredBob x z a rho_minus = (1/2:ℂ) • proj (obs x z) (-sign a) := by
  have hc : (x:ℂ)^2+(z:ℂ)^2=1 := by exact_mod_cast h
  ext i j : 2
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    norm_num [measuredBob,partialBob,flat,tensor,proj,obs,sign,rho_exact,identity,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, Fin.sum_univ_succ] <;>
    first | (solve | ring) | (solve | linear_combination hc / 8)

/-- Eve discards the measured qubit and prepares tau a, conditioned on her outcome. -/
def interceptResend (x z : ℝ) (tau : Outcome → Q) (ρ : PairQ) : PairQ :=
  ∑ a, tensor (tau a) (measuredBob x z a ρ)

def eveLaw : QuantumBB84ProtocolQBER.FiniteLaw Outcome where
  weight _ := 1/2
  nonneg _ := by norm_num
  normalized := by norm_num [Fin.sum_univ_two]

theorem intercept_resend_forces_separable (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1)
    (tau : Outcome → Q) (ht : ∀ a, IsDensity (tau a)) :
    interceptResend x z tau rho_minus =
      mixture eveLaw.weight tau (fun a => proj (obs x z) (-sign a)) ∧
    (∀ a, IsDensity (proj (obs x z) (-sign a))) ∧
    |S (interceptResend x z tau rho_minus)| ≤ 2 := by
  have he : interceptResend x z tau rho_minus =
      mixture eveLaw.weight tau (fun a => proj (obs x z) (-sign a)) := by
    simp only [interceptResend,measured_singlet_exact x z h,mixture,eveLaw]
    apply Finset.sum_congr rfl
    intro a _; ext i j : 2; simp [tensor]; ring
  have hd (a : Outcome) : IsDensity (proj (obs x z) (-sign a)) := by
    apply projector_density x z _ h
    fin_cases a <;> norm_num [sign]
  refine ⟨he,hd,?_⟩
  rw [he]; exact separable_state_chsh_bound eveLaw tau _ ht hd

theorem mixture_trace_one {ι : Type} [Fintype ι]
    (L : QuantumBB84ProtocolQBER.FiniteLaw ι) (U V : ι → Q)
    (hU : ∀ k, IsDensity (U k)) (hV : ∀ k, IsDensity (V k)) :
    (mixture L.weight U V).trace = 1 := by
  simp only [mixture,Matrix.trace_sum,Matrix.trace_smul,tensor_trace]
  simp only [(hU _).2,(hV _).2,mul_one,smul_eq_mul]
  rw [← Complex.ofReal_sum,L.normalized]; rfl

theorem intercept_trace_one (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1)
    (tau : Outcome → Q) (ht : ∀ a, IsDensity (tau a)) :
    (interceptResend x z tau rho_minus).trace = 1 := by
  obtain ⟨he,hd,_⟩ := intercept_resend_forces_separable x z h tau ht
  rw [he]; exact mixture_trace_one eveLaw tau _ ht hd

/-- Concrete full Z intercept/resend on Alice's half of the singlet. -/
def zAttack : PairQ := interceptResend 0 1 (fun a => proj (obs 0 1) (sign a)) rho_minus

theorem z_attack_exact : zAttack = !![0,0,0,0;0,1/2,0,0;0,0,1/2,0;0,0,0,0] := by
  have h : (0:ℝ)^2+1^2=1 := by norm_num
  simp only [zAttack,interceptResend,measured_singlet_exact 0 1 h,Fin.sum_univ_two]
  ext i j : 2; fin_cases i <;> fin_cases j <;> norm_num [tensor,proj,obs,sign]

theorem z_attack_chsh : S zAttack = -Real.sqrt 2 := by
  norm_num [S,z_attack_exact,tensor,A,B,ax,az,bx,bz,obs,Matrix.mul_apply,Matrix.trace,
    Fin.sum_univ_succ,Matrix.cons_val,r]; ring

theorem bridge_to_quantum_bell_chsh : |S rho_minus| = QuantumBellCHSH.tsirelsonBound :=
  chsh_quantum_violation.1

theorem bridge_to_bell_analyzer :
    (fun i => psi_minus i 0) = PhotonicsBellStateAnalyzer.bellVector .psiMinus := by
  ext i; fin_cases i <;>
    simp [psi_minus,PhotonicsBellStateAnalyzer.bellVector,
      PhotonicsBellStateAnalyzer.rootTwo,c,r]; ring

/-- All nine values, including the three discarded setting pairs. -/
theorem regression_nine_correlators :
    correlator 0 0 = -r ∧ correlator 0 1 = 0 ∧ correlator 0 2 = r ∧
    correlator 1 0 = -1 ∧ correlator 1 1 = -r ∧ correlator 1 2 = 0 ∧
    correlator 2 0 = -r ∧ correlator 2 1 = -1 ∧ correlator 2 2 = -r := by
  norm_num [correlator_table,corrTable]

theorem regression_key_probabilities (i j : Setting) (h : IsKey i j) :
    probability i j 0 1 = 1/2 ∧ probability i j 1 0 = 1/2 ∧ qber i j = 0 := by
  simp [(key_generation_perfect_anticorrelation i j h).2,key_qber_zero i j h]


theorem tensor_positive (U V : Q) (hU : U.PosSemidef) (hV : V.PosSemidef) :
    (tensor U V).PosSemidef :=
  (hU.kronecker hV).submatrix (fun i : Fin 4 =>
    (⟨i.val/2,by omega⟩,⟨i.val%2,by omega⟩))

theorem mixture_positive {ι : Type} [Fintype ι]
    (L : QuantumBB84ProtocolQBER.FiniteLaw ι) (U V : ι → Q)
    (hU : ∀ k, IsDensity (U k)) (hV : ∀ k, IsDensity (V k)) :
    (mixture L.weight U V).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro k _
  exact (tensor_positive _ _ (hU k).1 (hV k).1).smul
    (by exact_mod_cast L.nonneg k : (0:ℂ) ≤ (L.weight k:ℂ))

theorem intercepted_density (x z : ℝ) (h : x ^ 2 + z ^ 2 = 1)
    (tau : Outcome → Q) (ht : ∀ a, IsDensity (tau a)) :
    (interceptResend x z tau rho_minus).PosSemidef ∧
    (interceptResend x z tau rho_minus).trace = 1 := by
  obtain ⟨he,hd,_⟩ := intercept_resend_forces_separable x z h tau ht
  rw [he]
  exact ⟨mixture_positive eveLaw tau _ ht hd,mixture_trace_one eveLaw tau _ ht hd⟩

theorem born_trace_real (i j : Setting) (a b : Outcome) :
    (probability i j a b : ℂ) =
      (tensor (proj (A i) (sign a)) (proj (B j) (sign b)) * rho_minus).trace := by
  unfold probability A B
  rw [born_trace_general]
  simp

def outcomeLaw (i j : Setting) : QuantumBB84ProtocolQBER.FiniteLaw (Outcome × Outcome) where
  weight ab := probability i j ab.1 ab.2
  nonneg ab := probability_nonneg i j ab.1 ab.2
  normalized := by rw [Fintype.sum_prod_type]; exact probability_normalized i j

theorem bob_flip_error_iff (a b : Outcome) : sign a ≠ -sign b ↔ a=b := by
  fin_cases a <;> fin_cases b <;> norm_num [sign]

theorem key_corrected_agreement (i j : Setting) (h : IsKey i j) :
    (outcomeLaw i j).probability (fun ab => sign ab.1 = -sign ab.2) = 1 := by
  norm_num [QuantumBB84ProtocolQBER.FiniteLaw.probability,outcomeLaw,
    (key_generation_perfect_anticorrelation i j h).2,sign,
    Fintype.sum_prod_type,Fin.sum_univ_two]

theorem settings_hermitian_involutive (i : Setting) :
    (A i).conjTranspose = A i ∧ A i*A i=1 ∧
    (B i).conjTranspose = B i ∧ B i*B i=1 :=
  ⟨obs_hermitian _ _,obs_involution _ _ (directions_unit i).1,
   obs_hermitian _ _,obs_involution _ _ (directions_unit i).2⟩

theorem routing_disjoint (i j : Setting) : ¬(IsKey i j ∧ IsTest i j) := by
  fin_cases i <;> fin_cases j <;> norm_num [IsKey,IsTest]

theorem classical_expression_bridge (a c b d : ℝ) :
    chsh a c b d = QuantumBellCHSH.chshExpr a c b (-d) := by
  unfold chsh QuantumBellCHSH.chshExpr; ring

structure QuantumE91ProtocolBellCHSHSuite : Prop where
  density : rho_minus.PosSemidef ∧ rho_minus.trace = 1
  projectors : ∀ x z a, x ^ 2 + z ^ 2 = 1 → (a = 1 ∨ a = -1) →
    (proj (obs x z) a).conjTranspose = proj (obs x z) a ∧
    proj (obs x z) a * proj (obs x z) a = proj (obs x z) a
  complete : ∀ O, proj O 1 + proj O (-1) = 1
  born_nonnegative : ∀ i j a b, 0 ≤ probability i j a b
  born_real : ∀ i j a b, (probability i j a b : ℂ) =
    (tensor (proj (A i) (sign a)) (proj (B j) (sign b)) * rho_minus).trace
  normalized : ∀ i j, ∑ a, ∑ b, probability i j a b = 1
  marginals : ∀ i j a, (∑ b, probability i j a b) = 1/2 ∧ (∑ b, probability i j b a) = 1/2
  correlators : ∀ i j, (correlator i j:ℂ) = (tensor (A i) (B j) * rho_minus).trace
  quantum_value : S rho_minus = -2*Real.sqrt 2
  violation : |S rho_minus| = 2*Real.sqrt 2 ∧ 2 < |S rho_minus|
  key : ∀ i j, IsKey i j → (outcomeLaw i j).probability (fun ab => sign ab.1 = -sign ab.2) = 1
  routing : settingLaw.probability (fun ij => IsKey ij.1 ij.2) = 2/9 ∧
    settingLaw.probability (fun ij => IsTest ij.1 ij.2) = 4/9 ∧
    settingLaw.probability (fun ij => ¬IsKey ij.1 ij.2 ∧ ¬IsTest ij.1 ij.2) = 1/3
  local_bound : ∀ (ι : Type) [Fintype ι] (L : QuantumBB84ProtocolQBER.FiniteLaw ι)
    (a c b d : ι → Outcome),
    |∑ k, L.weight k * chsh (sign (a k)) (sign (c k)) (sign (b k)) (sign (d k))| ≤ 2
  separable_bound : ∀ (ι : Type) [Fintype ι] (L : QuantumBB84ProtocolQBER.FiniteLaw ι)
    (U V : ι → Q), (∀ k, IsDensity (U k)) → (∀ k, IsDensity (V k)) →
    |S (mixture L.weight U V)| ≤ 2
  measured_state : ∀ x z, x ^ 2 + z ^ 2 = 1 → ∀ a,
    measuredBob x z a rho_minus = (1/2:ℂ) • proj (obs x z) (-sign a)
  attack_bound : ∀ x z, x ^ 2 + z ^ 2 = 1 → ∀ tau, (∀ a, IsDensity (tau a)) →
    |S (interceptResend x z tau rho_minus)| ≤ 2
  attack_density : ∀ x z, x ^ 2 + z ^ 2 = 1 → ∀ tau, (∀ a, IsDensity (tau a)) →
    (interceptResend x z tau rho_minus).PosSemidef ∧ (interceptResend x z tau rho_minus).trace=1
  scalar_bridge : |S rho_minus| = QuantumBellCHSH.tsirelsonBound
  z_attack : S zAttack = -Real.sqrt 2

theorem quantum_e91_protocol_bell_chsh_master_suite : QuantumE91ProtocolBellCHSHSuite := {
  density := singlet_density
  projectors := projector_properties
  complete := projector_complete
  born_nonnegative := probability_nonneg
  born_real := born_trace_real
  normalized := probability_normalized
  marginals := uniform_marginals
  correlators := correlator_exact
  quantum_value := chsh_quantum_exact
  violation := chsh_quantum_violation
  key := key_corrected_agreement
  routing := round_routing_probabilities
  local_bound := fun _ _ => lhv_classical_bound
  separable_bound := fun _ _ => separable_state_chsh_bound
  measured_state := measured_singlet_exact
  attack_bound := fun x z h tau ht => (intercept_resend_forces_separable x z h tau ht).2.2
  attack_density := intercepted_density
  scalar_bridge := bridge_to_quantum_bell_chsh
  z_attack := z_attack_chsh
}
end QuantumE91ProtocolBellCHSH
