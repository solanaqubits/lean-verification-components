/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPOVMNaimarkDilation
import Verification.QuantumPOVMInformationallyComplete
import Verification.QuantumPOVMInformationEntropy
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Classical postprocessing of finite POVMs and finite, absolutely continuous KL.
This is not the quantum relative-entropy data processing theorem for CPTP maps.
-/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy
namespace QuantumChannelClassicalDataProcessing

structure ClassicalChannel (m n : ℕ) where
  matrix : Fin n → Fin m → ℝ
  nonneg : ∀ k j, 0 ≤ matrix k j
  col_sum_one : ∀ j, ∑ k, matrix k j = 1

@[ext] theorem channel_ext {m n : ℕ} (M N : ClassicalChannel m n)
    (h : M.matrix = N.matrix) : M = N := by
  cases M; cases N; cases h; rfl

structure BistochasticChannel (m : ℕ) extends ClassicalChannel m m where
  row_sum_one : ∀ k, ∑ j, matrix k j = 1

variable {m n l d : ℕ}

def apply_channel (M : ClassicalChannel m n) (p : Fin m → ℝ) : Fin n → ℝ :=
  fun k => ∑ j, M.matrix k j * p j

theorem apply_nonneg (M : ClassicalChannel m n) {p : Fin m → ℝ}
    (hp : ∀ j, 0 ≤ p j) : ∀ k, 0 ≤ apply_channel M p k :=
  fun k => Finset.sum_nonneg fun j _ => mul_nonneg (M.nonneg k j) (hp j)

theorem apply_sum (M : ClassicalChannel m n) (p : Fin m → ℝ) :
    ∑ k, apply_channel M p k = ∑ j, p j := by
  simp only [apply_channel, Finset.sum_comm, ← Finset.sum_mul, M.col_sum_one, one_mul]

theorem apply_distribution (M : ClassicalChannel m n) {p : Fin m → ℝ}
    (hp : IsDistribution p) : IsDistribution (apply_channel M p) :=
  ⟨apply_nonneg M hp.1, (apply_sum M p).trans hp.2⟩

def identity_channel (m : ℕ) : ClassicalChannel m m where
  matrix k j := if k = j then 1 else 0
  nonneg k j := by split <;> norm_num
  col_sum_one j := by simp

def compose (B : ClassicalChannel n l) (A : ClassicalChannel m n) : ClassicalChannel m l where
  matrix k j := ∑ i, B.matrix k i * A.matrix i j
  nonneg k j := Finset.sum_nonneg fun i _ => mul_nonneg (B.nonneg k i) (A.nonneg i j)
  col_sum_one j := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, B.col_sum_one, one_mul, A.col_sum_one]

theorem apply_identity (p : Fin m → ℝ) : apply_channel (identity_channel m) p = p := by
  funext k
  simp [apply_channel, identity_channel]

theorem apply_compose (B : ClassicalChannel n l) (A : ClassicalChannel m n) (p : Fin m → ℝ) :
    apply_channel (compose B A) p = apply_channel B (apply_channel A p) := by
  funext k
  simp only [apply_channel, compose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

def AbsContinuous {ι : Type*} (p q : ι → ℝ) : Prop := ∀ j, 0 < p j → 0 < q j

theorem abs_continuous_preserved (M : ClassicalChannel m n) {p q : Fin m → ℝ}
    (hp : ∀ j, 0 ≤ p j) (hq : ∀ j, 0 ≤ q j) (hac : AbsContinuous p q) :
    AbsContinuous (apply_channel M p) (apply_channel M q) := by
  intro k hk
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ => mul_nonneg (M.nonneg k j) (hp j))).mp hk
  have hm : 0 < M.matrix k j := (mul_pos_iff.mp hj).resolve_right (by
    rintro ⟨h, _⟩; exact (not_lt_of_ge (M.nonneg k j)) h) |>.1
  have hpj : 0 < p j := (mul_pos_iff.mp hj).resolve_right (by
    rintro ⟨h, _⟩; exact (not_lt_of_ge (M.nonneg k j)) h) |>.2
  exact (mul_pos hm (hac j hpj)).trans_le
    (Finset.single_le_sum (fun i _ => mul_nonneg (M.nonneg k i) (hq i)) (Finset.mem_univ j))

/-- Total formula; analytic claims below require nonnegativity and absolute continuity. -/
def kl_term (a b : ℝ) : ℝ := if a ≤ 0 then 0 else a * Real.log (a / b)
def kl_divergence {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ := ∑ j, kl_term (p j) (q j)
def kl_divergence_bits {ι : Type*} [Fintype ι] (p q : ι → ℝ) : ℝ :=
  kl_divergence p q / Real.log 2

theorem kl_term_of_nonneg {a b : ℝ} (ha : 0 ≤ a) :
    kl_term a b = a * Real.log (a / b) := by
  by_cases h : a ≤ 0
  · have : a = 0 := le_antisymm h ha
    simp [this, kl_term]
  · simp [kl_term, h]

@[simp] theorem kl_term_zero (b : ℝ) : kl_term 0 b = 0 := by simp [kl_term]

theorem kl_term_scale {a b t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) :
    kl_term (t*a) (t*b) = t * kl_term a b := by
  rw [kl_term_of_nonneg (mul_nonneg ht ha), kl_term_of_nonneg ha]
  by_cases h : t = 0
  · simp [h]
  · rw [mul_div_mul_left a b h]; ring

/-- Finite log-sum, including zero total mass and zero entries. -/
theorem log_sum_inequality {ι : Type*} [Fintype ι] (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hac : AbsContinuous a b) :
    kl_term (∑ i, a i) (∑ i, b i) ≤ ∑ i, kl_term (a i) (b i) := by
  classical
  let B := ∑ i, b i
  have hB : 0 ≤ B := Finset.sum_nonneg fun i _ => hb i
  have hz (i : ι) (h : b i = 0) : a i = 0 := by
    by_contra hne
    have := hac i (lt_of_le_of_ne (ha i) (Ne.symm hne))
    simp [h] at this
  have cancel (i : ι) : b i * (a i / b i) = a i := by
    by_cases h : b i = 0
    · simp [h, hz i h]
    · field_simp
  by_cases hzero : B = 0
  · have bz : ∀ i, b i = 0 := fun i =>
      le_antisymm (by simpa [B, hzero] using
        (Finset.single_le_sum (fun j _ => hb j) (Finset.mem_univ i))) (hb i)
    have az : ∀ i, a i = 0 := fun i => hz i (bz i)
    simp [az, bz]
  have hpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hzero)
  have hj := Real.convexOn_mul_log.map_sum_le (t := Finset.univ)
    (w := fun i => b i / B) (p := fun i => a i / b i)
    (fun i _ => div_nonneg (hb i) hB)
    (by rw [← Finset.sum_div]; exact div_self hzero)
    (fun i _ => div_nonneg (ha i) (hb i))
  simp only [smul_eq_mul] at hj
  have havg : (∑ i, b i / B * (a i / b i)) = (∑ i, a i) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    calc b i / B * (a i / b i) = (b i * (a i / b i)) / B := by ring
         _ = a i / B := by rw [cancel]
  rw [havg] at hj
  have hm := mul_le_mul_of_nonneg_left hj hB
  rw [Finset.mul_sum] at hm
  have hleft : B * ((∑ i, a i) / B * Real.log ((∑ i, a i) / B)) =
      kl_term (∑ i, a i) B := by
    rw [kl_term_of_nonneg (Finset.sum_nonneg fun i _ => ha i)]
    field_simp
  rw [hleft] at hm
  refine hm.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  rw [kl_term_of_nonneg (ha i)]
  calc B * (b i / B * (a i / b i * Real.log (a i / b i))) =
      (b i * (a i / b i)) * Real.log (a i / b i) := by field_simp
       _ = a i * Real.log (a i / b i) := by rw [cancel]

theorem kl_divergence_nonneg {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) (hac : AbsContinuous p q) :
    0 ≤ kl_divergence p q := by
  have h := log_sum_inequality p q hp.1 hq.1 hac
  simpa [hp.2, hq.2, kl_term, kl_divergence] using h

theorem kl_data_processing_inequality (M : ClassicalChannel m n) {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) (hac : AbsContinuous p q) :
    kl_divergence (apply_channel M p) (apply_channel M q) ≤ kl_divergence p q := by
  calc kl_divergence (apply_channel M p) (apply_channel M q) ≤
      ∑ k, ∑ j, kl_term (M.matrix k j * p j) (M.matrix k j * q j) := by
        apply Finset.sum_le_sum
        intro k _
        apply log_sum_inequality
        · exact fun j => mul_nonneg (M.nonneg k j) (hp.1 j)
        · exact fun j => mul_nonneg (M.nonneg k j) (hq.1 j)
        · intro j hj
          have h := (mul_pos_iff.mp hj).resolve_right (by
            rintro ⟨h, _⟩; exact (not_lt_of_ge (M.nonneg k j)) h)
          exact mul_pos h.1 (hac j h.2)
       _ = kl_divergence p q := by
         simp only [kl_term_scale (hp.1 _) (M.nonneg _ _), Finset.sum_comm,
           ← Finset.sum_mul, M.col_sum_one, one_mul, kl_divergence]


theorem kl_data_processing_bits (M : ClassicalChannel m n) {p q : Fin m → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) (hac : AbsContinuous p q) :
    kl_divergence_bits (apply_channel M p) (apply_channel M q) ≤ kl_divergence_bits p q :=
  div_le_div_of_nonneg_right (kl_data_processing_inequality M hp hq hac)
    (le_of_lt (Real.log_pos (by norm_num)))

/-- Row sums supply Jensen weights; column sums preserve the total entropy sum. -/
theorem bistochastic_entropy_nondecreasing (B : BistochasticChannel m) {p : Fin m → ℝ}
    (hp : IsDistribution p) :
    shannon_entropy_bits p ≤ shannon_entropy_bits (apply_channel B.toClassicalChannel p) := by
  rw [entropy_eq_negMulLog p hp.1,
    entropy_eq_negMulLog _ (apply_nonneg B.toClassicalChannel hp.1)]
  apply div_le_div_of_nonneg_right _ (le_of_lt (Real.log_pos (by norm_num)))
  calc ∑ j, Real.negMulLog (p j) = ∑ k, ∑ j, B.matrix k j * Real.negMulLog (p j) := by
         rw [Finset.sum_comm]
         simp only [← Finset.sum_mul, B.col_sum_one, one_mul]
       _ ≤ ∑ k, Real.negMulLog (apply_channel B.toClassicalChannel p k) := by
         apply Finset.sum_le_sum
         intro k _
         exact Real.concaveOn_negMulLog.le_map_sum
           (fun j _ => B.nonneg k j) (B.row_sum_one k) (fun j _ => hp.1 j)

@[ext] theorem povm_ext (E F : FinitePOVM d m) (h : E.effects = F.effects) : E = F := by
  cases E; cases F; cases h; rfl

def postprocess_povm (M : ClassicalChannel m n) (E : FinitePOVM d m) : FinitePOVM d n where
  effects k := ∑ j, (M.matrix k j : ℂ) • E.effects j
  pos_semidef k := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply Finset.sum_nonneg
    intro j _
    exact ((E.pos_semidef j).smul (show (0 : ℂ) ≤ (M.matrix k j : ℂ) from
      Complex.nonneg_iff.mpr ⟨M.nonneg k j, rfl⟩)).nonneg
  completeness := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, ← Complex.ofReal_sum, M.col_sum_one,
      Complex.ofReal_one, one_smul, E.completeness]

theorem postprocess_hermitian (M : ClassicalChannel m n) (E : FinitePOVM d m) (k : Fin n) :
    ((postprocess_povm M E).effects k).IsHermitian :=
  ((postprocess_povm M E).pos_semidef k).isHermitian

theorem postprocess_prob (M : ClassicalChannel m n) (E : FinitePOVM d m) (ρ : Q d) :
    prob_dist (postprocess_povm M E) ρ = apply_channel M (prob_dist E ρ) := by
  funext k
  simp [prob_dist, postprocess_povm, apply_channel, Finset.mul_sum,
    Matrix.trace_sum, Matrix.trace_smul, Complex.mul_re]

theorem postprocess_identity (E : FinitePOVM d m) :
    postprocess_povm (identity_channel m) E = E := by
  apply povm_ext
  funext k
  simp [postprocess_povm, identity_channel]

theorem postprocess_compose (B : ClassicalChannel n l) (A : ClassicalChannel m n)
    (E : FinitePOVM d m) : postprocess_povm (compose B A) E =
      postprocess_povm B (postprocess_povm A E) := by
  apply povm_ext
  funext k
  simp only [postprocess_povm, compose, Complex.ofReal_sum, Finset.sum_smul,
    Complex.ofReal_mul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem compose_associative {o : ℕ} (C : ClassicalChannel l o)
    (B : ClassicalChannel n l) (A : ClassicalChannel m n) :
    compose C (compose B A) = compose (compose C B) A := by
  have he : (compose C (compose B A)).matrix = (compose (compose C B) A).matrix := by
    funext k j
    simp only [compose, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  exact channel_ext _ _ he

theorem povm_kl_data_processing (M : ClassicalChannel m n) (E : FinitePOVM d m)
    (ρ σ : Q d) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    (hac : AbsContinuous (prob_dist E ρ) (prob_dist E σ)) :
    kl_divergence (prob_dist (postprocess_povm M E) ρ)
      (prob_dist (postprocess_povm M E) σ) ≤ kl_divergence (prob_dist E ρ) (prob_dist E σ) := by
  rw [postprocess_prob, postprocess_prob]
  exact kl_data_processing_inequality M (prob_dist_isDistribution E ρ hρ)
    (prob_dist_isDistribution E σ hσ) hac


def permutation_channel (e : Fin m ≃ Fin m) : BistochasticChannel m where
  matrix k j := if e k = j then 1 else 0
  nonneg k j := by split <;> norm_num
  col_sum_one j := by
    rw [e.sum_comp (fun i => if i = j then (1 : ℝ) else 0)]
    simp
  row_sum_one k := by simp

theorem apply_permutation (e : Fin m ≃ Fin m) (p : Fin m → ℝ) :
    apply_channel (permutation_channel e).toClassicalChannel p = fun k => p (e k) := by
  funext k
  simp [apply_channel, permutation_channel]

theorem postprocess_permutation (e : Fin m ≃ Fin m) (E : FinitePOVM d m) (k : Fin m) :
    (postprocess_povm (permutation_channel e).toClassicalChannel E).effects k =
      E.effects (e k) := by
  simp [postprocess_povm, permutation_channel]

theorem entropy_permutation (e : Fin m ≃ Fin m) (p : Fin m → ℝ) :
    shannon_entropy_bits (fun k => p (e k)) = shannon_entropy_bits p := by
  simp only [shannon_entropy_bits, e.sum_comp (fun j => xlogx (p j))]

theorem kl_permutation (e : Fin m ≃ Fin m) (p q : Fin m → ℝ) :
    kl_divergence (fun k => p (e k)) (fun k => q (e k)) = kl_divergence p q :=
  e.sum_comp (fun j => kl_term (p j) (q j))

def erasure_channel (m : ℕ) (u : Fin n → ℝ) (hu : IsDistribution u) : ClassicalChannel m n where
  matrix k _ := u k
  nonneg k _ := hu.1 k
  col_sum_one _ := hu.2

theorem apply_erasure {p : Fin m → ℝ} (hp : IsDistribution p)
    (u : Fin n → ℝ) (hu : IsDistribution u) : apply_channel (erasure_channel m u hu) p = u := by
  funext k
  simp [apply_channel, erasure_channel, ← Finset.mul_sum, hp.2]

theorem kl_self {ι : Type*} [Fintype ι] (p : ι → ℝ) : kl_divergence p p = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  unfold kl_term
  split
  · rfl
  · rename_i h
    rw [div_self (ne_of_gt (lt_of_not_ge h)), Real.log_one, mul_zero]

theorem erasure_kl_zero {p q : Fin m → ℝ} (hp : IsDistribution p) (hq : IsDistribution q)
    (u : Fin n → ℝ) (hu : IsDistribution u) :
    kl_divergence (apply_channel (erasure_channel m u hu) p)
      (apply_channel (erasure_channel m u hu) q) = 0 := by
  rw [apply_erasure hp, apply_erasure hq, kl_self]

theorem postprocess_zero_effect (M : ClassicalChannel m n) (E : FinitePOVM d m) (k : Fin n)
    (h : ∀ j, M.matrix k j = 0 ∨ E.effects j = 0) : (postprocess_povm M E).effects k = 0 := by
  change (∑ j, (M.matrix k j : ℂ) • E.effects j) = 0
  apply Finset.sum_eq_zero
  intro j _
  rcases h j with h | h <;> simp [h]

theorem entropy_strict_concave {p q : Fin m → ℝ} (hp : ∀ i, 0 ≤ p i)
    (hq : ∀ i, 0 ≤ q i) (hne : p ≠ q) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) :
    a * shannon_entropy_bits p + b * shannon_entropy_bits q <
      shannon_entropy_bits (fun i => a * p i + b * q i) := by
  rw [entropy_eq_negMulLog p hp, entropy_eq_negMulLog q hq,
    entropy_eq_negMulLog _ (fun i =>
      add_nonneg (mul_nonneg ha.le (hp i)) (mul_nonneg hb.le (hq i)))]
  rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
  apply (div_lt_div_iff_of_pos_right (Real.log_pos (by norm_num))).mpr
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum
  · intro i _
    exact Real.concaveOn_negMulLog.2 (hp i) (hq i) ha.le hb.le hab
  · obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
    exact ⟨i, Finset.mem_univ i, Real.strictConcaveOn_negMulLog.2
      (hp i) (hq i) hi ha hb hab⟩

def binary_symmetric (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) : BistochasticChannel 2 where
  matrix k j := if k = j then 1 - ε else ε
  nonneg k j := by split <;> linarith
  col_sum_one j := by fin_cases j <;> simp [Fin.sum_univ_two]
  row_sum_one k := by fin_cases k <;> simp [Fin.sum_univ_two]

theorem binary_symmetric_apply (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (p : Fin 2 → ℝ) :
    apply_channel (binary_symmetric ε hε hε1).toClassicalChannel p =
      fun i => (1 - ε) * p i + ε * p ((Equiv.swap 0 1) i) := by
  funext i
  fin_cases i <;> simp [apply_channel, binary_symmetric, Fin.sum_univ_two, add_comm]

/-- Every nonuniform binary distribution strictly gains entropy for 0<epsilon<1 / 2. -/
theorem binary_symmetric_entropy_strict {p : Fin 2 → ℝ} (hp : IsDistribution p)
    (hne : p 0 ≠ p 1) {ε : ℝ} (hε : 0 < ε) (hhalf : ε < 1 / 2) :
    shannon_entropy_bits p < shannon_entropy_bits
      (apply_channel (binary_symmetric ε hε.le (by linarith)).toClassicalChannel p) := by
  rw [binary_symmetric_apply]
  have hne' : p ≠ (fun i => p ((Equiv.swap 0 1) i)) := by
    intro h
    have hh := congrFun h 0
    simp only [Equiv.swap_apply_left] at hh
    exact hne hh
  have h := entropy_strict_concave hp.1 (fun i => hp.1 _) hne'
    (show 0 < 1 - ε by linarith) hε (by ring)
  rw [entropy_permutation] at h
  nlinarith

def fair_bit : Fin 2 → ℝ := fun _ => 1 / 2
def point_mass : Fin 1 → ℝ := fun _ => 1

theorem fair_bit_distribution : IsDistribution fair_bit := by
  constructor
  · intro i; norm_num [fair_bit]
  · norm_num [fair_bit, Fin.sum_univ_two]

theorem point_mass_distribution : IsDistribution point_mass := by
  constructor
  · intro i; norm_num [point_mass]
  · simp [point_mass]

theorem fair_bit_entropy : shannon_entropy_bits fair_bit = 1 := by
  have ht : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [entropy_eq_negMulLog _ fair_bit_distribution.1]
  simp only [Fin.sum_univ_two, fair_bit, Real.negMulLog]
  rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  field_simp
  ring

theorem point_mass_entropy : shannon_entropy_bits point_mass = 0 := by
  simp [shannon_entropy_bits, point_mass, xlogx]

theorem coarse_graining_entropy_decrease_counterexample :
    shannon_entropy_bits fair_bit = 1 ∧
    shannon_entropy_bits
      (apply_channel (erasure_channel 2 point_mass point_mass_distribution) fair_bit) = 0 := by
  exact ⟨fair_bit_entropy, by rw [apply_erasure fair_bit_distribution, point_mass_entropy]⟩


theorem compose_identity_left (M : ClassicalChannel m n) : compose (identity_channel n) M = M := by
  apply channel_ext
  funext k j
  simp [compose, identity_channel]

theorem compose_identity_right (M : ClassicalChannel m n) : compose M (identity_channel m) = M := by
  apply channel_ext
  funext k j
  simp [compose, identity_channel]

theorem povm_abs_continuous_preserved (M : ClassicalChannel m n) (E : FinitePOVM d m)
    (ρ σ : Q d) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    (hac : AbsContinuous (prob_dist E ρ) (prob_dist E σ)) :
    AbsContinuous (prob_dist (postprocess_povm M E) ρ) (prob_dist (postprocess_povm M E) σ) := by
  rw [postprocess_prob, postprocess_prob]
  exact abs_continuous_preserved M (prob_dist_isDistribution E ρ hρ).1
    (prob_dist_isDistribution E σ hσ).1 hac

theorem povm_kl_data_processing_bits (M : ClassicalChannel m n) (E : FinitePOVM d m)
    (ρ σ : Q d) (hρ : QuantumNoBroadcastingMixed.IsDensityMatrix ρ)
    (hσ : QuantumNoBroadcastingMixed.IsDensityMatrix σ)
    (hac : AbsContinuous (prob_dist E ρ) (prob_dist E σ)) :
    kl_divergence_bits (prob_dist (postprocess_povm M E) ρ)
      (prob_dist (postprocess_povm M E) σ) ≤ kl_divergence_bits (prob_dist E ρ) (prob_dist E σ) :=
  div_le_div_of_nonneg_right (povm_kl_data_processing M E ρ σ hρ hσ hac)
    (le_of_lt (Real.log_pos (by norm_num)))

/-- This finite real API deliberately refuses singular inputs instead of assigning infinity. -/
def checked_kl {ι : Type*} [Fintype ι] (p q : ι → ℝ) : Option ℝ := by
  classical
  exact if IsDistribution p ∧ IsDistribution q ∧ AbsContinuous p q then
    some (kl_divergence p q) else none

theorem checked_kl_valid {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (hp : IsDistribution p) (hq : IsDistribution q) (hac : AbsContinuous p q) :
    checked_kl p q = some (kl_divergence p q) := by simp [checked_kl, hp, hq, hac]

theorem checked_kl_singular {ι : Type*} [Fintype ι] {p q : ι → ℝ}
    (h : ¬ AbsContinuous p q) : checked_kl p q = none := by simp [checked_kl, h]

/-- All principal claims are theorems, with normalization and support hypotheses explicit. -/
structure QuantumChannelClassicalDataProcessingSuite : Prop where
  distribution : ∀ {m n} (M : ClassicalChannel m n) p,
    IsDistribution p → IsDistribution (apply_channel M p)
  postprocessing : ∀ {d m n} (M : ClassicalChannel m n) (E : FinitePOVM d m) ρ,
    prob_dist (postprocess_povm M E) ρ = apply_channel M (prob_dist E ρ)
  support : ∀ {m n} (M : ClassicalChannel m n) p q,
    IsDistribution p → IsDistribution q → AbsContinuous p q →
      AbsContinuous (apply_channel M p) (apply_channel M q)
  log_sum : ∀ {m} (a b : Fin m → ℝ), (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    AbsContinuous a b → kl_term (∑ i, a i) (∑ i, b i) ≤ ∑ i, kl_term (a i) (b i)
  nonnegative : ∀ {m} (p q : Fin m → ℝ), IsDistribution p → IsDistribution q →
    AbsContinuous p q → 0 ≤ kl_divergence p q
  dpi : ∀ {m n} (M : ClassicalChannel m n) p q,
    IsDistribution p → IsDistribution q → AbsContinuous p q →
      kl_divergence (apply_channel M p) (apply_channel M q) ≤ kl_divergence p q
  measurement_dpi : ∀ {d m n} (M : ClassicalChannel m n) (E : FinitePOVM d m) ρ σ,
    QuantumNoBroadcastingMixed.IsDensityMatrix ρ → QuantumNoBroadcastingMixed.IsDensityMatrix σ →
    AbsContinuous (prob_dist E ρ) (prob_dist E σ) →
      kl_divergence (prob_dist (postprocess_povm M E) ρ) (prob_dist (postprocess_povm M E) σ) ≤
        kl_divergence (prob_dist E ρ) (prob_dist E σ)
  entropy : ∀ {m} (B : BistochasticChannel m) p, IsDistribution p →
    shannon_entropy_bits p ≤ shannon_entropy_bits (apply_channel B.toClassicalChannel p)
  strict_binary : ∀ (p : Fin 2 → ℝ), IsDistribution p → p 0 ≠ p 1 →
    ∀ ε (hε : 0 < ε) (hhalf : ε < 1 / 2),
      shannon_entropy_bits p < shannon_entropy_bits
        (apply_channel (binary_symmetric ε hε.le (by linarith)).toClassicalChannel p)
  composition : ∀ {d m n l} (B : ClassicalChannel n l) (A : ClassicalChannel m n)
    (E : FinitePOVM d m),
    postprocess_povm (compose B A) E = postprocess_povm B (postprocess_povm A E)
  entropy_counterexample : shannon_entropy_bits fair_bit = 1 ∧
    shannon_entropy_bits
      (apply_channel (erasure_channel 2 point_mass point_mass_distribution) fair_bit) = 0

theorem verification_suite : QuantumChannelClassicalDataProcessingSuite where
  distribution := fun M _ hp => apply_distribution M hp
  postprocessing := postprocess_prob
  support := fun M _ _ hp hq hac => abs_continuous_preserved M hp.1 hq.1 hac
  log_sum := log_sum_inequality
  nonnegative := fun _ _ hp hq hac => kl_divergence_nonneg hp hq hac
  dpi := fun M _ _ hp hq hac => kl_data_processing_inequality M hp hq hac
  measurement_dpi := povm_kl_data_processing
  entropy := fun B _ hp => bistochastic_entropy_nondecreasing B hp
  strict_binary := fun _ hp hn _ he hh => binary_symmetric_entropy_strict hp hn he hh
  composition := postprocess_compose
  entropy_counterexample := coarse_graining_entropy_decrease_counterexample

end QuantumChannelClassicalDataProcessing
