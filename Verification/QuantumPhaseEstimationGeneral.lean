/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPhaseEstimation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! Finite-register QPE. Controlled powers and inverse Fourier interference are
explicit operations. Probability statements assume a normalized eigenvector.
No gate synthesis, eigenstate preparation or hardware implementation is claimed. -/
noncomputable section
namespace QuantumPhaseEstimationGeneral
open scoped BigOperators ComplexConjugate

/-- A phase measured in turns, with period one. -/
def phase (t : ℝ) : ℂ := Complex.exp (Complex.I * (2 * Real.pi * t : ℝ))

@[simp] theorem phase_zero : phase 0 = 1 := by simp [phase]
theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  simp only [phase, Complex.ofReal_add, mul_add, Complex.exp_add]
@[simp] theorem phase_norm (t : ℝ) : ‖phase t‖ = 1 := by
  simp [phase, Complex.norm_exp]
theorem phase_conj (t : ℝ) : conj (phase t) = phase (-t) := by
  rw [phase, ← Complex.exp_conj]
  simp [phase, map_ofNat]
theorem phase_nat_mul (t : ℝ) (k : ℕ) : phase (k * t) = phase t ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, phase_add, ih, pow_succ]
@[simp] theorem phase_int (z : ℤ) : phase z = 1 := by
  unfold phase
  rw [show Complex.I * ((2 * Real.pi * (z : ℝ) : ℝ) : ℂ) =
    (z : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I z

theorem phase_eq_one_iff (t : ℝ) : phase t = 1 ↔ ∃ z : ℤ, t = z := by
  rw [phase, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z, h⟩
    have hi := congrArg Complex.im h
    simp at hi
    refine ⟨z, ?_⟩
    nlinarith [Real.pi_pos]
  · rintro ⟨z, rfl⟩
    exact ⟨z, by push_cast; ring⟩

def amplitude (N : ℕ) (θ : ℝ) (y : Fin N) : ℂ :=
  (N : ℂ)⁻¹ * ∑ k : Fin N, phase (k.val * (θ - y.val / N))
def probability (N : ℕ) (θ : ℝ) (y : Fin N) : ℝ := ‖amplitude N θ y‖ ^ 2

theorem phase_sum_geometric (N : ℕ) (δ : ℝ) (hδ : phase δ ≠ 1) :
    (∑ k : Fin N, phase (k.val * δ)) = (phase (N * δ) - 1) / (phase δ - 1) := by
  simp_rw [phase_nat_mul]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq hδ]

theorem phase_sub_one_norm (t : ℝ) : ‖phase t - 1‖ = 2 * |Real.sin (Real.pi * t)| := by
  rw [phase, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * t / 2 = Real.pi * t by ring]
  simp

theorem qpe_geometric_sum_closed_form (N : ℕ) (_hN : 0 < N) (θ : ℝ) (y : Fin N)
    (hδ : ¬ ∃ z : ℤ, θ - y.val / N = z) :
    ‖amplitude N θ y‖ = |Real.sin (Real.pi * N * (θ - y.val / N))| /
      (N * |Real.sin (Real.pi * (θ - y.val / N))|) := by
  have hp : phase (θ - y.val / N) ≠ 1 := mt (phase_eq_one_iff _).mp hδ
  rw [amplitude, phase_sum_geometric _ _ hp, norm_mul, norm_inv, norm_div,
    phase_sub_one_norm, phase_sub_one_norm]
  simp only [Complex.norm_natCast, mul_assoc]
  ring

theorem phase_shift_int (t : ℝ) (z : ℤ) : phase (t + z) = phase t := by
  rw [phase_add, phase_int, mul_one]

theorem amplitude_of_integral (N : ℕ) (hN : 0 < N) (θ : ℝ) (y : Fin N)
    (h : phase (θ - y.val / N) = 1) : amplitude N θ y = 1 := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp [amplitude, phase_nat_mul, h, hn]

theorem amplitude_periodic (N : ℕ) (θ : ℝ) (y : Fin N) (z : ℤ) :
    amplitude N (θ + z) y = amplitude N θ y := by
  unfold amplitude
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  have h : (k.val : ℝ) * (θ + z - y.val / N) =
      k.val * (θ - y.val / N) + ((k.val : ℤ) * z : ℤ) := by push_cast; ring
  rw [h, phase_shift_int]

/-- A representative of the distance on the circle, including either midpoint tie. -/
def Nearest (N : ℕ) (θ : ℝ) (b : Fin N) : Prop :=
  ∃ z : ℤ, |θ - b.val / N - z| ≤ 1 / (2 * N)

theorem amplitude_lower_bound_local (N : ℕ) (hN : 0 < N) (θ : ℝ) (b : Fin N)
    (hnear : |θ - b.val / N| ≤ 1 / (2 * N)) :
    2 / Real.pi ≤ ‖amplitude N θ b‖ := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp := Real.pi_pos
  by_cases h : phase (θ - b.val / N) = 1
  · rw [amplitude_of_integral N hN θ b h, norm_one]
    exact (div_le_one hp).2 Real.two_le_pi
  · have hc := qpe_geometric_sum_closed_form N hN θ b
      (mt (phase_eq_one_iff _).mpr h)
    rw [hc]
    have hs : 0 < |Real.sin (Real.pi * (θ - b.val / N))| := by
      have hz := norm_pos_iff.mpr (sub_ne_zero.mpr h)
      rw [phase_sub_one_norm] at hz
      linarith
    have habs : (N : ℝ) * |θ - b.val / N| ≤ 1 / 2 := by
      have := (le_div_iff₀ (show (0 : ℝ) < 2 * N by positivity)).1 hnear
      nlinarith
    have hj := Real.mul_abs_le_abs_sin (x := Real.pi * N * (θ - b.val / N))
      (by rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hn]; nlinarith)
    have hu := Real.abs_sin_le_abs (x := Real.pi * (θ - b.val / N))
    rw [abs_mul, abs_of_pos hp] at hu
    rw [abs_mul, abs_mul, abs_of_pos hp, abs_of_pos hn] at hj
    apply (le_div_iff₀ (mul_pos hn hs)).2
    calc
      2 / Real.pi * (N * |Real.sin (Real.pi * (θ - b.val / N))|) ≤
          2 / Real.pi * (N * (Real.pi * |θ - b.val / N|)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hu hn.le) (by positivity)
      _ = 2 / Real.pi * (Real.pi * N * |θ - b.val / N|) := by ring
      _ ≤ _ := hj

theorem qpe_arbitrary_phase_lower_bound (N : ℕ) (hN : 0 < N) (θ : ℝ) (b : Fin N)
    (hnear : Nearest N θ b) : 4 / Real.pi ^ 2 ≤ probability N θ b := by
  obtain ⟨z, hz⟩ := hnear
  have hl := amplitude_lower_bound_local N hN (θ - z) b
    (by simpa only [sub_right_comm] using hz)
  have he : amplitude N (θ - z) b = amplitude N θ b := by
    have := amplitude_periodic N (θ - z) b z
    simpa using this.symm
  rw [he] at hl
  have hsq := mul_self_le_mul_self (by positivity : (0 : ℝ) ≤ 2 / Real.pi) hl
  unfold probability
  have heq : (4 : ℝ) / Real.pi ^ 2 = (2 / Real.pi) ^ 2 := by ring
  rw [heq]
  nlinarith

theorem phase_fraction_ne_one {N : ℕ} (hN : 0 < N) (x y : Fin N) (hxy : x ≠ y) :
    phase ((x.val - y.val : ℝ) / N) ≠ 1 := by
  intro h
  obtain ⟨z, hz⟩ := (phase_eq_one_iff _).mp h
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hx : (x.val : ℝ) < N := by exact_mod_cast x.isLt
  have hy : (y.val : ℝ) < N := by exact_mod_cast y.isLt
  have hx0 : (0 : ℝ) ≤ x.val := by positivity
  have hy0 : (0 : ℝ) ≤ y.val := by positivity
  have hm := (div_eq_iff hn.ne').mp hz
  have hzlo : (-1 : ℤ) < z := by exact_mod_cast (show (-1 : ℝ) < z by nlinarith)
  have hzhi : z < (1 : ℤ) := by exact_mod_cast (show (z : ℝ) < 1 by nlinarith)
  have hz0 : z = 0 := by omega
  subst z
  have he : (x.val : ℝ) = (y.val : ℝ) := sub_eq_zero.mp (by simpa using hm)
  exact hxy (Fin.ext (by exact_mod_cast he))

theorem phase_orthogonality {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    (∑ k : Fin N, phase (k.val * ((x.val - y.val : ℝ) / N))) =
      if x = y then (N : ℂ) else 0 := by
  by_cases hxy : x = y
  · simp [hxy]
  · rw [if_neg hxy, phase_sum_geometric _ _ (phase_fraction_ne_one hN x y hxy)]
    have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [show (N : ℝ) * ((x.val - y.val : ℝ) / N) = x.val - y.val by field_simp]
    have hi : phase (x.val - y.val : ℝ) = 1 := by
      exact_mod_cast phase_int ((x.val : ℤ) - y.val)
    rw [hi, sub_self, zero_div]

theorem qpe_exact_dyadic_phase {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    amplitude N (x.val / N) y = if y = x then 1 else 0 := by
  have hn : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  unfold amplitude
  simp_rw [← sub_div]
  rw [phase_orthogonality hN]
  by_cases h : x = y <;> simp [h, Ne.symm, hn]

def scale (N : ℕ) : ℂ := (Real.sqrt N : ℂ)⁻¹
def kernel (N : ℕ) (j k : Fin N) : ℂ := phase (j.val * k.val / N)
def QFT (N : ℕ) (v : Fin N → ℂ) (j : Fin N) : ℂ :=
  scale N * ∑ k, kernel N j k * v k
def inverseQFT (N : ℕ) (v : Fin N → ℂ) (j : Fin N) : ℂ :=
  scale N * ∑ k, conj (kernel N j k) * v k

theorem scale_sq {N : ℕ} (_hN : 0 < N) : scale N * scale N = (N : ℂ)⁻¹ := by
  have h : (Real.sqrt N : ℂ) * (Real.sqrt N : ℂ) = N := by
    norm_cast
    exact Real.mul_self_sqrt (Nat.cast_nonneg N)
  rw [scale, ← mul_inv, h]
@[simp] theorem scale_conj (N : ℕ) : conj (scale N) = scale N := by simp [scale]

theorem kernel_symm (N : ℕ) (j k : Fin N) : kernel N j k = kernel N k j := by
  unfold kernel; rw [mul_comm (j.val : ℝ)]

theorem kernel_orthogonality {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    (∑ k, conj (kernel N k y) * kernel N k x) = if x = y then (N : ℂ) else 0 := by
  convert phase_orthogonality hN x y using 1
  apply Finset.sum_congr rfl
  intro k _
  rw [kernel, kernel, phase_conj, ← phase_add]
  congr 1
  ring

theorem inverse_qft_qft {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    inverseQFT N (QFT N v) = v := by
  funext j
  simp only [inverseQFT, QFT]
  calc
    _ = (scale N * scale N) * ∑ k, (∑ a, conj (kernel N a j) * kernel N a k) * v k := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro a _
      rw [kernel_symm N j a]
      ring
    _ = v j := by
      rw [scale_sq hN]
      simp [kernel_orthogonality hN, hN.ne']

theorem qft_inverse_qft {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    QFT N (inverseQFT N v) = v := by
  have hi := congrArg (fun u j => conj (u j)) (inverse_qft_qft hN (fun j => conj (v j)))
  funext j
  simpa [QFT, inverseQFT, map_sum] using congrFun hi j

def hermitian {N : ℕ} (u v : Fin N → ℂ) : ℂ := ∑ j, conj (u j) * v j
def normSquared {N : ℕ} (v : Fin N → ℂ) : ℝ := ∑ j, Complex.normSq (v j)

theorem fourier_adjoint {N : ℕ} (u v : Fin N → ℂ) :
    hermitian (QFT N u) v = hermitian u (inverseQFT N v) := by
  simp only [hermitian, QFT, inverseQFT, map_mul, map_sum, scale_conj,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [kernel_symm N k j]
  ring

theorem qft_unitarity {N : ℕ} (hN : 0 < N) (u v : Fin N → ℂ) :
    hermitian (QFT N u) (QFT N v) = hermitian u v := by
  rw [fourier_adjoint, inverse_qft_qft hN]

theorem inverse_qft_unitarity {N : ℕ} (hN : 0 < N) (u v : Fin N → ℂ) :
    hermitian (inverseQFT N u) (inverseQFT N v) = hermitian u v := by
  rw [← fourier_adjoint, qft_inverse_qft hN]

theorem hermitian_self {N : ℕ} (v : Fin N → ℂ) :
    hermitian v v = (normSquared v : ℂ) := by
  simp only [hermitian, normSquared, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_comm, Complex.mul_conj]

theorem inverse_qft_norm {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    normSquared (inverseQFT N v) = normSquared v := by
  have h := inverse_qft_unitarity hN v v
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h

theorem qft_norm {N : ℕ} (hN : 0 < N) (v : Fin N → ℂ) :
    normSquared (QFT N v) = normSquared v := by
  have h := qft_unitarity hN v v
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h

def preState (N : ℕ) (θ : ℝ) (k : Fin N) : ℂ := scale N * phase (k.val * θ)

theorem inverse_pre_amplitude {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    inverseQFT N (preState N θ) = amplitude N θ := by
  funext y
  unfold inverseQFT preState amplitude
  rw [← scale_sq hN]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hk : conj (kernel N y k) * phase (k.val * θ) =
      phase (k.val * (θ - y.val / N)) := by
    rw [kernel, phase_conj, ← phase_add]
    congr 1
    ring
  calc
    _ = (scale N * scale N) * (conj (kernel N y k) * phase (k.val * θ)) := by ring
    _ = _ := by rw [hk]

theorem pre_state_normalized {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    normSquared (preState N θ) = 1 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hs : Complex.normSq (scale N) = (N : ℝ)⁻¹ := by
    have h := congrArg norm (scale_sq hN)
    simp only [norm_mul, norm_inv, Complex.norm_natCast] at h
    rw [Complex.normSq_eq_norm_sq, pow_two]
    exact h
  simp [normSquared, preState, Complex.normSq_eq_norm_sq,
    phase_norm, ← Complex.normSq_eq_norm_sq (scale N), hs, hn]

theorem qpe_probability_normalized {N : ℕ} (hN : 0 < N) (θ : ℝ) :
    (∑ y : Fin N, probability N θ y) = 1 := by
  have h := inverse_qft_norm hN (preState N θ)
  rw [inverse_pre_amplitude hN, pre_state_normalized hN] at h
  simpa only [normSquared, Complex.normSq_eq_norm_sq, probability] using h

def nearestSample (N : ℕ) (hN : 0 < N) (θ : ℝ) : Fin N :=
  ⟨(round (N * θ) % (N : ℤ)).toNat,
    (Int.toNat_lt (Int.emod_nonneg _ (by omega))).mpr (Int.emod_lt_of_pos _ (by omega))⟩

theorem nearest_sample_valid (N : ℕ) (hN : 0 < N) (θ : ℝ) :
    Nearest N θ (nearestSample N hN θ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hz : (0 : ℤ) ≤ round (N * θ) % (N : ℤ) := Int.emod_nonneg _ (by omega)
  have hb : ((nearestSample N hN θ).val : ℝ) = ((round (N * θ) % (N : ℤ) : ℤ) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hz
  refine ⟨round (N * θ) / (N : ℤ), ?_⟩
  have he : (((round (N * θ) % (N : ℤ)) : ℤ) : ℝ) +
      (N : ℝ) * ((round (N * θ) / (N : ℤ) : ℤ) : ℝ) = round (N * θ) := by
    exact_mod_cast Int.emod_add_mul_ediv (round ((N : ℝ) * θ)) (N : ℤ)
  have hid : θ - (nearestSample N hN θ).val / N -
      ((round (N * θ) / (N : ℤ) : ℤ) : ℝ) = (N * θ - round (N * θ)) / N := by
    rw [hb]
    apply (eq_div_iff hn.ne').2
    field_simp
    simp only [mul_comm (N : ℝ) θ] at he
    nlinarith
  rw [hid, abs_div, abs_of_pos hn]
  calc
    _ ≤ (1 / 2 : ℝ) / N := div_le_div_of_nonneg_right (abs_sub_round _) hn.le
    _ = _ := by ring

abbrev TargetState (d : ℕ) := Fin d → ℂ
abbrev TargetOperator (d : ℕ) := TargetState d →ₗ[ℂ] TargetState d

/-- Binary control order: recurse through lower bits, then apply the high controlled power.
Each branch is linear; the high branch applies precisely U^(2^n), not a prescribed phase. -/
def controlledCascade (U : TargetOperator d) : (n : ℕ) → Fin (2 ^ n) → TargetOperator d
  | 0, _ => 1
  | n + 1, k =>
    let j : Fin (2 ^ n) := ⟨k.val % (2 ^ n), Nat.mod_lt _ (by positivity)⟩
    if k.val < 2 ^ n then controlledCascade U n j
    else U ^ (2 ^ n) * controlledCascade U n j

theorem controlled_cascade_eq_power (U : TargetOperator d) (n : ℕ) (k : Fin (2 ^ n)) :
    controlledCascade U n k = U ^ k.val := by
  induction n with
  | zero => simp [controlledCascade]
  | succ n ih =>
    have hp : 0 < 2 ^ n := by positivity
    have hk : k.val < 2 ^ n * 2 := by simpa [pow_succ] using k.isLt
    simp only [controlledCascade, ih]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · rw [← pow_add]
      congr 1
      have hmod : k.val % (2 ^ n) = k.val - 2 ^ n := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      omega

theorem eigen_power (U : TargetOperator d) (ψ : TargetState d) (θ : ℝ)
    (hψ : U ψ = phase θ • ψ) (k : ℕ) : (U ^ k) ψ = phase (k * θ) • ψ := by
  rw [phase_nat_mul]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, map_smul, hψ, smul_smul]
    rw [pow_succ]

def prepareControl (n : ℕ) (ψ : TargetState d) : Fin (2 ^ n) → TargetState d :=
  fun _ => scale (2 ^ n) • ψ

/-- The normalized n-fold Hadamard kernel in the binary integer basis. -/
def hadamardKernel (n : ℕ) (j k : Fin (2 ^ n)) : ℂ :=
  scale (2 ^ n) * (-1 : ℂ) ^ (∑ b : Fin n,
    if j.val.testBit b.val && k.val.testBit b.val then (1 : ℕ) else 0)

def hadamardControl (n : ℕ) (v : Fin (2 ^ n) → ℂ) (j : Fin (2 ^ n)) : ℂ :=
  ∑ k, hadamardKernel n j k * v k

def zeroControl (n : ℕ) (k : Fin (2 ^ n)) : ℂ := if k.val = 0 then 1 else 0

theorem hadamard_prepares_uniform (n : ℕ) (j : Fin (2 ^ n)) :
    hadamardControl n (zeroControl n) j = scale (2 ^ n) := by
  have hz : (0 : ℕ) < 2 ^ n := by positivity
  let z : Fin (2 ^ n) := ⟨0, hz⟩
  unfold hadamardControl zeroControl
  rw [Finset.sum_eq_single z]
  · simp [hadamardKernel, z]
  · intro k _ hk
    have hk0 : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [hk0]
  · simp

theorem prepare_control_from_hadamard (n : ℕ) (ψ : TargetState d) :
    prepareControl n ψ = fun k => hadamardControl n (zeroControl n) k • ψ := by
  funext k
  rw [hadamard_prepares_uniform]
  rfl

def runControlled (U : TargetOperator d) (n : ℕ) (ψ : TargetState d) :
    Fin (2 ^ n) → TargetState d :=
  fun k => controlledCascade U n k (prepareControl n ψ k)

def inverseControl (N : ℕ) (v : Fin N → TargetState d) : Fin N → TargetState d :=
  fun y t => inverseQFT N (fun k => v k t) y

def runQPE (U : TargetOperator d) (n : ℕ) (ψ : TargetState d) :
    Fin (2 ^ n) → TargetState d := inverseControl (2 ^ n) (runControlled U n ψ)

theorem controlled_powers_kickback (U : TargetOperator d) (n : ℕ) (ψ : TargetState d)
    (θ : ℝ) (hψ : U ψ = phase θ • ψ) :
    runControlled U n ψ = fun k => preState (2 ^ n) θ k • ψ := by
  funext k
  simp only [runControlled, prepareControl, controlled_cascade_eq_power, map_smul,
    eigen_power U ψ θ hψ, smul_smul, preState]

theorem inverse_on_product {N : ℕ} (v : Fin N → ℂ) (ψ : TargetState d) :
    inverseControl N (fun k => v k • ψ) = fun y => inverseQFT N v y • ψ := by
  funext y t
  simp [inverseControl, inverseQFT, Finset.sum_mul, mul_assoc]

theorem qpe_amplitude_derivation (U : TargetOperator d) (n : ℕ) (ψ : TargetState d)
    (θ : ℝ) (hψ : U ψ = phase θ • ψ) :
    runQPE U n ψ = fun y => amplitude (2 ^ n) θ y • ψ := by
  rw [runQPE, controlled_powers_kickback U n ψ θ hψ, inverse_on_product,
    inverse_pre_amplitude (by positivity)]

def IsUnitary (U : TargetOperator d) : Prop :=
  ∀ u v, hermitian (U u) (U v) = hermitian u v

def jointNormSquared {N d : ℕ} (v : Fin N → TargetState d) : ℝ :=
  ∑ k, normSquared (v k)

theorem target_norm_smul (z : ℂ) (ψ : TargetState d) :
    normSquared (z • ψ) = Complex.normSq z * normSquared ψ := by
  simp [normSquared, Complex.normSq_mul, Finset.mul_sum]

theorem unitary_norm (U : TargetOperator d) (hU : IsUnitary U) (ψ : TargetState d) :
    normSquared (U ψ) = normSquared ψ := by
  have h := hU ψ ψ
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h

theorem power_norm (U : TargetOperator d) (hU : IsUnitary U) (k : ℕ) (ψ : TargetState d) :
    normSquared ((U ^ k) ψ) = normSquared ψ := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', Module.End.mul_apply, unitary_norm U hU, ih]

theorem prepare_control_norm (n : ℕ) (ψ : TargetState d) :
    jointNormSquared (prepareControl n ψ) = normSquared ψ := by
  have h := pre_state_normalized (N := 2 ^ n) (by positivity) 0
  simp only [normSquared, preState, mul_zero, phase_zero, mul_one] at h
  simp only [jointNormSquared, prepareControl, target_norm_smul, ← Finset.sum_mul]
  rw [h, one_mul]

theorem controlled_cascade_norm (U : TargetOperator d) (hU : IsUnitary U)
    (n : ℕ) (v : Fin (2 ^ n) → TargetState d) :
    jointNormSquared (fun k => controlledCascade U n k (v k)) = jointNormSquared v := by
  simp only [jointNormSquared, controlled_cascade_eq_power, power_norm U hU]

theorem inverse_control_norm {N : ℕ} (hN : 0 < N) (v : Fin N → TargetState d) :
    jointNormSquared (inverseControl N v) = jointNormSquared v := by
  calc
    _ = ∑ t, normSquared (inverseQFT N (fun k => v k t)) := by
      simp only [jointNormSquared, inverseControl, normSquared]
      exact Finset.sum_comm
    _ = ∑ t, normSquared (fun k => v k t) := by simp_rw [inverse_qft_norm hN]
    _ = _ := by simp only [jointNormSquared, normSquared]; exact Finset.sum_comm

theorem qpe_circuit_norm (U : TargetOperator d) (hU : IsUnitary U) (n : ℕ)
    (ψ : TargetState d) : jointNormSquared (runQPE U n ψ) = normSquared ψ := by
  rw [runQPE, inverse_control_norm (by positivity)]
  change jointNormSquared (fun k => controlledCascade U n k (prepareControl n ψ k)) = _
  rw [controlled_cascade_norm U hU, prepare_control_norm]

structure UnitaryEigenInput (d : ℕ) (θ : ℝ) where
  operator : TargetOperator d
  target : TargetState d
  unitary : IsUnitary operator
  normalized : normSquared target = 1
  eigenstate : operator target = phase θ • target

theorem qpe_joint_distribution (e : UnitaryEigenInput d θ) (n : ℕ) (y : Fin (2 ^ n)) :
    normSquared (runQPE e.operator n e.target y) = probability (2 ^ n) θ y := by
  rw [qpe_amplitude_derivation _ _ _ _ e.eigenstate, target_norm_smul, e.normalized,
    mul_one, Complex.normSq_eq_norm_sq]
  rfl

theorem qpe_nearest_sample_success (e : UnitaryEigenInput d θ) (n : ℕ) :
    4 / Real.pi ^ 2 ≤ normSquared (runQPE e.operator n e.target
      (nearestSample (2 ^ n) (by positivity) θ)) := by
  rw [qpe_joint_distribution]
  exact qpe_arbitrary_phase_lower_bound _ (by positivity) _ _
    (nearest_sample_valid _ (by positivity) _)

theorem qpe_case_zero_qubits (U : TargetOperator d) (ψ : TargetState d) :
    runQPE U 0 ψ = fun _ => ψ := by
  funext y t
  simp [runQPE, runControlled, controlledCascade, prepareControl, inverseControl,
    inverseQFT, scale, kernel, phase]

theorem qpe_exact_probability {N : ℕ} (hN : 0 < N) (x y : Fin N) :
    probability N (x.val / N) y = if y = x then 1 else 0 := by
  rw [probability, qpe_exact_dyadic_phase hN]
  split_ifs <;> norm_num

@[simp] theorem scale_four : scale 4 = (1 / 2 : ℂ) := by
  have hs : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp [scale, hs]

theorem scaled_kernel_four (j k : Fin 4) :
    scale 4 * kernel 4 j k = QuantumPhaseEstimation.fourierMatrix j k := by
  rw [QuantumPhaseEstimation.fourier_exponential, scale_four]
  congr 1
  unfold kernel phase
  congr 1
  push_cast
  ring

theorem inverse_qft_bridge_two (v : Fin 4 → ℂ) :
    inverseQFT 4 v = QuantumPhaseEstimation.QFT_inv v := by
  funext j
  simp only [inverseQFT, QuantumPhaseEstimation.QFT_inv,
    QuantumPhaseEstimation.inverseFourierMatrix, ← scaled_kernel_four, map_mul, scale_conj]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [kernel_symm 4 k j]
  ring

theorem controlled_bridge_two (U : TargetOperator 2) (ψ : TargetState 2) :
    runControlled U 2 ψ = QuantumPhaseEstimation.runControlled U ψ := by
  funext k
  fin_cases k <;>
    simp [runControlled, controlledCascade, prepareControl,
      QuantumPhaseEstimation.runControlled, QuantumPhaseEstimation.controlled,
      QuantumPhaseEstimation.highBit, QuantumPhaseEstimation.lowBit,
      QuantumPhaseEstimation.prepareControl, QuantumPhaseEstimation.hadamard_prepares_uniform,
      pow_succ, Module.End.mul_apply, LinearMap.comp_apply]

theorem qpe_bridge_to_two_qubit (U : TargetOperator 2) (ψ : TargetState 2) :
    runQPE U 2 ψ = QuantumPhaseEstimation.runQPE U ψ := by
  rw [runQPE, controlled_bridge_two, QuantumPhaseEstimation.runQPE]
  funext j t
  exact congrFun (inverse_qft_bridge_two
    (fun k => QuantumPhaseEstimation.runControlled U ψ k t)) j

theorem qpe_probability_bridge_two (p : QuantumPhaseEstimation.DyadicPhase2) (y : Fin 4) :
    probability 4 (QuantumPhaseEstimation.phaseValue p) y =
      QuantumPhaseEstimation.outcomeWeight
        (QuantumPhaseEstimation.QFT_inv (QuantumPhaseEstimation.qpePreState p)) y := by
  rw [QuantumPhaseEstimation.qpe_inverse_qft_exact, QuantumPhaseEstimation.phaseValue_eq_index]
  have he := qpe_exact_probability (N := 4) (by decide) (QuantumPhaseEstimation.phaseIndex p) y
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  by_cases h : y = QuantumPhaseEstimation.phaseIndex p <;>
    simp [h, QuantumPhaseEstimation.outcomeWeight, QuantumPhaseEstimation.basis]

theorem qpe_zero_qubit_probability (θ : ℝ) (y : Fin (2 ^ 0)) :
    probability (2 ^ 0) θ y = 1 := by
  simp [probability, amplitude]

theorem qpe_amplitude_exponential (N : ℕ) (θ : ℝ) (y : Fin N) :
    amplitude N θ y = (N : ℂ)⁻¹ * ∑ k : Fin N,
      Complex.exp (2 * Real.pi * Complex.I * k.val * ((θ - y.val / N : ℝ) : ℂ)) := by
  unfold amplitude phase
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  push_cast
  ring

/-- The suite includes both the operational circuit and the analytic estimate.
Nearest is a proved inhabited rounding contract, not an assumed success event. -/
structure QuantumPhaseEstimationGeneralSuite : Prop where
  inverse_left : ∀ N, 0 < N → ∀ v, inverseQFT N (QFT N v) = v
  inverse_right : ∀ N, 0 < N → ∀ v, QFT N (inverseQFT N v) = v
  unitary : ∀ N, 0 < N → ∀ u v, hermitian (inverseQFT N u) (inverseQFT N v) = hermitian u v
  preparation : ∀ n d (ψ : TargetState d),
    prepareControl n ψ = fun k => hadamardControl n (zeroControl n) k • ψ
  controlled_powers : ∀ d (U : TargetOperator d) n k, controlledCascade U n k = U ^ k.val
  operational_amplitude : ∀ d (U : TargetOperator d) n ψ θ, U ψ = phase θ • ψ →
    runQPE U n ψ = fun y => amplitude (2 ^ n) θ y • ψ
  circuit_norm : ∀ d (U : TargetOperator d), IsUnitary U → ∀ n ψ,
    jointNormSquared (runQPE U n ψ) = normSquared ψ
  exact : ∀ N, 0 < N → ∀ x y : Fin N,
    amplitude N (x.val / N) y = if y = x then 1 else 0
  normalized : ∀ N, 0 < N → ∀ θ, (∑ y : Fin N, probability N θ y) = 1
  geometric : ∀ N, 0 < N → ∀ (θ : ℝ) (y : Fin N), (¬ ∃ z : ℤ, θ - y.val / N = z) →
    ‖amplitude N θ y‖ = |Real.sin (Real.pi * N * (θ - y.val / N))| /
      (N * |Real.sin (Real.pi * (θ - y.val / N))|)
  integral : ∀ N, 0 < N → ∀ θ (y : Fin N), phase (θ - y.val / N) = 1 →
    amplitude N θ y = 1
  nearest_exists : ∀ N (hN : 0 < N) θ, Nearest N θ (nearestSample N hN θ)
  lower_bound : ∀ N, 0 < N → ∀ θ (b : Fin N), Nearest N θ b →
    4 / Real.pi ^ 2 ≤ probability N θ b
  measured_lower_bound : ∀ d θ (e : UnitaryEigenInput d θ) n,
    4 / Real.pi ^ 2 ≤ normSquared (runQPE e.operator n e.target
      (nearestSample (2 ^ n) (by positivity) θ))
  bridge : ∀ (U : TargetOperator 2) ψ, runQPE U 2 ψ = QuantumPhaseEstimation.runQPE U ψ
  zero_qubits : ∀ d (U : TargetOperator d) ψ, runQPE U 0 ψ = fun _ => ψ

theorem quantum_phase_estimation_general_master_suite : QuantumPhaseEstimationGeneralSuite where
  inverse_left := fun _ => inverse_qft_qft
  inverse_right := fun _ => qft_inverse_qft
  unitary := fun _ => inverse_qft_unitarity
  preparation := fun n _ ψ => prepare_control_from_hadamard n ψ
  controlled_powers := fun _ => controlled_cascade_eq_power
  operational_amplitude := fun _ => qpe_amplitude_derivation
  circuit_norm := fun _ => qpe_circuit_norm
  exact := fun _ => qpe_exact_dyadic_phase
  normalized := fun _ => qpe_probability_normalized
  geometric := qpe_geometric_sum_closed_form
  integral := amplitude_of_integral
  nearest_exists := nearest_sample_valid
  lower_bound := qpe_arbitrary_phase_lower_bound
  measured_lower_bound := fun _ _ => qpe_nearest_sample_success
  bridge := qpe_bridge_to_two_qubit
  zero_qubits := fun _ => qpe_case_zero_qubits

end QuantumPhaseEstimationGeneral
