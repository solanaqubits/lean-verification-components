/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumPhaseEstimationGeneral
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Spectral order finding on a padded finite register. The order is a mathematical
parameter of the proof, not input supplied to the modular-multiplication circuit.
Continued fractions, repeated sampling and factorization are separate obligations. -/
noncomputable section
namespace QuantumShorOrderFindingCore
open scoped BigOperators ComplexConjugate
open QuantumPhaseEstimationGeneral

structure Parameters where
  modulus : ℕ
  modulus_ge_two : 2 ≤ modulus
  base : ℕ
  coprime : Nat.Coprime base modulus
  width : ℕ
  fits : modulus ≤ 2 ^ width

namespace Parameters
variable (c : Parameters)
instance : NeZero c.modulus := ⟨by have := c.modulus_ge_two; omega⟩
abbrev dimension := 2 ^ c.width
def period : ℕ := orderOf (c.base : ZMod c.modulus)
theorem period_pos : 0 < c.period :=
  ((ZMod.isUnit_iff_coprime _ _).2 c.coprime).isOfFinOrder.orderOf_pos
instance : NeZero c.period := ⟨c.period_pos.ne'⟩
theorem period_power : (c.base : ZMod c.modulus) ^ c.period = 1 := pow_orderOf_eq_one _
theorem powers_distinct {k l : ℕ} (hk : k < c.period) (hl : l < c.period) :
    (c.base : ZMod c.modulus) ^ k = (c.base : ZMod c.modulus) ^ l ↔ k = l := by
  constructor
  · exact pow_injOn_Iio_orderOf hk hl
  · rintro rfl; rfl

def residuePerm : Equiv.Perm (Fin c.modulus) where
  toFun y := ⟨((c.base : ZMod c.modulus) * (y.val : ZMod c.modulus)).val, ZMod.val_lt _⟩
  invFun y := ⟨(((ZMod.unitOfCoprime c.base c.coprime)⁻¹ : (ZMod c.modulus)ˣ) *
    (y.val : ZMod c.modulus)).val, ZMod.val_lt _⟩
  left_inv y := by
    apply Fin.ext
    simp only [ZMod.natCast_zmod_val]
    rw [← ZMod.coe_unitOfCoprime c.base c.coprime, ← mul_assoc]
    rw [Units.inv_mul, one_mul, ZMod.val_natCast_of_lt y.isLt]
  right_inv y := by
    apply Fin.ext
    simp only [ZMod.natCast_zmod_val]
    rw [← ZMod.coe_unitOfCoprime c.base c.coprime, ← mul_assoc]
    rw [Units.mul_inv, one_mul, ZMod.val_natCast_of_lt y.isLt]

def residueEmbedding : Fin c.modulus ≃ {y : Fin c.dimension // y.val < c.modulus} where
  toFun y := ⟨⟨y.val, y.isLt.trans_le c.fits⟩, y.isLt⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def registerPerm : Equiv.Perm (Fin c.dimension) :=
  c.residuePerm.extendDomain c.residueEmbedding

theorem registerPerm_low (y : Fin c.dimension) (hy : y.val < c.modulus) :
    (c.registerPerm y).val = (c.base * y.val) % c.modulus := by
  rw [registerPerm,
    Equiv.Perm.extendDomain_apply_subtype c.residuePerm c.residueEmbedding (b := y) hy]
  change ((c.base : ZMod c.modulus) * (y.val : ZMod c.modulus)).val = _
  rw [← Nat.cast_mul, ZMod.val_natCast]

theorem registerPerm_high (y : Fin c.dimension) (hy : c.modulus ≤ y.val) :
    c.registerPerm y = y :=
  Equiv.Perm.extendDomain_apply_not_subtype _ _ (not_lt.mpr hy)

/-- Push forward along the actual padded modular-multiplication permutation. -/
def modularOperator : TargetOperator c.dimension where
  toFun v := fun y => v (c.registerPerm.symm y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem modularOperator_unitary : IsUnitary c.modularOperator := by
  intro u v
  exact Equiv.sum_comp c.registerPerm.symm (fun y => conj (u y) * v y)

def orbit (k : Fin c.period) : Fin c.dimension :=
  ⟨((c.base : ZMod c.modulus) ^ k.val).val, (ZMod.val_lt _).trans_le c.fits⟩

theorem orbit_injective : Function.Injective c.orbit := by
  intro k l h
  apply Fin.ext
  apply (c.powers_distinct k.isLt l.isLt).1
  apply ZMod.val_injective c.modulus
  exact congrArg Fin.val h

theorem orbit_val (k : Fin c.period) : (c.orbit k).val = c.base ^ k.val % c.modulus := by
  change ((c.base : ZMod c.modulus) ^ k.val).val = _
  rw [← Nat.cast_pow, ZMod.val_natCast]

/-- Cyclic successor in the orbit index. -/
def successor : Equiv.Perm (Fin c.period) := Equiv.addRight 1

theorem registerPerm_orbit (k : Fin c.period) :
    c.registerPerm (c.orbit k) = c.orbit (c.successor k) := by
  apply Fin.ext
  rw [c.registerPerm_low _ (ZMod.val_lt _)]
  rw [← ZMod.val_natCast c.modulus, Nat.cast_mul]
  simp only [orbit, ZMod.natCast_zmod_val]
  change ((c.base : ZMod c.modulus) * (c.base : ZMod c.modulus) ^ k.val).val =
    ((c.base : ZMod c.modulus) ^ (c.successor k).val).val
  congr 1
  rw [← pow_succ']
  change _ = (c.base : ZMod c.modulus) ^ (k + 1 : Fin c.period).val
  rw [Fin.val_add]
  change _ = (c.base : ZMod c.modulus) ^ ((k.val + 1 % c.period) % c.period)
  rw [Nat.add_mod_mod]
  exact (pow_mod_orderOf _ _).symm

end Parameters

variable {d r : ℕ}
/-- A computational basis vector, with no eigenstate assumption. -/
def basis (j : Fin d) : TargetState d := fun y => if y = j then 1 else 0

theorem basis_inner (i j : Fin d) : hermitian (basis i) (basis j) =
    if i = j then 1 else 0 := by
  classical
  simp [hermitian, basis, eq_comm]

namespace Parameters
variable (c : Parameters)
/-- Isometric inclusion of orbit coordinates into the physical target register. -/
def orbitLift : (Fin c.period → ℂ) →ₗ[ℂ] TargetState c.dimension where
  toFun v := ∑ k, v k • basis (c.orbit k)
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' z v := by simp [smul_smul, Finset.smul_sum]

theorem orbitLift_apply (v : Fin c.period → ℂ) (y : Fin c.dimension) :
    c.orbitLift v y = ∑ k, v k * if y = c.orbit k then 1 else 0 := by
  simp [orbitLift, basis]

theorem orbitLift_inner (u v : Fin c.period → ℂ) :
    hermitian (c.orbitLift u) (c.orbitLift v) = hermitian u v := by
  classical
  simp only [hermitian, orbitLift_apply, map_sum, map_mul, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  simp [c.orbit_injective.eq_iff]

theorem modularOperator_basis (y : Fin c.dimension) :
    c.modularOperator (basis y) = basis (c.registerPerm y) := by
  funext z
  simp [modularOperator, basis, Equiv.symm_apply_eq]

end Parameters

/-- Fourier eigen-coordinates on the orbit, before embedding into the target. -/
def wave (r : ℕ) (s : Fin r) : Fin r → ℂ := inverseQFT r (basis s)

theorem wave_apply (r : ℕ) (s k : Fin r) :
    wave r s k = scale r * conj (kernel r k s) := by
  classical
  simp [wave, inverseQFT, basis]

theorem wave_orthonormal (hr : 0 < r) (s t : Fin r) :
    hermitian (wave r s) (wave r t) = if s = t then 1 else 0 := by
  rw [wave, wave, inverse_qft_unitarity hr, basis_inner]

/-- The orbit character is periodic; reducing an exponent does not change it. -/
theorem character_mod (hr : 0 < r) (s k : ℕ) :
    phase (-(k % r : ℕ) * (s : ℝ) / r) = phase (-(k : ℝ) * s / r) := by
  have hdiv : (k : ℝ) = (k % r : ℕ) + (r : ℝ) * (k / r : ℕ) := by
    exact_mod_cast (Nat.mod_add_div k r).symm
  have hn : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : -(k : ℝ) * s / r = -(k % r : ℕ) * (s : ℝ) / r +
      (-((s * (k / r) : ℕ) : ℤ) : ℤ) := by
    simp only [Int.cast_neg, Int.cast_natCast]
    rw [Nat.cast_mul]
    rw [hdiv]
    field_simp
    ring
  rw [he, phase_shift_int]

theorem wave_successor (hr : 0 < r) [NeZero r] (s k : Fin r) :
    wave r s k = phase (s.val / r) * wave r s (k + 1) := by
  rw [wave_apply, wave_apply]
  simp only [kernel, phase_conj]
  have hk : (k + 1 : Fin r).val = (k.val + 1) % r := by
    rw [Fin.val_add]
    change (k.val + 1 % r) % r = _
    rw [Nat.add_mod_mod]
  rw [hk]
  have hm := character_mod hr s.val (k.val + 1)
  simp only [neg_mul, neg_div] at hm
  rw [hm]
  rw [mul_left_comm, ← phase_add]
  congr 1
  push_cast
  congr 1
  ring

theorem wave_decomposition (hr : 0 < r) [NeZero r] :
    scale r • (∑ s : Fin r, wave r s) = basis (0 : Fin r) := by
  funext k
  have h := congrFun (inverse_qft_qft hr (basis (0 : Fin r))) k
  simpa [inverseQFT, QFT, basis, wave_apply, Finset.mul_sum, mul_assoc,
    mul_left_comm, mul_comm, kernel] using h

namespace Parameters
variable (c : Parameters)
def eigenstate (s : Fin c.period) : TargetState c.dimension := c.orbitLift (wave c.period s)

theorem shor_eigenstates_orthonormal (s t : Fin c.period) :
    hermitian (c.eigenstate s) (c.eigenstate t) = if s = t then 1 else 0 := by
  rw [eigenstate, eigenstate, c.orbitLift_inner, wave_orthonormal c.period_pos]

theorem shor_eigenstate_action (s : Fin c.period) :
    c.modularOperator (c.eigenstate s) = phase (s.val / c.period) • c.eigenstate s := by
  change c.modularOperator (∑ k, wave c.period s k • basis (c.orbit k)) = _
  rw [map_sum]
  simp_rw [map_smul, c.modularOperator_basis, c.registerPerm_orbit]
  change (∑ k, wave c.period s k • basis (c.orbit (c.successor k))) = _
  calc
    _ = ∑ k, (phase (s.val / c.period) * wave c.period s (c.successor k)) •
        basis (c.orbit (c.successor k)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [wave_successor c.period_pos s k]
      rfl
    _ = _ := by
      rw [Equiv.sum_comp c.successor (fun k =>
        (phase (s.val / c.period) * wave c.period s k) • basis (c.orbit k))]
      simp [eigenstate, orbitLift, Finset.smul_sum, smul_smul]

theorem orbitLift_basis (k : Fin c.period) :
    c.orbitLift (basis k) = basis (c.orbit k) := by
  classical
  change (∑ i, (if i = k then (1 : ℂ) else 0) • basis (c.orbit i)) = _
  simp only [ite_smul, one_smul, zero_smul]
  simp

def input : TargetState c.dimension :=
  basis ⟨1, (lt_of_lt_of_le (by have := c.modulus_ge_two; omega) c.fits)⟩

theorem orbit_zero : c.orbit (0 : Fin c.period) =
    ⟨1, (lt_of_lt_of_le (by have := c.modulus_ge_two; omega) c.fits)⟩ := by
  apply Fin.ext
  simp only [orbit, Fin.val_zero, pow_zero]
  rw [ZMod.val_one_eq_one_mod]
  apply Nat.mod_eq_of_lt
  have := c.modulus_ge_two
  omega

theorem shor_input_state_decomposition :
    c.input = scale c.period • (∑ s, c.eigenstate s) := by
  have h := congrArg c.orbitLift (wave_decomposition c.period_pos)
  rw [map_smul, map_sum, c.orbitLift_basis, c.orbit_zero] at h
  exact h.symm

theorem orbitLift_norm (v : Fin c.period → ℂ) :
    normSquared (c.orbitLift v) = normSquared v := by
  have h := c.orbitLift_inner v v
  rw [hermitian_self, hermitian_self] at h
  exact_mod_cast h

theorem eigenstate_normalized (s : Fin c.period) : normSquared (c.eigenstate s) = 1 := by
  have h := c.shor_eigenstates_orthonormal s s
  rw [if_pos rfl, hermitian_self] at h
  exact_mod_cast h

/-- A concrete inhabitant of the existing QPE interface, proved from modular arithmetic. -/
def eigenInput (s : Fin c.period) : UnitaryEigenInput c.dimension (s.val / c.period) where
  operator := c.modularOperator
  target := c.eigenstate s
  unitary := c.modularOperator_unitary
  normalized := c.eigenstate_normalized s
  eigenstate := c.shor_eigenstate_action s

end Parameters

theorem wave_synthesis (v : Fin r → ℂ) :
    (∑ s : Fin r, v s • wave r s) = inverseQFT r v := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, wave_apply, inverseQFT,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Linearity in the target input of the actual circuit, at each output coordinate. -/
def qpeLinear (U : TargetOperator d) (n : ℕ) (y : Fin (2 ^ n)) : TargetOperator d where
  toFun ψ := runQPE U n ψ y
  map_add' u v := by
    funext t
    simp [runQPE, inverseControl, inverseQFT, runControlled, prepareControl,
      smul_add, map_add, mul_add, Finset.sum_add_distrib]
  map_smul' z v := by
    funext t
    simp [runQPE, inverseControl, inverseQFT, runControlled, prepareControl,
      smul_smul, map_smul, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem scale_norm_square (_hr : 0 < r) : ‖scale r‖ ^ 2 = (r : ℝ)⁻¹ := by
  simp [scale, norm_inv, Complex.norm_real, Real.norm_eq_abs, inv_pow,
    sq_abs, Real.sq_sqrt (Nat.cast_nonneg r)]

namespace Parameters
variable (c : Parameters)
theorem eigenstate_synthesis (v : Fin c.period → ℂ) :
    (∑ s, v s • c.eigenstate s) = c.orbitLift (inverseQFT c.period v) := by
  rw [← wave_synthesis, map_sum]
  simp [map_smul, eigenstate]

theorem eigenstate_synthesis_norm (v : Fin c.period → ℂ) :
    normSquared (∑ s, v s • c.eigenstate s) = normSquared v := by
  rw [c.eigenstate_synthesis, c.orbitLift_norm, inverse_qft_norm c.period_pos]

theorem shor_qpe_output (n : ℕ) (y : Fin (2 ^ n)) :
    runQPE c.modularOperator n c.input y = scale c.period •
      ∑ s, amplitude (2 ^ n) (s.val / c.period) y • c.eigenstate s := by
  change qpeLinear c.modularOperator n y c.input = _
  rw [c.shor_input_state_decomposition, map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  exact congrFun (qpe_amplitude_derivation c.modularOperator n (c.eigenstate s)
    (s.val / c.period) (c.shor_eigenstate_action s)) y

theorem shor_qpe_probability_mixture (n : ℕ) (y : Fin (2 ^ n)) :
    normSquared (runQPE c.modularOperator n c.input y) =
      (c.period : ℝ)⁻¹ * ∑ s : Fin c.period, probability (2 ^ n) (s.val / c.period) y := by
  rw [c.shor_qpe_output, target_norm_smul, Complex.normSq_eq_norm_sq,
    scale_norm_square c.period_pos,
    c.eigenstate_synthesis_norm]
  simp only [normSquared, probability, Complex.normSq_eq_norm_sq]

theorem shor_phase_accuracy_bound (n : ℕ) (s : Fin c.period)
    (b : Fin (2 ^ n))
    (hb : Nearest (2 ^ n) (s.val / c.period) b) :
    4 / Real.pi ^ 2 ≤ probability (2 ^ n) (s.val / c.period) b :=
  qpe_arbitrary_phase_lower_bound _ (by positivity) _ _ hb

/-- Norm of the actual computational input; the order is not needed to prepare it. -/
theorem input_normalized : normSquared c.input = 1 := by
  classical
  simp [input, normSquared, basis]

theorem shor_distribution_normalized (n : ℕ) :
    (∑ y : Fin (2 ^ n), normSquared (runQPE c.modularOperator n c.input y)) = 1 := by
  simp_rw [c.shor_qpe_probability_mixture]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp [qpe_probability_normalized (by positivity : 0 < 2 ^ n), c.period_pos.ne']

theorem shor_component_exact (n : ℕ) (s : Fin c.period) (x y : Fin (2 ^ n))
    (hphase : (s.val : ℝ) / c.period = x.val / (2 ^ n : ℕ)) :
    normSquared (runQPE c.modularOperator n (c.eigenstate s) y) =
      if y = x then 1 else 0 := by
  have h := qpe_joint_distribution (c.eigenInput s) n y
  change normSquared (runQPE c.modularOperator n (c.eigenstate s) y) = _ at h
  rw [h, hphase]
  exact qpe_exact_probability (by positivity) x y

theorem shor_component_nearest_success (n : ℕ) (s : Fin c.period) :
    4 / Real.pi ^ 2 ≤ normSquared (runQPE c.modularOperator n (c.eigenstate s)
      (nearestSample (2 ^ n) (by positivity) (s.val / c.period))) :=
  qpe_nearest_sample_success (c.eigenInput s) n

/-- An individual component carries weight 1/r in the actual marginal mixture. -/
theorem shor_mixture_peak_lower_bound (n : ℕ) (s : Fin c.period) (b : Fin (2 ^ n))
    (hb : Nearest (2 ^ n) (s.val / c.period) b) :
    (c.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) ≤
      normSquared (runQPE c.modularOperator n c.input b) := by
  rw [c.shor_qpe_probability_mixture]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (c.shor_phase_accuracy_bound n s b hb).trans
    (Finset.single_le_sum (fun t _ => sq_nonneg ‖amplitude (2 ^ n) (t.val / c.period) b‖)
      (Finset.mem_univ s))

theorem shor_period_modulo : c.base ^ c.period % c.modulus = 1 := by
  have h := congrArg ZMod.val c.period_power
  rw [← Nat.cast_pow, ZMod.val_natCast, ZMod.val_one_eq_one_mod] at h
  rw [Nat.mod_eq_of_lt (show 1 < c.modulus by have := c.modulus_ge_two; omega)] at h
  exact h

theorem shor_powers_distinct_modulo {k l : ℕ} (hk : k < c.period) (hl : l < c.period) :
    c.base ^ k % c.modulus = c.base ^ l % c.modulus ↔ k = l := by
  rw [← ZMod.val_natCast c.modulus, ← ZMod.val_natCast c.modulus,
    Nat.cast_pow, Nat.cast_pow, (ZMod.val_injective c.modulus).eq_iff]
  exact c.powers_distinct hk hl

/-- The explicit inverse acts by the inverse permutation; no oracle is assumed. -/
def inverseOperator : TargetOperator c.dimension where
  toFun v := fun y => v (c.registerPerm y)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem modularOperator_inverse (v : TargetState c.dimension) :
    c.inverseOperator (c.modularOperator v) = v ∧
    c.modularOperator (c.inverseOperator v) = v := by
  constructor <;> funext y <;> simp [inverseOperator, modularOperator]

/-- An explicit exponential-sum description of the constructed eigenstate. -/
theorem shor_eigenstate_formula (s : Fin c.period) (y : Fin c.dimension) :
    c.eigenstate s y = scale c.period * ∑ k : Fin c.period,
      phase (-(s.val : ℝ) * k.val / c.period) *
        (if y = c.orbit k then 1 else 0) := by
  rw [eigenstate, c.orbitLift_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [wave_apply, kernel, phase_conj, mul_assoc]
  congr 2
  congr 1
  ring

end Parameters

/-- Reviewed obligations for the finite, padded modular-multiplication model. -/
structure QuantumShorOrderFindingSuite : Prop where
  positive_order : ∀ c : Parameters, 0 < c.period
  order_modulo : ∀ c : Parameters, c.base ^ c.period % c.modulus = 1
  distinct_powers : ∀ (c : Parameters) (k l : ℕ), k < c.period → l < c.period →
    (c.base ^ k % c.modulus = c.base ^ l % c.modulus ↔ k = l)
  permutation_low : ∀ (c : Parameters) (y : Fin c.dimension), y.val < c.modulus →
    (c.registerPerm y).val = (c.base * y.val) % c.modulus
  permutation_high : ∀ (c : Parameters) (y : Fin c.dimension), c.modulus ≤ y.val →
    c.registerPerm y = y
  inverse : ∀ (c : Parameters) (v : TargetState c.dimension),
    c.inverseOperator (c.modularOperator v) = v ∧ c.modularOperator (c.inverseOperator v) = v
  unitary : ∀ c : Parameters, IsUnitary c.modularOperator
  orthonormal : ∀ (c : Parameters) (s t : Fin c.period),
    hermitian (c.eigenstate s) (c.eigenstate t) = if s = t then 1 else 0
  eigen_action : ∀ (c : Parameters) (s : Fin c.period),
    c.modularOperator (c.eigenstate s) = phase (s.val / c.period) • c.eigenstate s
  decomposition : ∀ c : Parameters, c.input = scale c.period • ∑ s, c.eigenstate s
  mixture : ∀ (c : Parameters) n (y : Fin (2 ^ n)),
    normSquared (runQPE c.modularOperator n c.input y) =
      (c.period : ℝ)⁻¹ * ∑ s : Fin c.period, probability (2 ^ n) (s.val / c.period) y
  normalized : ∀ (c : Parameters) n,
    (∑ y : Fin (2 ^ n), normSquared (runQPE c.modularOperator n c.input y)) = 1
  exact_component : ∀ (c : Parameters) n (s : Fin c.period) (x y : Fin (2 ^ n)),
    (s.val : ℝ) / c.period = x.val / (2 ^ n : ℕ) →
    normSquared (runQPE c.modularOperator n (c.eigenstate s) y) = if y = x then 1 else 0
  component_accuracy : ∀ (c : Parameters) n (s : Fin c.period) (b : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / c.period) b →
    4 / Real.pi ^ 2 ≤ probability (2 ^ n) (s.val / c.period) b
  mixture_peak : ∀ (c : Parameters) n (s : Fin c.period) (b : Fin (2 ^ n)),
    Nearest (2 ^ n) (s.val / c.period) b →
    (c.period : ℝ)⁻¹ * (4 / Real.pi ^ 2) ≤ normSquared (runQPE c.modularOperator n c.input b)

theorem quantum_shor_order_finding_master_suite : QuantumShorOrderFindingSuite where
  positive_order := Parameters.period_pos
  order_modulo := Parameters.shor_period_modulo
  distinct_powers c _ _ := c.shor_powers_distinct_modulo
  permutation_low := Parameters.registerPerm_low
  permutation_high := Parameters.registerPerm_high
  inverse := Parameters.modularOperator_inverse
  unitary := Parameters.modularOperator_unitary
  orthonormal := Parameters.shor_eigenstates_orthonormal
  eigen_action := Parameters.shor_eigenstate_action
  decomposition := Parameters.shor_input_state_decomposition
  mixture := Parameters.shor_qpe_probability_mixture
  normalized := Parameters.shor_distribution_normalized
  exact_component := Parameters.shor_component_exact
  component_accuracy := Parameters.shor_phase_accuracy_bound
  mixture_peak := Parameters.shor_mixture_peak_lower_bound

end QuantumShorOrderFindingCore
