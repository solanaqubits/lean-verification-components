/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional scalar formulas and a prescribed two-component partition

This is an algebraic model of the supplied HCTK curves, not a physical derivation.
The integer label is copied by an explicit transition; no Chern class, quantum
state, Casimir geometry, vacuum transport or consciousness model is constructed.
The regularized reciprocal is bounded, unlike the ideal positive-domain one.
-/

namespace HCTKScalarPartition

noncomputable section

/-- Positive real constants and scales; no empirical calibration is asserted. -/
structure Parameters where
  c : ℝ
  grav : ℝ
  hbar : ℝ
  boltzmann : ℝ
  tau : ℝ
  radius : ℝ
  c_pos : 0 < c
  grav_pos : 0 < grav
  hbar_pos : 0 < hbar
  boltzmann_pos : 0 < boltzmann
  tau_pos : 0 < tau
  radius_pos : 0 < radius

/-- Prescribed frequency-shaped scalar function. -/
def frequency (p : Parameters) (chi : ℝ) : ℝ := Real.exp chi / p.tau

/-- Prescribed metric-shaped scalar, dimensionless only for a mass-valued amount. -/
def metricScalar (p : Parameters) (amount : ℝ) : ℝ :=
  p.grav * amount / (p.c ^ 2 * p.radius)

/-- Schwarzschild-temperature-shaped formula, without a black-hole model. -/
def temperature (p : Parameters) (mass : ℝ) : ℝ :=
  p.hbar * p.c ^ 3 / (8 * Real.pi * p.grav * mass * p.boltzmann)

/-- Entropy-bound-shaped expression in bits; not an attainable capacity theorem. -/
def informationBound (p : Parameters) (energy : ℝ) : ℝ :=
  2 * Real.pi * energy * p.radius / (p.hbar * p.c * Real.log 2)

/-- A positive time scale makes the prescribed frequency strictly positive. -/
theorem frequency_pos (p : Parameters) (chi : ℝ) : 0 < frequency p chi :=
  div_pos (Real.exp_pos chi) p.tau_pos

/-- Positivity of the metric-shaped expression for a positive scalar amount. -/
theorem metricScalar_pos (p : Parameters) (amount : ℝ) (hq : 0 < amount) :
    0 < metricScalar p amount := by
  exact div_pos (mul_pos p.grav_pos hq) (mul_pos (pow_pos p.c_pos _) p.radius_pos)

/-- Linear scaling is a real identity, not a claim about rounded products. -/
theorem metricScalar_scale (p : Parameters) (q k : ℝ) :
    metricScalar p (k * q) = k * metricScalar p q := by
  unfold metricScalar
  ring

/-- Positive mass makes the prescribed temperature strictly positive. -/
theorem temperature_pos (p : Parameters) (mass : ℝ) (hm : 0 < mass) :
    0 < temperature p mass := by
  exact div_pos (mul_pos p.hbar_pos (pow_pos p.c_pos _))
    (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) p.grav_pos) hm)
      p.boltzmann_pos)

/-- Inverse mass scaling for a strictly positive scaling factor. -/
theorem temperature_scale (p : Parameters) (mass k : ℝ) (hm : 0 < mass) (hk : 0 < k) :
    temperature p (k * mass) = temperature p mass / k := by
  unfold temperature
  field_simp

/-- The bound-shaped scalar is nonnegative at nonnegative energy. -/
theorem informationBound_nonneg (p : Parameters) (energy : ℝ) (he : 0 ≤ energy) :
    0 ≤ informationBound p energy := by
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  exact div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) he) p.radius_pos.le)
    (mul_pos (mul_pos p.hbar_pos p.c_pos) hl).le

/-- Energy scaling for the prescribed expression. -/
theorem informationBound_scale (p : Parameters) (energy k : ℝ) :
    informationBound p (k * energy) = k * informationBound p energy := by
  unfold informationBound
  ring

/-- Two scalar components and an integer bookkeeping label, not a topological class. -/
structure State where
  localAmount : ℝ
  reservoirAmount : ℝ
  label : ℤ

/-- Total scalar amount. -/
def total (s : State) : ℝ := s.localAmount + s.reservoirAmount

/-- Explicit partition by a prescribed real fraction. -/
def partition (q power : ℝ) (label : ℤ) : State :=
  ⟨q * power, q * (1 - power), label⟩

/-- Conservation follows by ring arithmetic from this construction. -/
theorem partition_total (q power : ℝ) (label : ℤ) : total (partition q power label) = q := by
  unfold total partition
  ring

/-- Both components lie in the allowed range under admissible signs. -/
theorem partition_bounds (q power : ℝ) (label : ℤ)
    (hq : 0 ≤ q) (hp : 0 ≤ power) (hp1 : power ≤ 1) :
    0 ≤ (partition q power label).localAmount ∧
    (partition q power label).localAmount ≤ q ∧
    0 ≤ (partition q power label).reservoirAmount ∧
    (partition q power label).reservoirAmount ≤ q := by
  dsimp [partition]
  constructor
  · exact mul_nonneg hq hp
  constructor
  · nlinarith
  constructor
  · exact mul_nonneg hq (sub_nonneg.mpr hp1)
  · nlinarith

/-- The stopped endpoint is specified, not discovered by simulation. -/
theorem partition_stopped (q : ℝ) (label : ℤ) : partition q 0 label = ⟨0, q, label⟩ := by
  simp [partition]

/-- The powered endpoint has no reservoir component. -/
theorem partition_powered (q : ℝ) (label : ℤ) : partition q 1 label = ⟨q, 0, label⟩ := by
  simp [partition]

/-- Increasing the prescribed fraction increases the local component. -/
theorem local_monotone (q p₀ p₁ : ℝ) (label : ℤ) (hq : 0 ≤ q) (hp : p₀ ≤ p₁) :
    (partition q p₀ label).localAmount ≤ (partition q p₁ label).localAmount :=
  mul_le_mul_of_nonneg_left hp hq

/-- Explicit transfer from one scalar component to the other. -/
def transfer (s : State) (amount : ℝ) : State :=
  ⟨s.localAmount - amount, s.reservoirAmount + amount, s.label⟩

/-- An actual transition identity; conservation is not a premise. -/
theorem transfer_total (s : State) (amount : ℝ) : total (transfer s amount) = total s := by
  unfold total transfer
  ring

/-- The label remains unchanged because this transition copies it. -/
theorem transfer_label (s : State) (amount : ℝ) : (transfer s amount).label = s.label := rfl

/-- Nonnegative components require an admissible transfer size. -/
theorem transfer_nonneg (s : State) (amount : ℝ)
    (hr : 0 ≤ s.reservoirAmount) (ha : 0 ≤ amount) (hal : amount ≤ s.localAmount) :
    0 ≤ (transfer s amount).localAmount ∧ 0 ≤ (transfer s amount).reservoirAmount :=
  ⟨sub_nonneg.mpr hal, add_nonneg hr ha⟩

/-- Execute a finite prescribed transfer trace. -/
def runTransfers : State → List ℝ → State
  | s, [] => s
  | s, a :: rest => runTransfers (transfer s a) rest

/-- Induction extends the two invariants to every finite transfer trace. -/
theorem runTransfers_invariants (amounts : List ℝ) (s : State) :
    total (runTransfers s amounts) = total s ∧ (runTransfers s amounts).label = s.label := by
  induction amounts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons a rest ih =>
    obtain ⟨ht, hl⟩ := ih (transfer s a)
    exact ⟨ht.trans (transfer_total s a), hl.trans (transfer_label s a)⟩

/-- Regularized reciprocal; admissible use requires a positive denominator. -/
def regularizedWindow (tau epsilon power : ℝ) : ℝ := tau / (power + epsilon)

/-- Positive regularization gives a finite cap, including at zero power. -/
theorem regularizedWindow_bounds (tau epsilon power : ℝ)
    (ht : 0 < tau) (he : 0 < epsilon) (hp : 0 ≤ power) :
    0 < regularizedWindow tau epsilon power ∧
    regularizedWindow tau epsilon power ≤ tau / epsilon := by
  have hd : 0 < power + epsilon := by linarith
  exact ⟨div_pos ht hd, div_le_div_of_nonneg_left ht.le he (by linarith)⟩

/-- The cap is attained at the stopped endpoint. -/
theorem regularizedWindow_stopped (tau epsilon : ℝ) :
    regularizedWindow tau epsilon 0 = tau / epsilon := by simp [regularizedWindow]

/-- Refining power downward increases the regularized reciprocal. -/
theorem regularizedWindow_antitone (tau epsilon p₀ p₁ : ℝ)
    (ht : 0 ≤ tau) (he : 0 < epsilon) (hp : 0 ≤ p₀) (horder : p₀ ≤ p₁) :
    regularizedWindow tau epsilon p₁ ≤ regularizedWindow tau epsilon p₀ := by
  exact div_le_div_of_nonneg_left ht (by linarith) (by linarith)

/-- Even within the unit power interval the ideal reciprocal has arbitrarily large values. -/
theorem idealWindow_unbounded (tau bound : ℝ) (ht : 0 < tau) (hb : 0 < bound) :
    ∃ power : ℝ, 0 < power ∧ power ≤ 1 ∧ tau / power > bound := by
  have hf : 0 < tau / (2 * bound) := div_pos ht (by positivity)
  have hd : 0 < min 1 (tau / (2 * bound)) := lt_min (by norm_num) hf
  refine ⟨min 1 (tau / (2 * bound)), hd, min_le_left _ _, ?_⟩
  apply (lt_div_iff₀ hd).mpr
  have heq : bound * (tau / (2 * bound)) = tau / 2 := by field_simp
  have hm := mul_le_mul_of_nonneg_left (min_le_right (1 : ℝ) (tau / (2 * bound))) hb.le
  rw [heq] at hm
  linarith

/-- Registry package of conditional scalar results; no physical/topological invariant. -/
structure HCTKScalarPartitionSuite : Prop where
  partition_conservation : ∀ q p n, total (partition q p n) = q
  component_bounds : ∀ q p n, 0 ≤ q → 0 ≤ p → p ≤ 1 →
    0 ≤ (partition q p n).localAmount ∧ (partition q p n).localAmount ≤ q ∧
    0 ≤ (partition q p n).reservoirAmount ∧ (partition q p n).reservoirAmount ≤ q
  transfer_conservation : ∀ s a, total (transfer s a) = total s
  trace_invariants : ∀ xs s, total (runTransfers s xs) = total s ∧
    (runTransfers s xs).label = s.label
  regularization_bound : ∀ tau eps p, 0 < tau → 0 < eps → 0 ≤ p →
    0 < regularizedWindow tau eps p ∧ regularizedWindow tau eps p ≤ tau / eps
  ideal_unbounded : ∀ tau bound, 0 < tau → 0 < bound →
    ∃ p : ℝ, 0 < p ∧ p ≤ 1 ∧ tau / p > bound

theorem verification_suite : HCTKScalarPartitionSuite :=
  ⟨partition_total, partition_bounds, transfer_total, runTransfers_invariants,
    regularizedWindow_bounds, idealWindow_unbounded⟩

end
end HCTKScalarPartition
