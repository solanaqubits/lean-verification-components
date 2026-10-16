/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumNoBroadcastingMixed
import Verification.QuantumChannelTraceDistanceContract
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Finite Kraus channels, their dual effects, and trace-distance contraction.
Complete positivity uses every finite block amplification from the existing channel API.
No numerical diagonalization or physical implementation is asserted. -/
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
open QuantumPOVMNaimarkDilation QuantumPOVMInformationEntropy QuantumHelstromStateDiscrimination
open QuantumChannelTraceDistanceContract
namespace QuantumCPTPChannelContract
variable {d e r : ℕ}

/-- Rectangular Kraus operators allow distinct input and output dimensions. -/
structure KrausChannel (d e r : ℕ) where
  operators : Fin r → Matrix (Fin e) (Fin d) ℂ
  complete : ∑ j, (operators j).conjTranspose * operators j = 1

def KrausChannel.toChannel (K : KrausChannel d e r) :
    QuantumNoBroadcastingMixed.Channel (Fin d) (Fin e) :=
  QuantumNoBroadcastingMixed.krausChannel K.operators K.complete

def apply_channel (K : KrausChannel d e r) : Q d →ₗ[ℂ] Q e := K.toChannel.toLinearMap

theorem apply_channel_eq (K : KrausChannel d e r) (X : Q d) :
    apply_channel K X = ∑ j, K.operators j * X * (K.operators j).conjTranspose := rfl

theorem channel_add (K : KrausChannel d e r) (X Y : Q d) :
    apply_channel K (X + Y) = apply_channel K X + apply_channel K Y := map_add _ _ _

theorem channel_smul (K : KrausChannel d e r) (z : ℂ) (X : Q d) :
    apply_channel K (z • X) = z • apply_channel K X := map_smul _ _ _

theorem channel_trace_preserving (K : KrausChannel d e r) (X : Q d) :
    (apply_channel K X).trace = X.trace := K.toChannel.trace_preserving X

theorem channel_completely_positive (K : KrausChannel d e r) :
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel K) :=
  K.toChannel.completely_positive

theorem channel_positive (K : KrausChannel d e r) {X : Q d} (hX : X.PosSemidef) :
    (apply_channel K X).PosSemidef := K.toChannel.positive X hX

theorem channel_density (K : KrausChannel d e r) {ρ : Q d} (hρ : Density ρ) :
    Density (apply_channel K ρ) := K.toChannel.density_preserved ρ hρ

/-- The Heisenberg dual acts on output observables. -/
def dual_channel (K : KrausChannel d e r) : Q e →ₗ[ℂ] Q d :=
  QuantumNoBroadcastingMixed.krausMap (fun j => (K.operators j).conjTranspose)

theorem dual_channel_eq (K : KrausChannel d e r) (E : Q e) :
    dual_channel K E = ∑ j, (K.operators j).conjTranspose * E * K.operators j := by
  simp [dual_channel, QuantumNoBroadcastingMixed.krausMap]

theorem dual_unital (K : KrausChannel d e r) : dual_channel K 1 = 1 := by
  simpa [dual_channel_eq] using K.complete

theorem dual_positive (K : KrausChannel d e r) {E : Q e} (hE : E.PosSemidef) :
    (dual_channel K E).PosSemidef := by
  rw [dual_channel_eq]
  exact Matrix.posSemidef_sum _ fun j _ => hE.conjTranspose_mul_mul_same _

theorem trace_adjoint_identity (K : KrausChannel d e r) (E : Q e) (X : Q d) :
    (E * apply_channel K X).trace = (dual_channel K E * X).trace := by
  rw [apply_channel_eq, dual_channel_eq, Finset.mul_sum, Finset.sum_mul,
    Matrix.trace_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.mul_assoc]

def pullback_effect (K : KrausChannel d e r) (E : Effect e) : Effect d where
  matrix := dual_channel K E.matrix
  positive := dual_positive K E.positive
  complement := by
    have h := dual_positive K E.complement
    simpa only [map_sub, dual_unital] using h

/-- Contractivity is obtained by pulling back the attained output effect. -/
theorem trace_distance_contractive (K : KrausChannel d e r) {ρ σ : Q d}
    (hρ : Density ρ) (hσ : Density σ) :
    trace_distance (apply_channel K ρ) (apply_channel K σ) ≤ trace_distance ρ σ := by
  let E := distance_effect (channel_density K hρ) (channel_density K hσ)
  have h := trace_distance_effect_bound hρ hσ (pullback_effect K E)
  have ha := distance_effect_attains (channel_density K hρ) (channel_density K hσ)
  change (E.matrix * (apply_channel K ρ - apply_channel K σ)).trace.re = _ at ha
  rw [← map_sub, trace_adjoint_identity] at ha
  change |(dual_channel K E.matrix * (ρ - σ)).trace.re| ≤ _ at h
  rw [ha, abs_of_nonneg (trace_distance_nonneg (channel_density K hρ)
    (channel_density K hσ))] at h
  exact h

theorem trace_norm_contractive (K : KrausChannel d e r) {ρ σ : Q d}
    (hρ : Density ρ) (hσ : Density σ) :
    trace_norm (apply_channel K ρ - apply_channel K σ) ≤ trace_norm (ρ - σ) := by
  have h := trace_distance_contractive K hρ hσ
  unfold trace_distance at h
  linarith

/-- Equal-prior discrimination cannot improve after a quantum channel. -/
theorem optimal_success_contractive (K : KrausChannel d e r) {ρ σ : Q d}
    (hρ : Density ρ) (hσ : Density σ) :
    optimal_success Examples.fair (apply_channel K ρ) (apply_channel K σ) ≤
      optimal_success Examples.fair ρ σ := by
  rw [trace_distance_helstrom_link (channel_density K hρ) (channel_density K hσ),
    trace_distance_helstrom_link hρ hσ]
  linarith [trace_distance_contractive K hρ hσ]

/-- Abstract CPTP maps from the existing block-amplification API are also covered.
This second proof needs only positivity and trace preservation. -/
theorem cptp_trace_distance_contractive
    (F : QuantumNoBroadcastingMixed.Channel (Fin d) (Fin e)) {ρ σ : Q d}
    (hρ : Density ρ) (hσ : Density σ) :
    trace_distance (F.toLinearMap ρ) (F.toLinearMap σ) ≤ trace_distance ρ σ := by
  let hA := hρ.1.isHermitian.sub hσ.1.isHermitian
  let E := distance_effect (F.density_preserved ρ hρ) (F.density_preserved σ hσ)
  have hp := effect_trace_le E (F.positive _ (positive_part_positive hA))
  have hn := trace_product_nonneg E.positive (F.positive _ (negative_part_positive hA))
  rw [F.trace_preserving, traceless_positive_trace hA (difference_traceless hρ hσ)] at hp
  have ha := distance_effect_attains (F.density_preserved ρ hρ) (F.density_preserved σ hσ)
  change (E.matrix * (F.toLinearMap ρ - F.toLinearMap σ)).trace.re = _ at ha
  rw [← map_sub, ← parts_sub hA, map_sub, mul_sub, Matrix.trace_sub, Complex.sub_re] at ha
  change (E.matrix * F.toLinearMap (positive_part hA)).trace.re ≤ trace_distance ρ σ at hp
  linarith

def identity_channel (d : ℕ) : KrausChannel d d 1 where
  operators := fun _ => 1
  complete := by simp

@[simp] theorem identity_channel_apply (X : Q d) : apply_channel (identity_channel d) X = X := by
  simp [apply_channel_eq, identity_channel]

theorem identity_preserves_distance (ρ σ : Q d) :
    trace_distance (apply_channel (identity_channel d) ρ)
      (apply_channel (identity_channel d) σ) = trace_distance ρ σ := by simp

def unitary_channel (U : Matrix.unitaryGroup (Fin d) ℂ) : KrausChannel d d 1 where
  operators := fun _ => U
  complete := by
    simp only [Fin.sum_univ_one]
    exact Unitary.coe_star_mul_self U

@[simp] theorem unitary_channel_apply (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) :
    apply_channel (unitary_channel U) X = (U : Q d) * X * (U : Q d).conjTranspose := by
  simp [apply_channel_eq, unitary_channel]

theorem unitary_inverse_apply (U : Matrix.unitaryGroup (Fin d) ℂ) (X : Q d) :
    apply_channel (unitary_channel (star U)) (apply_channel (unitary_channel U) X) = X := by
  simp only [unitary_channel_apply, Unitary.coe_star, star_star, ← Matrix.star_eq_conjTranspose]
  simp [Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Q d)) (U : Q d)]

theorem unitary_preserves_distance (U : Matrix.unitaryGroup (Fin d) ℂ) {ρ σ : Q d}
    (hρ : Density ρ) (hσ : Density σ) :
    trace_distance (apply_channel (unitary_channel U) ρ)
      (apply_channel (unitary_channel U) σ) = trace_distance ρ σ := by
  apply le_antisymm (trace_distance_contractive _ hρ hσ)
  have h := trace_distance_contractive (unitary_channel (star U))
    (channel_density (unitary_channel U) hρ) (channel_density (unitary_channel U) hσ)
  simpa only [unitary_inverse_apply] using h

/-- Replacement by a fixed basis state, in possibly different output dimension. -/
def reset_channel (v : Fin e) : KrausChannel d e d where
  operators := fun j => Matrix.single v j 1
  complete := by
    ext a b
    simp [Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.single,
      Matrix.one_apply, ite_and, eq_comm]

theorem reset_channel_apply (v : Fin e) (X : Q d) :
    apply_channel (reset_channel v) X = X.trace • QuantumNoBroadcastingMixed.basisProjector v := by
  ext a b
  simp [apply_channel_eq, reset_channel, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.single, QuantumNoBroadcastingMixed.basisProjector, Matrix.diagonal,
    Matrix.trace, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp_all [eq_comm]

theorem reset_density (v : Fin e) {ρ : Q d} (hρ : Density ρ) :
    apply_channel (reset_channel v) ρ = QuantumNoBroadcastingMixed.basisProjector v := by
  rw [reset_channel_apply, hρ.2, one_smul]

theorem reset_distance_zero (v : Fin e) {ρ σ : Q d} (hρ : Density ρ) (hσ : Density σ) :
    trace_distance (apply_channel (reset_channel v) ρ) (apply_channel (reset_channel v) σ) = 0 := by
  rw [reset_density v hρ, reset_density v hσ, trace_distance_self]

/-- Projective dephasing in the computational basis. -/
def dephasing_channel (d : ℕ) : KrausChannel d d d where
  operators := QuantumNoBroadcastingMixed.basisProjector
  complete := by
    ext a b
    simp [Matrix.sum_apply, QuantumNoBroadcastingMixed.basisProjector, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.one_apply, eq_comm]

theorem dephasing_channel_apply (X : Q d) :
    apply_channel (dephasing_channel d) X = Matrix.diagonal (fun i => X i i) := by
  ext a b
  simp [apply_channel_eq, dephasing_channel, QuantumNoBroadcastingMixed.basisProjector,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.diagonal, Matrix.sum_apply,
    apply_ite (starRingEnd ℂ), eq_comm]
  split_ifs <;> simp_all

namespace Regression
open QuantumHelstromStateDiscrimination.Examples

/-- A second pure state with opposite coherence. -/
def rhoMinus : Q 2 := !![1/2, -1/2; -1/2, 1/2]

theorem rhoMinus_density : Density rhoMinus := by
  have heq : rhoMinus = pauliX.effects 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [rhoMinus, pauliX, QuantumPOVMInformationallyComplete.phaseMinus,
        QuantumPOVMInformationallyComplete.blochEffect]
  refine ⟨?_, ?_⟩
  · rw [heq]
    exact pauliX.pos_semidef 1
  · norm_num [rhoMinus, Matrix.trace, Fin.sum_univ_two]

theorem dephasing_identifies_pair :
    apply_channel (dephasing_channel 2) rhoPlus =
      apply_channel (dephasing_channel 2) rhoMinus := by
  rw [dephasing_channel_apply, dephasing_channel_apply]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem dephasing_strict_loss :
    trace_distance (apply_channel (dephasing_channel 2) rhoPlus)
      (apply_channel (dephasing_channel 2) rhoMinus) < trace_distance rhoPlus rhoMinus := by
  rw [dephasing_identifies_pair, trace_distance_self]
  apply lt_of_le_of_ne (trace_distance_nonneg rhoPlus_density rhoMinus_density)
  intro h
  have he := (trace_distance_eq_zero_iff rhoPlus_density rhoMinus_density).mp h.symm
  have hij := congrArg (fun X : Q 2 => X 0 1) he
  norm_num [rhoPlus, rhoMinus] at hij

end Regression
structure QuantumCPTPChannelContractSuite : Prop where
  trace_preserving : ∀ {d e r} (K : KrausChannel d e r) (X : Q d),
    (apply_channel K X).trace = X.trace
  completely_positive : ∀ {d e r} (K : KrausChannel d e r),
    QuantumNoBroadcastingMixed.IsCompletelyPositive (apply_channel K)
  density_preserved : ∀ {d e r} (K : KrausChannel d e r) {ρ : Q d},
    Density ρ → Density (apply_channel K ρ)
  dual_unital : ∀ {d e r} (K : KrausChannel d e r), dual_channel K 1 = 1
  adjoint : ∀ {d e r} (K : KrausChannel d e r) (E : Q e) (X : Q d),
    (E * apply_channel K X).trace = (dual_channel K E * X).trace
  effects : ∀ {d e r} (K : KrausChannel d e r) (E : Effect e),
    (dual_channel K E.matrix).PosSemidef ∧ (1 - dual_channel K E.matrix).PosSemidef
  contractive : ∀ {d e r} (K : KrausChannel d e r) {ρ σ : Q d}, Density ρ → Density σ →
    trace_distance (apply_channel K ρ) (apply_channel K σ) ≤ trace_distance ρ σ
  abstract_cptp : ∀ {d e} (F : QuantumNoBroadcastingMixed.Channel (Fin d) (Fin e))
    {ρ σ : Q d}, Density ρ → Density σ →
    trace_distance (F.toLinearMap ρ) (F.toLinearMap σ) ≤ trace_distance ρ σ
  unitary : ∀ {d} (U : Matrix.unitaryGroup (Fin d) ℂ) {ρ σ : Q d}, Density ρ → Density σ →
    trace_distance (apply_channel (unitary_channel U) ρ)
      (apply_channel (unitary_channel U) σ) = trace_distance ρ σ
  reset : ∀ {d e} (v : Fin e) {ρ σ : Q d}, Density ρ → Density σ →
    trace_distance (apply_channel (reset_channel v) ρ) (apply_channel (reset_channel v) σ) = 0
  strict_loss : trace_distance (apply_channel (dephasing_channel 2) Examples.rhoPlus)
    (apply_channel (dephasing_channel 2) Regression.rhoMinus) <
      trace_distance Examples.rhoPlus Regression.rhoMinus

theorem verification_suite : QuantumCPTPChannelContractSuite where
  trace_preserving := channel_trace_preserving
  completely_positive := channel_completely_positive
  density_preserved := channel_density
  dual_unital := QuantumCPTPChannelContract.dual_unital
  adjoint := trace_adjoint_identity
  effects := fun K E => ⟨(pullback_effect K E).positive, (pullback_effect K E).complement⟩
  contractive := trace_distance_contractive
  abstract_cptp := cptp_trace_distance_contractive
  unitary := unitary_preserves_distance
  reset := reset_distance_zero
  strict_loss := Regression.dephasing_strict_loss

end QuantumCPTPChannelContract
