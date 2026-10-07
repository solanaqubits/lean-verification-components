/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.Complex.BigOperators
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases

/-! Independently reviewed Simon contract. No Verification implementation imports.
The finite witness below establishes satisfiability for a concrete instance only. -/
noncomputable section
open scoped BigOperators ComplexConjugate
namespace QuantumSimonsSpec

abbrev Register (n : ℕ) := Fin n → Bool
abbrev JointState (n m : ℕ) := Register n → Register m → ℂ
abbrev BinarySpace (n : ℕ) := Fin n → ZMod 2

def zeroBits (n : ℕ) : Register n := fun _ => false
def xorVec {n : ℕ} (x y : Register n) : Register n := fun i => x i ^^ y i
def signOfBool (b : Bool) : ℝ := if b then -1 else 1
def character {n : ℕ} (x y : Register n) : ℝ := ∏ i, signOfBool (x i && y i)
def rho (n : ℕ) : ℝ := 1 / Real.sqrt (2 ^ n : ℝ)
def bit (b : Bool) : ZMod 2 := if b then 1 else 0
def encode {n : ℕ} (x : Register n) : BinarySpace n := fun i => bit (x i)
def dot {n : ℕ} (x y : Register n) : ZMod 2 := ∑ i, encode x i * encode y i

def GoldSimonPromise {n m : ℕ} (f : Register n → Register m) (s : Register n) : Prop :=
  s ≠ zeroBits n ∧ ∀ x x', f x = f x' ↔ x = x' ∨ x = xorVec x' s

def hermitian {n m : ℕ} (u v : JointState n m) : ℂ :=
  ∑ x, ∑ z, conj (u x z) * v x z

def xorOracle {n m : ℕ} (f : Register n → Register m) (v : JointState n m) : JointState n m :=
  fun x z => v x (xorVec z (f x))

def inputHadamard {n m : ℕ} (v : JointState n m) : JointState n m :=
  fun y z => (rho n : ℂ) * ∑ x, (character x y : ℂ) * v x z

def initial (n m : ℕ) : JointState n m :=
  fun x z => if x = zeroBits n ∧ z = zeroBits m then 1 else 0

def runSimon {n m : ℕ} (f : Register n → Register m) : JointState n m :=
  inputHadamard (xorOracle f (inputHadamard (initial n m)))

def fiberSum {n m : ℕ} (f : Register n → Register m) (y : Register n) (z : Register m) : ℝ :=
  ∑ x, if f x = z then character x y else 0

def probability {n m : ℕ} (f : Register n → Register m) (y : Register n) : ℝ :=
  ∑ z, Complex.normSq (runSimon f y z)

def rowSpan {n : ℕ} (Y : Finset (Register n)) : Submodule (ZMod 2) (BinarySpace n) :=
  Submodule.span (ZMod 2) (encode '' (Y : Set (Register n)))

def GoldDistribution : Prop := ∀ (n m : ℕ) (f : Register n → Register m) s,
  GoldSimonPromise f s → ∀ y,
    probability f y = if dot y s = 0 then 2 / (2 ^ n : ℝ) else 0

def GoldRecovery : Prop := ∀ (n : ℕ) (s : Register n) (Y : Finset (Register n)),
  s ≠ zeroBits n → (∀ y ∈ Y, dot y s = 0) →
  Module.finrank (ZMod 2) (rowSpan Y) = n - 1 → ∀ v,
    (∀ y ∈ Y, dot y v = 0) ↔ v = zeroBits n ∨ v = s

structure GoldSimonSuite : Prop where
  oracle_unitary : ∀ (n m : ℕ) (f : Register n → Register m),
    (∀ v, xorOracle f (xorOracle f v) = v) ∧
    (∀ u v, hermitian (xorOracle f u) (xorOracle f v) = hermitian u v)
  hadamard_unitary : ∀ (n m : ℕ) (u v : JointState n m),
    inputHadamard (inputHadamard u) = u ∧
      hermitian (inputHadamard u) (inputHadamard v) = hermitian u v
  circuit_amplitude : ∀ (n m : ℕ) (f : Register n → Register m) y z,
    runSimon f y z = ((fiberSum f y z / (2 ^ n : ℝ) : ℝ) : ℂ)
  odd_amplitude : ∀ (n m : ℕ) (f : Register n → Register m) s,
    GoldSimonPromise f s → ∀ y, dot y s = 1 → ∀ z, runSimon f y z = 0
  exact_distribution : GoldDistribution
  normalized : ∀ (n m : ℕ) (f : Register n → Register m), (∑ y, probability f y) = 1
  recovery : GoldRecovery

/-- A two-element input register with the nonzero period 1 and constant output. -/
def witnessFunction : Register 1 → Register 0 := fun _ => zeroBits 0
def witnessPeriod : Register 1 := fun _ => true

theorem witness_period_nonzero : witnessPeriod ≠ zeroBits 1 := by
  intro h
  have h0 := congrFun h 0
  simp [witnessPeriod, zeroBits] at h0

theorem witness_promise : GoldSimonPromise witnessFunction witnessPeriod := by
  refine ⟨witness_period_nonzero, ?_⟩
  intro x y
  constructor
  · intro _
    by_cases h : x 0 = y 0
    · left; funext i; fin_cases i; exact h
    · right
      funext i; fin_cases i
      cases hx : x 0 <;> cases hy : y 0 <;> simp_all [xorVec, witnessPeriod]
  · intro _; rfl

theorem simon_promise_satisfiable :
    ∃ (f : Register 1 → Register 0) (s : Register 1), GoldSimonPromise f s :=
  ⟨witnessFunction, witnessPeriod, witness_promise⟩

/-- For n=1, the empty row set has the required rank 0 and is orthogonal to s. -/
theorem recovery_hypotheses_satisfiable :
    ∃ (s : Register 1) (Y : Finset (Register 1)), s ≠ zeroBits 1 ∧
      (∀ y ∈ Y, dot y s = 0) ∧ Module.finrank (ZMod 2) (rowSpan Y) = 1 - 1 := by
  refine ⟨witnessPeriod, ∅, witness_period_nonzero, by simp, ?_⟩
  have he : encode '' (↑(∅ : Finset (Register 1)) : Set (Register 1)) = ∅ := by
    ext x
    simp
  have hb : rowSpan (∅ : Finset (Register 1)) = ⊥ := by
    unfold rowSpan
    rw [he, Submodule.span_empty]
  have : Subsingleton (rowSpan (∅ : Finset (Register 1))) := by
    rw [hb]
    infer_instance
  exact Module.finrank_zero_of_subsingleton

end QuantumSimonsSpec
