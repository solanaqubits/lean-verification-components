/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Logic.Equiv.Fin.Basic

/-! Independent normative definitions for module 190. No candidate imports.
The contract fixes coordinates, normalization, pair ordering and Kraus operators.
It is a reviewed specification, not a decision procedure for human intent. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
namespace QuantumQutritDecoderSpec
abbrev Q (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

def forward (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (p.2 - p.1, 2 * p.2 - p.1)
def backward (p : Fin 3 × Fin 3) : Fin 3 × Fin 3 := (p.2 - 2 * p.1, p.2 - p.1)
def pair {a b : ℕ} (i : Fin a) (j : Fin b) : Fin (a * b) := finProdFinEquiv (i,j)
def amplitude : ℂ := ((Real.sqrt 3)⁻¹ : ℝ)
def decoder : Q 9 := fun y x =>
  if y = finProdFinEquiv (forward (finProdFinEquiv.symm x)) then 1 else 0

def code : Matrix (Fin 27) (Fin 3) ℂ := fun x s =>
  let uv := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).symm x
  let ab := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv.1
  if ab.2 = ab.1 + s ∧ uv.2 = ab.1 + 2 * s then amplitude else 0

def regroupIndex (q : Fin 3) (x : Fin 27) : Fin 27 :=
  let uv := (finProdFinEquiv : Fin 9 × Fin 3 ≃ Fin 27).symm x
  let ab := (finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv.1
  if q = 0 then pair (pair uv.2 ab.1) ab.2
  else if q = 1 then pair (pair ab.2 uv.2) ab.1 else pair (pair ab.1 ab.2) uv.2

def retainedPair (q : Fin 3) (Y : Q 27) : Q 9 := fun i j =>
  ∑ w : Fin 3, Y (regroupIndex q (pair i w)) (regroupIndex q (pair j w))

def discard (t : Fin 3) : Matrix (Fin 3) (Fin 9) ℂ :=
  fun i x => if pair i t = x then 1 else 0

def kraus (t : Fin 3) : Matrix (Fin 3) (Fin 9) ℂ := discard t * decoder

theorem inverse_witness : Function.LeftInverse backward forward := by decide
/-- A separate nine-entry expected table; labels use pair-major flat ordering. -/
def expectedTable : Fin 9 → Fin 9 := ![0,5,7,8,1,3,4,6,2]

theorem table_witness (x : Fin 9) :
    finProdFinEquiv (forward (finProdFinEquiv.symm x)) = expectedTable x := by
  revert x
  decide
end QuantumQutritDecoderSpec
