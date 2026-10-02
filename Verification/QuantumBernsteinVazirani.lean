import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.header false
noncomputable section

namespace QuantumBernsteinVazirani

/-- Four real amplitudes; normalization is not part of the type. -/
@[ext] structure QState4 where
  x00 : ℝ
  x01 : ℝ
  x10 : ℝ
  x11 : ℝ

def dot (u v : QState4) : ℝ :=
  u.x00 * v.x00 + u.x01 * v.x01 + u.x10 * v.x10 + u.x11 * v.x11

def basis00 : QState4 := ⟨1, 0, 0, 0⟩
def basis01 : QState4 := ⟨0, 1, 0, 0⟩
def basis10 : QState4 := ⟨0, 0, 1, 0⟩
def basis11 : QState4 := ⟨0, 0, 0, 1⟩

inductive Mask2 where
  | s00 | s01 | s10 | s11
  deriving DecidableEq, Repr

def maskToBasis (s : Mask2) : QState4 :=
  match s with
  | .s00 => basis00
  | .s01 => basis01
  | .s10 => basis10
  | .s11 => basis11

/-- The explicit real four-dimensional Hadamard transform. -/
def hadamard2 (v : QState4) : QState4 :=
  ⟨(v.x00 + v.x01 + v.x10 + v.x11) / 2,
   (v.x00 - v.x01 + v.x10 - v.x11) / 2,
   (v.x00 + v.x01 - v.x10 - v.x11) / 2,
   (v.x00 - v.x01 - v.x10 + v.x11) / 2⟩

/-- Prescribed phase-sign table for the four masks. -/
def oracle (s : Mask2) (v : QState4) : QState4 :=
  match s with
  | .s00 => ⟨v.x00, v.x01, v.x10, v.x11⟩
  | .s01 => ⟨v.x00, -v.x01, v.x10, -v.x11⟩
  | .s10 => ⟨v.x00, v.x01, -v.x10, -v.x11⟩
  | .s11 => ⟨v.x00, -v.x01, -v.x10, v.x11⟩

/-- Composition containing one oracle application; no query-cost semantics is defined. -/
def bvPipeline (s : Mask2) : QState4 :=
  hadamard2 (oracle s (hadamard2 basis00))

theorem bv_search_00 : bvPipeline Mask2.s00 = basis00 := by
  ext <;> norm_num [bvPipeline, hadamard2, oracle, basis00]

theorem bv_search_01 : bvPipeline Mask2.s01 = basis01 := by
  ext <;> norm_num [bvPipeline, hadamard2, oracle, basis00, basis01]

theorem bv_search_10 : bvPipeline Mask2.s10 = basis10 := by
  ext <;> norm_num [bvPipeline, hadamard2, oracle, basis00, basis10]

theorem bv_search_11 : bvPipeline Mask2.s11 = basis11 := by
  ext <;> norm_num [bvPipeline, hadamard2, oracle, basis00, basis11]

/-- Exact reconstruction for the prescribed real operators and each mask. -/
theorem bv_exact_reconstruction (s : Mask2) : bvPipeline s = maskToBasis s := by
  cases s with
  | s00 => exact bv_search_00
  | s01 => exact bv_search_01
  | s10 => exact bv_search_10
  | s11 => exact bv_search_11

/-- Unit overlap; a probabilistic measurement model is not defined here. -/
theorem bv_success_probability_one (s : Mask2) :
    dot (bvPipeline s) (maskToBasis s) = 1 := by
  rw [bv_exact_reconstruction s]
  cases s <;> norm_num [dot, maskToBasis, basis00, basis01, basis10, basis11]

structure QuantumBernsteinVaziraniFormalSuite : Prop where
  h_find_00 : bvPipeline Mask2.s00 = basis00
  h_find_01 : bvPipeline Mask2.s01 = basis01
  h_find_10 : bvPipeline Mask2.s10 = basis10
  h_find_11 : bvPipeline Mask2.s11 = basis11
  h_universal : ∀ (s : Mask2), bvPipeline s = maskToBasis s
  h_prob_one : ∀ (s : Mask2), dot (bvPipeline s) (maskToBasis s) = 1

theorem quantum_bernstein_vazirani_master_verification_suite :
    QuantumBernsteinVaziraniFormalSuite := {
  h_find_00 := bv_search_00
  h_find_01 := bv_search_01
  h_find_10 := bv_search_10
  h_find_11 := bv_search_11
  h_universal := bv_exact_reconstruction
  h_prob_one := bv_success_probability_one
}

end QuantumBernsteinVazirani
