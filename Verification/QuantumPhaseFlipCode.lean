import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumPhaseFlipCode

/-- Explicit real 2-by-2 matrices; no multi-qubit state space is defined here. -/
@[ext] structure RMat2 where
  a11 : ℝ
  a12 : ℝ
  a21 : ℝ
  a22 : ℝ

def rmatZero : RMat2 := ⟨0, 0, 0, 0⟩
def rmatI : RMat2 := ⟨1, 0, 0, 1⟩

def radd (A B : RMat2) : RMat2 :=
  ⟨A.a11 + B.a11, A.a12 + B.a12, A.a21 + B.a21, A.a22 + B.a22⟩

def rsmul (c : ℝ) (A : RMat2) : RMat2 :=
  ⟨c * A.a11, c * A.a12, c * A.a21, c * A.a22⟩

def rmul (A B : RMat2) : RMat2 :=
  ⟨A.a11 * B.a11 + A.a12 * B.a21, A.a11 * B.a12 + A.a12 * B.a22,
   A.a21 * B.a11 + A.a22 * B.a21, A.a21 * B.a12 + A.a22 * B.a22⟩

def pauliX : RMat2 := ⟨0, 1, 1, 0⟩
def pauliZ : RMat2 := ⟨1, 0, 0, -1⟩
def hadamard (invSqrt2 : ℝ) : RMat2 := rsmul invSqrt2 ⟨1, 1, 1, -1⟩

/-- Hadamard conjugation under the stated normalization condition. -/
theorem hadamard_conjugation_Z_to_X (invSqrt2 : ℝ)
    (h_sq : invSqrt2 * invSqrt2 = 1 / 2) :
    rmul (hadamard invSqrt2) (rmul pauliZ (hadamard invSqrt2)) = pauliX := by
  ext <;> dsimp [hadamard, pauliZ, pauliX, rmul, rsmul] <;> nlinarith [h_sq]

/-- The four labels supported by the prescribed single-phase-error table. -/
inductive PhaseError
  | none
  | z1
  | z2
  | z3
  deriving DecidableEq, Repr

/-- A prescribed syndrome table, not a derived quantum measurement. -/
def syndromeMeasure (err : PhaseError) : ℕ × ℕ :=
  match err with
  | .none => (0, 0)
  | .z1 => (1, 0)
  | .z2 => (1, 1)
  | .z3 => (0, 1)

/-- Decode supported syndromes; other natural-number pairs default to none. -/
def decodeSyndrome (s : ℕ × ℕ) : PhaseError :=
  match s with
  | (1, 0) => .z1
  | (1, 1) => .z2
  | (0, 1) => .z3
  | _ => .none

theorem decode_syndrome_correct (e : PhaseError) :
    decodeSyndrome (syndromeMeasure e) = e := by
  cases e <;> rfl

theorem syndrome_measure_injective (e1 e2 : PhaseError) :
    syndromeMeasure e1 = syndromeMeasure e2 ↔ e1 = e2 := by
  constructor
  · intro h
    have h_decode := congrArg decodeSyndrome h
    simpa only [decode_syndrome_correct] using h_decode
  · rintro rfl
    rfl

theorem pauliZ_involutive : rmul pauliZ pauliZ = rmatI := by
  ext <;> norm_num [rmul, pauliZ, rmatI]

/-- Recovery of the error label only; not restoration of a quantum state. -/
theorem error_correction_identity (e : PhaseError) :
    let correction := decodeSyndrome (syndromeMeasure e)
    correction = e := decode_syndrome_correct e

structure QuantumPhaseFlipFormalSuite : Prop where
  h_hadamard_conj : ∀ (invSqrt2 : ℝ), invSqrt2 * invSqrt2 = 1 / 2 →
    rmul (hadamard invSqrt2) (rmul pauliZ (hadamard invSqrt2)) = pauliX
  h_z_involutive : rmul pauliZ pauliZ = rmatI
  h_syndrome_inj : ∀ (e1 e2 : PhaseError), syndromeMeasure e1 = syndromeMeasure e2 ↔ e1 = e2
  h_decode_corr : ∀ (e : PhaseError), decodeSyndrome (syndromeMeasure e) = e

/-- Matrix identities and correctness of the four-label decoding table. -/
theorem quantum_phase_flip_master_verification_suite : QuantumPhaseFlipFormalSuite := {
  h_hadamard_conj := hadamard_conjugation_Z_to_X
  h_z_involutive := pauliZ_involutive
  h_syndrome_inj := syndrome_measure_injective
  h_decode_corr := decode_syndrome_correct
}

#print axioms quantum_phase_flip_master_verification_suite

end QuantumPhaseFlipCode
