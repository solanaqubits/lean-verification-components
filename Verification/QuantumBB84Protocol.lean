import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

set_option linter.style.header false
noncomputable section

namespace QuantumBB84Protocol

/-- Two basis labels, without a quantum-state representation. -/
inductive Basis where
  | rectilinear
  | diagonal
  deriving DecidableEq, Repr

def siftMatch (aBasis bBasis : Basis) : Bool := decide (aBasis = bBasis)

/-- Prescribed identity map, not a measurement model. -/
def measuredBitOnMatch (aliceBit : Bool) : Bool := aliceBit

/-- The basis hypothesis is retained but not needed for this identity. -/
theorem sifting_basis_match_correctness (aliceBit : Bool) (aBasis bBasis : Basis)
    (_h_match : aBasis = bBasis) : measuredBitOnMatch aliceBit = aliceBit := rfl

theorem sift_match_iff (aBasis bBasis : Basis) :
    siftMatch aBasis bBasis = true ↔ aBasis = bBasis := by
  simp [siftMatch]

/-- Supplied scalar error parameter; not derived from an attack experiment. -/
def eveErrorProbabilityPerBit : ℝ := 1 / 4

theorem eve_detection_single_bit_complement :
    1 - eveErrorProbabilityPerBit = 3 / 4 := by
  norm_num [eveErrorProbabilityPerBit]

/-- Arithmetic evaluation, without a probabilistic independence model. -/
theorem eve_detection_two_bits :
    1 - (3 / 4 : ℝ) ^ 2 = 7 / 16 := by
  norm_num

structure QuantumBB84FormalSuite : Prop where
  h_sift_corr : ∀ (aliceBit : Bool) (aBasis bBasis : Basis),
    aBasis = bBasis → measuredBitOnMatch aliceBit = aliceBit
  h_sift_iff : ∀ aBasis bBasis : Basis,
    siftMatch aBasis bBasis = true ↔ aBasis = bBasis
  h_eve_comp : 1 - eveErrorProbabilityPerBit = 3 / 4
  h_eve_two : 1 - (3 / 4 : ℝ) ^ 2 = 7 / 16

/-- Registry of basis-label comparison and scalar arithmetic facts. -/
theorem quantum_bb84_master_verification_suite : QuantumBB84FormalSuite := {
  h_sift_corr := sifting_basis_match_correctness
  h_sift_iff := sift_match_iff
  h_eve_comp := eve_detection_single_bit_complement
  h_eve_two := eve_detection_two_bits
}

end QuantumBB84Protocol
