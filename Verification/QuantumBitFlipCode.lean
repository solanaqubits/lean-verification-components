import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumBitFlipCode

/-- Eight real coordinates; normalization is not built into the type. -/
@[ext] structure QState8 where
  x000 : ℝ
  x001 : ℝ
  x010 : ℝ
  x011 : ℝ
  x100 : ℝ
  x101 : ℝ
  x110 : ℝ
  x111 : ℝ

def dot (u v : QState8) : ℝ :=
  u.x000 * v.x000 + u.x001 * v.x001 + u.x010 * v.x010 + u.x011 * v.x011 +
  u.x100 * v.x100 + u.x101 * v.x101 + u.x110 * v.x110 + u.x111 * v.x111

def encode (α β : ℝ) : QState8 := ⟨α, 0, 0, 0, 0, 0, 0, β⟩

inductive BitFlipError where
  | noError | flip1 | flip2 | flip3
  deriving DecidableEq, Repr

/-- Coordinate permutations representing at most one bit flip. -/
def applyError (e : BitFlipError) (v : QState8) : QState8 :=
  match e with
  | .noError => v
  | .flip1 => ⟨v.x100, v.x101, v.x110, v.x111, v.x000, v.x001, v.x010, v.x011⟩
  | .flip2 => ⟨v.x010, v.x011, v.x000, v.x001, v.x110, v.x111, v.x100, v.x101⟩
  | .flip3 => ⟨v.x001, v.x000, v.x011, v.x010, v.x101, v.x100, v.x111, v.x110⟩

/-- Exact coordinate-support classifier, not a projective quantum measurement. -/
def measureSyndrome (v : QState8) : BitFlipError :=
  if v.x000 ≠ 0 ∨ v.x111 ≠ 0 then .noError
  else if v.x100 ≠ 0 ∨ v.x011 ≠ 0 then .flip1
  else if v.x010 ≠ 0 ∨ v.x101 ≠ 0 then .flip2
  else .flip3

def correct (v : QState8) : QState8 := applyError (measureSyndrome v) v

theorem bit_flip_correct_no_error (α β : ℝ) (h_norm : α ≠ 0 ∨ β ≠ 0) :
    correct (applyError BitFlipError.noError (encode α β)) = encode α β := by
  simp [correct, applyError, measureSyndrome, encode, h_norm]

theorem bit_flip_correct_flip1 (α β : ℝ) (h_norm : α ≠ 0 ∨ β ≠ 0) :
    correct (applyError BitFlipError.flip1 (encode α β)) = encode α β := by
  simp [correct, applyError, measureSyndrome, encode, h_norm]

theorem bit_flip_correct_flip2 (α β : ℝ) (h_norm : α ≠ 0 ∨ β ≠ 0) :
    correct (applyError BitFlipError.flip2 (encode α β)) = encode α β := by
  simp [correct, applyError, measureSyndrome, encode, h_norm]

theorem bit_flip_correct_flip3 (α β : ℝ) (_h_norm : α ≠ 0 ∨ β ≠ 0) :
    correct (applyError BitFlipError.flip3 (encode α β)) = encode α β := by
  simp [correct, applyError, measureSyndrome, encode]

theorem bit_flip_universal_recovery (α β : ℝ) (h_norm : α ≠ 0 ∨ β ≠ 0)
    (e : BitFlipError) : correct (applyError e (encode α β)) = encode α β := by
  cases e with
  | noError => exact bit_flip_correct_no_error α β h_norm
  | flip1 => exact bit_flip_correct_flip1 α β h_norm
  | flip2 => exact bit_flip_correct_flip2 α β h_norm
  | flip3 => exact bit_flip_correct_flip3 α β h_norm

/-- Normalization of the encoding under the supplied input normalization hypothesis. -/
theorem bit_flip_norm_preservation (α β : ℝ) (h_sq : α ^ 2 + β ^ 2 = 1) :
    dot (encode α β) (encode α β) = 1 := by
  calc dot (encode α β) (encode α β)
    _ = α ^ 2 + β ^ 2 := by dsimp [dot, encode]; ring
    _ = 1 := h_sq

structure QuantumBitFlipCodeFormalSuite : Prop where
  h_rec_none : ∀ (α β : ℝ), α ≠ 0 ∨ β ≠ 0 →
    correct (applyError BitFlipError.noError (encode α β)) = encode α β
  h_rec_flip1 : ∀ (α β : ℝ), α ≠ 0 ∨ β ≠ 0 →
    correct (applyError BitFlipError.flip1 (encode α β)) = encode α β
  h_rec_flip2 : ∀ (α β : ℝ), α ≠ 0 ∨ β ≠ 0 →
    correct (applyError BitFlipError.flip2 (encode α β)) = encode α β
  h_rec_flip3 : ∀ (α β : ℝ), α ≠ 0 ∨ β ≠ 0 →
    correct (applyError BitFlipError.flip3 (encode α β)) = encode α β
  h_rec_univ : ∀ (α β : ℝ), α ≠ 0 ∨ β ≠ 0 → ∀ (e : BitFlipError),
    correct (applyError e (encode α β)) = encode α β
  h_norm : ∀ (α β : ℝ), α ^ 2 + β ^ 2 = 1 → dot (encode α β) (encode α β) = 1

theorem quantum_bit_flip_code_master_verification_suite : QuantumBitFlipCodeFormalSuite := {
  h_rec_none := bit_flip_correct_no_error
  h_rec_flip1 := bit_flip_correct_flip1
  h_rec_flip2 := bit_flip_correct_flip2
  h_rec_flip3 := bit_flip_correct_flip3
  h_rec_univ := bit_flip_universal_recovery
  h_norm := bit_flip_norm_preservation
}

end QuantumBitFlipCode
