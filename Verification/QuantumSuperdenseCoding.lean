import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumSuperdenseCoding

/-- Real coordinates in the ordered computational basis 00, 01, 10, 11. -/
structure QState4 where
  x00 : ℝ
  x01 : ℝ
  x10 : ℝ
  x11 : ℝ

def dot (u v : QState4) : ℝ :=
  u.x00 * v.x00 + u.x01 * v.x01 + u.x10 * v.x10 + u.x11 * v.x11

/-- Four prescribed Bell-vector representatives, without a gate model. -/
def encode (s : ℝ) (b1 b2 : Bool) : QState4 :=
  match b1, b2 with
  | false, false => ⟨s, 0, 0, s⟩
  | false, true => ⟨0, s, s, 0⟩
  | true, false => ⟨s, 0, 0, -s⟩
  | true, true => ⟨0, s, -s, 0⟩

/-- Coordinate/sign classifier, not a quantum measurement operation.
Correctness below assumes the positive-scale representatives produced by encode. -/
def decode (v : QState4) : Bool × Bool :=
  if v.x00 ≠ 0 then
    (decide (v.x11 < 0), false)
  else
    (decide (v.x10 < 0), true)

theorem superdense_decode_ff (s : ℝ) (hs_pos : 0 < s) :
    decode (encode s false false) = (false, false) := by
  simp [encode, decode, ne_of_gt hs_pos, not_lt_of_ge (le_of_lt hs_pos)]

theorem superdense_decode_ft (s : ℝ) (hs_pos : 0 < s) :
    decode (encode s false true) = (false, true) := by
  simp [encode, decode, not_lt_of_ge (le_of_lt hs_pos)]

theorem superdense_decode_tf (s : ℝ) (hs_pos : 0 < s) :
    decode (encode s true false) = (true, false) := by
  simp [encode, decode, ne_of_gt hs_pos, neg_lt_zero.mpr hs_pos]

theorem superdense_decode_tt (s : ℝ) (hs_pos : 0 < s) :
    decode (encode s true true) = (true, true) := by
  simp [encode, decode, neg_lt_zero.mpr hs_pos]

theorem superdense_universal_correctness (s : ℝ) (hs_pos : 0 < s) (b1 b2 : Bool) :
    decode (encode s b1 b2) = (b1, b2) := by
  cases b1 <;> cases b2
  · exact superdense_decode_ff s hs_pos
  · exact superdense_decode_ft s hs_pos
  · exact superdense_decode_tf s hs_pos
  · exact superdense_decode_tt s hs_pos

theorem superdense_states_normalized (s : ℝ) (hs_sq : s * s = 1 / 2) (b1 b2 : Bool) :
    dot (encode s b1 b2) (encode s b1 b2) = 1 := by
  cases b1 <;> cases b2 <;> dsimp [dot, encode] <;> nlinarith

theorem superdense_states_orthogonal (s : ℝ) (b1 b2 b1' b2' : Bool)
    (h_diff : (b1, b2) ≠ (b1', b2')) :
    dot (encode s b1 b2) (encode s b1' b2') = 0 := by
  cases b1 <;> cases b2 <;> cases b1' <;> cases b2' <;>
    first | exact False.elim (h_diff rfl) | (dsimp [dot, encode]; ring)

structure QuantumSuperdenseFormalSuite : Prop where
  h_decode_ff : ∀ s : ℝ, 0 < s → decode (encode s false false) = (false, false)
  h_decode_ft : ∀ s : ℝ, 0 < s → decode (encode s false true) = (false, true)
  h_decode_tf : ∀ s : ℝ, 0 < s → decode (encode s true false) = (true, false)
  h_decode_tt : ∀ s : ℝ, 0 < s → decode (encode s true true) = (true, true)
  h_universal : ∀ s : ℝ, 0 < s → ∀ b1 b2 : Bool, decode (encode s b1 b2) = (b1, b2)
  h_normalized : ∀ s : ℝ, s * s = 1 / 2 → ∀ b1 b2 : Bool,
    dot (encode s b1 b2) (encode s b1 b2) = 1
  h_orthogonal : ∀ (s : ℝ) (b1 b2 b1' b2' : Bool), (b1, b2) ≠ (b1', b2') →
    dot (encode s b1 b2) (encode s b1' b2') = 0

/-- Registry of coordinate decoding and Bell-vector inner-product identities. -/
theorem quantum_superdense_master_verification_suite : QuantumSuperdenseFormalSuite := {
  h_decode_ff := superdense_decode_ff
  h_decode_ft := superdense_decode_ft
  h_decode_tf := superdense_decode_tf
  h_decode_tt := superdense_decode_tt
  h_universal := superdense_universal_correctness
  h_normalized := superdense_states_normalized
  h_orthogonal := superdense_states_orthogonal
}

end QuantumSuperdenseCoding
