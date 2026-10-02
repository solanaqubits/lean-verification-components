import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace QuantumSuperdenseCoding

/-- Real coordinates in the ordered computational basis 00, 01, 10, 11. -/
@[ext] structure QState4 where
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

def basis00 : QState4 := ⟨1, 0, 0, 0⟩
def basis01 : QState4 := ⟨0, 1, 0, 0⟩
def basis10 : QState4 := ⟨0, 0, 1, 0⟩
def basis11 : QState4 := ⟨0, 0, 0, 1⟩

inductive ClassicalMsg where
  | m00 | m01 | m10 | m11
  deriving DecidableEq, Repr

def msgToBasis : ClassicalMsg → QState4
  | .m00 => basis00
  | .m01 => basis01
  | .m10 => basis10
  | .m11 => basis11

/-- The same signed normalization factor is used in encoding and decoding. -/
structure BellPairSetup where
  s : ℝ
  h_norm : 2 * s * s = 1

def aliceEncode (setup : BellPairSetup) : ClassicalMsg → QState4
  | .m00 => encode setup.s false false
  | .m01 => encode setup.s false true
  | .m10 => encode setup.s true false
  | .m11 => encode setup.s true true

def bobCNOT (v : QState4) : QState4 :=
  ⟨v.x00, v.x01, v.x11, v.x10⟩

def bobHadamard1 (setup : BellPairSetup) (v : QState4) : QState4 :=
  ⟨setup.s * (v.x00 + v.x10), setup.s * (v.x01 + v.x11),
   setup.s * (v.x00 - v.x10), setup.s * (v.x01 - v.x11)⟩

def bobDecode (setup : BellPairSetup) (v : QState4) : QState4 :=
  bobHadamard1 setup (bobCNOT v)

theorem superdense_decode_00 (setup : BellPairSetup) :
    bobDecode setup (aliceEncode setup .m00) = basis00 := by
  apply QState4.ext
  all_goals dsimp [bobDecode, bobHadamard1, bobCNOT, aliceEncode, encode, basis00]
  all_goals nlinarith only [setup.h_norm]

theorem superdense_decode_01 (setup : BellPairSetup) :
    bobDecode setup (aliceEncode setup .m01) = basis01 := by
  apply QState4.ext
  all_goals dsimp [bobDecode, bobHadamard1, bobCNOT, aliceEncode, encode, basis01]
  all_goals nlinarith only [setup.h_norm]

theorem superdense_decode_10 (setup : BellPairSetup) :
    bobDecode setup (aliceEncode setup .m10) = basis10 := by
  apply QState4.ext
  all_goals dsimp [bobDecode, bobHadamard1, bobCNOT, aliceEncode, encode, basis10]
  all_goals nlinarith only [setup.h_norm]

theorem superdense_decode_11 (setup : BellPairSetup) :
    bobDecode setup (aliceEncode setup .m11) = basis11 := by
  apply QState4.ext
  all_goals dsimp [bobDecode, bobHadamard1, bobCNOT, aliceEncode, encode, basis11]
  all_goals nlinarith only [setup.h_norm]

theorem superdense_universal_exactness (setup : BellPairSetup) (m : ClassicalMsg) :
    bobDecode setup (aliceEncode setup m) = msgToBasis m := by
  cases m
  · exact superdense_decode_00 setup
  · exact superdense_decode_01 setup
  · exact superdense_decode_10 setup
  · exact superdense_decode_11 setup

theorem bell_states_normalized (setup : BellPairSetup) (m : ClassicalMsg) :
    dot (aliceEncode setup m) (aliceEncode setup m) = 1 := by
  cases m <;> dsimp [aliceEncode, encode, dot] <;> nlinarith only [setup.h_norm]

theorem bell_states_orthogonal (setup : BellPairSetup) (m n : ClassicalMsg) (h : m ≠ n) :
    dot (aliceEncode setup m) (aliceEncode setup n) = 0 := by
  cases m <;> cases n <;>
    first | exact False.elim (h rfl) | (dsimp [aliceEncode, encode, dot]; ring)

theorem bell_states_orthogonal_phi (setup : BellPairSetup) :
    dot (aliceEncode setup .m00) (aliceEncode setup .m10) = 0 :=
  bell_states_orthogonal setup .m00 .m10 (by decide)

theorem bell_state_phi_plus_norm (setup : BellPairSetup) :
    dot (aliceEncode setup .m00) (aliceEncode setup .m00) = 1 :=
  bell_states_normalized setup .m00

structure QuantumSuperdenseCodingFormalSuite : Prop where
  h_dec_00 : ∀ setup, bobDecode setup (aliceEncode setup .m00) = basis00
  h_dec_01 : ∀ setup, bobDecode setup (aliceEncode setup .m01) = basis01
  h_dec_10 : ∀ setup, bobDecode setup (aliceEncode setup .m10) = basis10
  h_dec_11 : ∀ setup, bobDecode setup (aliceEncode setup .m11) = basis11
  h_universal : ∀ setup m, bobDecode setup (aliceEncode setup m) = msgToBasis m
  h_ortho : ∀ setup, dot (aliceEncode setup .m00) (aliceEncode setup .m10) = 0
  h_norm : ∀ setup, dot (aliceEncode setup .m00) (aliceEncode setup .m00) = 1
  h_all_norm : ∀ setup m, dot (aliceEncode setup m) (aliceEncode setup m) = 1
  h_all_ortho : ∀ setup m n, m ≠ n → dot (aliceEncode setup m) (aliceEncode setup n) = 0

theorem quantum_superdense_coding_master_suite : QuantumSuperdenseCodingFormalSuite := {
  h_dec_00 := superdense_decode_00
  h_dec_01 := superdense_decode_01
  h_dec_10 := superdense_decode_10
  h_dec_11 := superdense_decode_11
  h_universal := superdense_universal_exactness
  h_ortho := bell_states_orthogonal_phi
  h_norm := bell_state_phi_plus_norm
  h_all_norm := bell_states_normalized
  h_all_ortho := bell_states_orthogonal
}

structure QuantumSuperdenseFormalSuite : Prop where
  h_circuit : QuantumSuperdenseCodingFormalSuite
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
  h_circuit := quantum_superdense_coding_master_suite
  h_decode_ff := superdense_decode_ff
  h_decode_ft := superdense_decode_ft
  h_decode_tf := superdense_decode_tf
  h_decode_tt := superdense_decode_tt
  h_universal := superdense_universal_correctness
  h_normalized := superdense_states_normalized
  h_orthogonal := superdense_states_orthogonal
}

end QuantumSuperdenseCoding
