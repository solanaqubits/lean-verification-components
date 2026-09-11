import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

set_option linter.style.header false
noncomputable section

namespace CryptoFiatShamirTransform

/-- Real scalar keys with a nonzero base; not a hard discrete-log group. -/
structure SchnorrKeys where
  G : ℝ
  privKey : ℝ
  pubKey : ℝ
  hG_ne_zero : G ≠ 0
  h_key_eq : pubKey = privKey * G

def commitment (G r : ℝ) : ℝ := r * G
def response (r c privKey : ℝ) : ℝ := r + c * privKey
def verifyEquation (G R Y c s : ℝ) : Prop := s * G = R + c * Y

theorem schnorr_completeness (keys : SchnorrKeys) (r c : ℝ) :
    let R := commitment keys.G r
    let s := response r c keys.privKey
    verifyEquation keys.G R keys.pubKey c s := by
  dsimp [verifyEquation, commitment, response]
  rw [keys.h_key_eq]
  ring

def extractWitness (s1 s2 c1 c2 : ℝ) : ℝ := (s1 - s2) / (c1 - c2)

/-- Two accepted responses at distinct challenges and the same R give a witness. -/
theorem schnorr_special_soundness (keys : SchnorrKeys) (R c1 c2 s1 s2 : ℝ)
    (h_c_diff : c1 ≠ c2)
    (h_v1 : verifyEquation keys.G R keys.pubKey c1 s1)
    (h_v2 : verifyEquation keys.G R keys.pubKey c2 s2) :
    keys.pubKey = extractWitness s1 s2 c1 c2 * keys.G := by
  have hdiff : (s1 - s2) * keys.G = (c1 - c2) * keys.pubKey := by
    calc (s1 - s2) * keys.G = s1 * keys.G - s2 * keys.G := by ring
         _ = (R + c1 * keys.pubKey) - (R + c2 * keys.pubKey) := by rw [h_v1, h_v2]
         _ = (c1 - c2) * keys.pubKey := by ring
  dsimp [extractWitness]
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff (sub_ne_zero.mpr h_c_diff)).mpr
  calc keys.pubKey * (c1 - c2) = (c1 - c2) * keys.pubKey := mul_comm _ _
       _ = (s1 - s2) * keys.G := hdiff.symm

/-- Nonzero G makes the extracted witness equal to the stored private scalar. -/
theorem schnorr_extracts_private_key (keys : SchnorrKeys) (R c1 c2 s1 s2 : ℝ)
    (h_c_diff : c1 ≠ c2)
    (h_v1 : verifyEquation keys.G R keys.pubKey c1 s1)
    (h_v2 : verifyEquation keys.G R keys.pubKey c2 s2) :
    extractWitness s1 s2 c1 c2 = keys.privKey := by
  have h := schnorr_special_soundness keys R c1 c2 s1 s2 h_c_diff h_v1 h_v2
  rw [keys.h_key_eq] at h
  exact (mul_right_cancel₀ keys.hG_ne_zero h).symm

/-- An arbitrary deterministic function, without randomness or hash assumptions. -/
def FiatShamirOracle (oracle : ℝ → ℝ → ℝ) (R msg : ℝ) : ℝ := oracle R msg

theorem fiat_shamir_non_interactive_completeness
    (keys : SchnorrKeys) (r msg : ℝ) (oracle : ℝ → ℝ → ℝ) :
    let R := commitment keys.G r
    let c := FiatShamirOracle oracle R msg
    let s := response r c keys.privKey
    verifyEquation keys.G R keys.pubKey c s := by
  exact schnorr_completeness keys r (FiatShamirOracle oracle (commitment keys.G r) msg)

structure CryptoFiatShamirFormalSuite : Prop where
  h_completeness : ∀ (keys : SchnorrKeys) r c,
    let R := commitment keys.G r
    let s := response r c keys.privKey
    verifyEquation keys.G R keys.pubKey c s
  h_soundness : ∀ (keys : SchnorrKeys) R c1 c2 s1 s2, c1 ≠ c2 →
    verifyEquation keys.G R keys.pubKey c1 s1 →
    verifyEquation keys.G R keys.pubKey c2 s2 →
    keys.pubKey = extractWitness s1 s2 c1 c2 * keys.G
  h_extract_key : ∀ (keys : SchnorrKeys) R c1 c2 s1 s2, c1 ≠ c2 →
    verifyEquation keys.G R keys.pubKey c1 s1 →
    verifyEquation keys.G R keys.pubKey c2 s2 →
    extractWitness s1 s2 c1 c2 = keys.privKey
  h_non_interact : ∀ (keys : SchnorrKeys) r msg (oracle : ℝ → ℝ → ℝ),
    let R := commitment keys.G r
    let c := FiatShamirOracle oracle R msg
    let s := response r c keys.privKey
    verifyEquation keys.G R keys.pubKey c s

theorem crypto_fiat_shamir_master_verification_suite : CryptoFiatShamirFormalSuite := {
  h_completeness := schnorr_completeness
  h_soundness := schnorr_special_soundness
  h_extract_key := schnorr_extracts_private_key
  h_non_interact := fiat_shamir_non_interactive_completeness
}

#print axioms crypto_fiat_shamir_master_verification_suite

end CryptoFiatShamirTransform
