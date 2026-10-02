/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

/-!
# CryptoElGamalEncryption

Algebraic and conditional invariants; see the theorem hypotheses and knowledge card for scope.
-/

namespace CryptoElGamalEncryption

/-! Scalar ElGamal identities over ℝ. No randomness or security game is modeled. -/
structure ElGamalSetup where
  g : ℝ
  hg_ne : g ≠ 0

@[ext] structure Ciphertext where
  c1 : ℝ
  c2 : ℝ

noncomputable def publicKey (setup : ElGamalSetup) (x : ℝ) : ℝ := x * setup.g
noncomputable def encrypt (setup : ElGamalSetup) (pk r m : ℝ) : Ciphertext :=
  ⟨r * setup.g, m + r * pk⟩
noncomputable def decrypt (x : ℝ) (c : Ciphertext) : ℝ := c.c2 - x * c.c1
noncomputable def addCiphertext (ca cb : Ciphertext) : Ciphertext :=
  ⟨ca.c1 + cb.c1, ca.c2 + cb.c2⟩
noncomputable def scaleCiphertext (k : ℝ) (c : Ciphertext) : Ciphertext :=
  ⟨k * c.c1, k * c.c2⟩

theorem elgamal_correctness (setup : ElGamalSetup) (x r m : ℝ) :
    decrypt x (encrypt setup (publicKey setup x) r m) = m := by
  dsimp [decrypt, encrypt, publicKey]
  ring

theorem elgamal_homomorphic_add (x : ℝ) (ca cb : Ciphertext) :
    decrypt x (addCiphertext ca cb) = decrypt x ca + decrypt x cb := by
  dsimp [decrypt, addCiphertext]
  ring

theorem elgamal_ciphertext_composition (setup : ElGamalSetup) (pk r1 r2 m1 m2 : ℝ) :
    addCiphertext (encrypt setup pk r1 m1) (encrypt setup pk r2 m2) =
      encrypt setup pk (r1 + r2) (m1 + m2) := by
  ext <;> dsimp [addCiphertext, encrypt] <;> ring

theorem elgamal_homomorphic_scale (x k : ℝ) (c : Ciphertext) :
    decrypt x (scaleCiphertext k c) = k * decrypt x c := by
  dsimp [decrypt, scaleCiphertext]
  ring

/-- Adding an encryption of zero preserves the plaintext; no distributional claim. -/
theorem elgamal_rerandomize (setup : ElGamalSetup) (x r1 r2 m : ℝ) :
    let pk := publicKey setup x
    let cOriginal := encrypt setup pk r1 m
    let cZero := encrypt setup pk r2 0
    decrypt x (addCiphertext cOriginal cZero) = m := by
  dsimp [publicKey, encrypt, decrypt, addCiphertext]
  ring

structure CryptoElGamalFormalSuite : Prop where
  h_correctness : ∀ (setup : ElGamalSetup) (x r m : ℝ),
    decrypt x (encrypt setup (publicKey setup x) r m) = m
  h_add_homo : ∀ (x : ℝ) (ca cb : Ciphertext),
    decrypt x (addCiphertext ca cb) = decrypt x ca + decrypt x cb
  h_composition : ∀ (setup : ElGamalSetup) (pk r1 r2 m1 m2 : ℝ),
    addCiphertext (encrypt setup pk r1 m1) (encrypt setup pk r2 m2) =
      encrypt setup pk (r1 + r2) (m1 + m2)
  h_scale_homo : ∀ (x k : ℝ) (c : Ciphertext),
    decrypt x (scaleCiphertext k c) = k * decrypt x c
  h_rerandomize : ∀ (setup : ElGamalSetup) (x r1 r2 m : ℝ),
    let pk := publicKey setup x
    decrypt x (addCiphertext (encrypt setup pk r1 m) (encrypt setup pk r2 0)) = m

theorem crypto_elgamal_master_verification_suite : CryptoElGamalFormalSuite := {
  h_correctness := elgamal_correctness
  h_add_homo := elgamal_homomorphic_add
  h_composition := elgamal_ciphertext_composition
  h_scale_homo := elgamal_homomorphic_scale
  h_rerandomize := elgamal_rerandomize
}

end CryptoElGamalEncryption
