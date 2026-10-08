/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoPedersenHomomorphicSum

/-! Schnorr identification in the finite group model of Pedersen. Only the generator g
is used. Perfect special HVZK is an equality of full transcript PMFs for each fixed
challenge. No computational hardness, adversarial interaction or runtime model is assumed. -/
namespace CryptoSchnorrIdentification

universe u
variable {q : ℕ} [Fact q.Prime]
variable {G : Type u} [Fintype G] [AddCommGroup G] [Module (ZMod q) G]

abbrev Setup := CryptoPedersenHomomorphicSum.Setup

/-- Public data only: no secret witness is stored in a statement. -/
structure Statement (G : Type u) where
  X : G

def Statement.Holds (S : Setup q G) (P : Statement G) (x : ZMod q) : Prop :=
  P.X = x • S.g

structure Transcript (q : ℕ) (G : Type u) where
  R : G
  c : ZMod q
  s : ZMod q
  deriving DecidableEq

def Verify (S : Setup q G) (X : G) (t : Transcript q G) : Prop :=
  t.s • S.g = t.R + t.c • X

def honestTranscript (S : Setup q G) (x r c : ZMod q) : Transcript q G :=
  ⟨r • S.g, c, r + c * x⟩

/-- The simulator uses only the public key, challenge and sampled response. -/
def simulateTranscript (S : Setup q G) (X : G) (c s : ZMod q) : Transcript q G :=
  ⟨s • S.g - c • X, c, s⟩

def extractWitness (c₁ c₂ s₁ s₂ : ZMod q) : ZMod q := (s₁ - s₂) * (c₁ - c₂)⁻¹

theorem schnorr_perfect_completeness (S : Setup q G) (x r c : ZMod q) :
    Verify S (x • S.g) (honestTranscript S x r c) := by
  simp [Verify, honestTranscript, add_smul, mul_smul]

theorem schnorr_special_soundness (S : Setup q G) (X R : G)
    (c₁ c₂ s₁ s₂ : ZMod q) (hc : c₁ ≠ c₂)
    (h₁ : Verify S X ⟨R, c₁, s₁⟩) (h₂ : Verify S X ⟨R, c₂, s₂⟩) :
    c₁ - c₂ ≠ 0 ∧ X = extractWitness c₁ c₂ s₁ s₂ • S.g := by
  have hdiff : (s₁ - s₂) • S.g = (c₁ - c₂) • X := by
    calc
      (s₁ - s₂) • S.g = s₁ • S.g - s₂ • S.g := sub_smul _ _ _
      _ = (R + c₁ • X) - (R + c₂ • X) := congrArg₂ (· - ·) h₁ h₂
      _ = (c₁ - c₂) • X := by simp [sub_smul]
  refine ⟨sub_ne_zero.mpr hc, ?_⟩
  have hi := congrArg (fun z : G => (c₁ - c₂)⁻¹ • z) hdiff
  simpa [extractWitness, smul_smul, sub_ne_zero.mpr hc, mul_comm] using hi.symm

theorem extracted_witness_eq_secret (S : Setup q G) (x : ZMod q) (R : G)
    (c₁ c₂ s₁ s₂ : ZMod q) (hc : c₁ ≠ c₂)
    (h₁ : Verify S (x • S.g) ⟨R, c₁, s₁⟩) (h₂ : Verify S (x • S.g) ⟨R, c₂, s₂⟩) :
    extractWitness c₁ c₂ s₁ s₂ = x :=
  (smul_left_injective (ZMod q) S.g_ne_zero
    (schnorr_special_soundness S _ R c₁ c₂ s₁ s₂ hc h₁ h₂).2).symm

theorem challenge_difference_inverse (c₁ c₂ : ZMod q) (hc : c₁ ≠ c₂) :
    (c₁ - c₂) * (c₁ - c₂)⁻¹ = 1 := mul_inv_cancel₀ (sub_ne_zero.mpr hc)

theorem schnorr_hvzk_simulator_valid (S : Setup q G) (X : G) (c s : ZMod q) :
    Verify S X (simulateTranscript S X c s) := by simp [Verify, simulateTranscript]

def responseEquiv (x c : ZMod q) : ZMod q ≃ ZMod q where
  toFun r := r + c * x
  invFun s := s - c * x
  left_inv r := add_sub_cancel_right r (c * x)
  right_inv s := sub_add_cancel s (c * x)

theorem simulate_response_eq_honest (S : Setup q G) (x r c : ZMod q) :
    simulateTranscript S (x • S.g) c (responseEquiv x c r) = honestTranscript S x r c := by
  simp [simulateTranscript, honestTranscript, responseEquiv, add_smul, mul_smul]

noncomputable def realLaw (S : Setup q G) (x c : ZMod q) : PMF (Transcript q G) :=
  (PMF.uniformOfFintype (ZMod q)).map (fun r => honestTranscript S x r c)

noncomputable def simulatedLaw (S : Setup q G) (X : G) (c : ZMod q) :
    PMF (Transcript q G) :=
  (PMF.uniformOfFintype (ZMod q)).map (simulateTranscript S X c)

/-- Exact equality of joint transcripts, not just verifier acceptance or equal marginals. -/
theorem schnorr_hvzk_distribution (S : Setup q G) (X : G) (x c : ZMod q)
    (hx : X = x • S.g) : realLaw S x c = simulatedLaw S X c := by
  subst X
  have hshift := CryptoPedersenHomomorphicSum.map_uniform_equiv (responseEquiv x c)
  unfold simulatedLaw
  rw [← hshift, PMF.map_comp]
  change realLaw S x c = (PMF.uniformOfFintype (ZMod q)).map
    (fun r => simulateTranscript S (x • S.g) c (responseEquiv x c r))
  simp_rw [simulate_response_eq_honest]
  rfl

theorem schnorr_hvzk_pairs (S : Setup q G) (x c : ZMod q) :
    (realLaw S x c).map (fun t => (t.R, t.s)) =
      (simulatedLaw S (x • S.g) c).map (fun t => (t.R, t.s)) := by
  rw [schnorr_hvzk_distribution S _ x c rfl]

/-- Every public group element has a unique witness; no witness is an input to the simulator. -/
theorem statement_has_unique_witness (S : Setup q G) (P : Statement G) :
    ∃! x : ZMod q, P.Holds S x := by
  obtain ⟨x, hx⟩ := (CryptoPedersenHomomorphicSum.nonzero_generator_bijective
    S S.g_ne_zero).2 P.X
  refine ⟨x, hx.symm, ?_⟩
  intro y hy
  exact smul_left_injective (ZMod q) S.g_ne_zero (hy.symm.trans hx.symm)

/-- Any one-generator group embeds in the reused setup by taking h=g. -/
def oneGeneratorSetup (g : G) (hg : g ≠ 0) (hcard : Fintype.card G = q) : Setup q G :=
  ⟨hcard, g, g, hg, hg⟩

/-- Real protocol order: nonce first, then an independent challenge. -/
noncomputable def honestInteractionLaw (S : Setup q G) (x : ZMod q) (ν : PMF (ZMod q)) :
    PMF (Transcript q G) :=
  (PMF.uniformOfFintype (ZMod q)).bind fun r => ν.map (honestTranscript S x r)

noncomputable def simulatedInteractionLaw (S : Setup q G) (X : G) (ν : PMF (ZMod q)) :
    PMF (Transcript q G) := ν.bind (simulatedLaw S X)

theorem schnorr_hvzk_independent_challenge (S : Setup q G) (x : ZMod q)
    (ν : PMF (ZMod q)) :
    honestInteractionLaw S x ν = simulatedInteractionLaw S (x • S.g) ν := by
  have horder : honestInteractionLaw S x ν = ν.bind (realLaw S x) :=
    PMF.bind_comm _ _ _
  rw [horder]
  change ν.bind (realLaw S x) = ν.bind (simulatedLaw S (x • S.g))
  congr 1
  funext c
  exact schnorr_hvzk_distribution S _ x c rfl

theorem simulated_support_iff (S : Setup q G) (X : G) (c : ZMod q)
    (t : Transcript q G) :
    t ∈ (simulatedLaw S X c).support ↔ t.c = c ∧ Verify S X t := by
  rw [simulatedLaw, PMF.mem_support_map_iff]
  constructor
  · rintro ⟨s, _, rfl⟩
    exact ⟨rfl, schnorr_hvzk_simulator_valid S X c s⟩
  · rcases t with ⟨R, c', s⟩
    rintro ⟨hc, hv⟩
    change c' = c at hc
    subst c'
    refine ⟨s, PMF.mem_support_uniformOfFintype s, ?_⟩
    change Transcript.mk (s • S.g - c • X) c s = Transcript.mk R c s
    congr 1
    exact sub_eq_iff_eq_add.mpr hv

theorem real_support_iff (S : Setup q G) (x c : ZMod q) (t : Transcript q G) :
    t ∈ (realLaw S x c).support ↔ t.c = c ∧ Verify S (x • S.g) t := by
  rw [schnorr_hvzk_distribution S _ x c rfl]
  exact simulated_support_iff S _ c t

/-- The challenge-zero transcript needs no secret; fixed-challenge acceptance alone
is not knowledge extraction. Distinct challenges are essential. -/
theorem zero_challenge_transcript (S : Setup q G) (X : G) (r : ZMod q) :
    Verify S X ⟨r • S.g, 0, r⟩ := by simp [Verify]

structure VerifiedProperties (S : Setup q G) : Prop where
  completeness : ∀ x r c, Verify S (x • S.g) (honestTranscript S x r c)
  soundness : ∀ X R c₁ c₂ s₁ s₂, c₁ ≠ c₂ →
    Verify S X ⟨R, c₁, s₁⟩ → Verify S X ⟨R, c₂, s₂⟩ →
    c₁ - c₂ ≠ 0 ∧ X = extractWitness c₁ c₂ s₁ s₂ • S.g
  simulator_valid : ∀ X c s, Verify S X (simulateTranscript S X c s)
  hvzk_distribution : ∀ X x c, X = x • S.g → realLaw S x c = simulatedLaw S X c
  independent_challenge : ∀ x ν,
    honestInteractionLaw S x ν = simulatedInteractionLaw S (x • S.g) ν
  witness_exists_unique : ∀ P : Statement G, ∃! x, P.Holds S x
  support_exact : ∀ x c t,
    t ∈ (realLaw S x c).support ↔ t.c = c ∧ Verify S (x • S.g) t

theorem verified_properties (S : Setup q G) : VerifiedProperties S where
  completeness := schnorr_perfect_completeness S
  soundness := schnorr_special_soundness S
  simulator_valid := schnorr_hvzk_simulator_valid S
  hvzk_distribution := schnorr_hvzk_distribution S
  independent_challenge := schnorr_hvzk_independent_challenge S
  witness_exists_unique := statement_has_unique_witness S
  support_exact := real_support_iff S

structure CryptoSchnorrIdentificationSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (G : Type u) [Fintype G] [AddCommGroup G]
    [Module (ZMod q) G] (S : Setup q G), VerifiedProperties S
  satisfiable : ∀ (q : ℕ) [Fact q.Prime], Nonempty (Setup q (ZMod q))

theorem crypto_schnorr_identification_master_suite : CryptoSchnorrIdentificationSuite.{u} where
  all_models := fun _ _ _ _ _ _ S => verified_properties S
  satisfiable := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoSchnorrIdentification
