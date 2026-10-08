import Verification.CryptoSchnorrIdentification
import Verification.CryptoSchnorrSignature

open CryptoSchnorrIdentification

universe u
section Generic
variable {q : ℕ} [Fact q.Prime] {G : Type u}
variable [Fintype G] [AddCommGroup G] [Module (ZMod q) G] (S : Setup q G)

example : VerifiedProperties S :=
  crypto_schnorr_identification_master_suite.all_models q G S

example (x r c : ZMod q) : Verify S (x • S.g) (honestTranscript S x r c) :=
  schnorr_perfect_completeness S x r c

example (X R : G) (c₁ c₂ s₁ s₂ : ZMod q) (hc : c₁ ≠ c₂)
    (h₁ : Verify S X ⟨R, c₁, s₁⟩) (h₂ : Verify S X ⟨R, c₂, s₂⟩) :
    (c₁ - c₂) * (c₁ - c₂)⁻¹ = 1 ∧
      X = extractWitness c₁ c₂ s₁ s₂ • S.g :=
  ⟨challenge_difference_inverse _ _ hc,
    (schnorr_special_soundness S X R c₁ c₂ s₁ s₂ hc h₁ h₂).2⟩

example (x : ZMod q) (R : G) (c₁ c₂ s₁ s₂ : ZMod q) (hc : c₁ ≠ c₂)
    (h₁ : Verify S (x • S.g) ⟨R, c₁, s₁⟩) (h₂ : Verify S (x • S.g) ⟨R, c₂, s₂⟩) :
    extractWitness c₁ c₂ s₁ s₂ = x := extracted_witness_eq_secret S x R _ _ _ _ hc h₁ h₂

-- No secret argument or witness is required by the simulator.
example (X : G) (c s : ZMod q) : Verify S X (simulateTranscript S X c s) :=
  schnorr_hvzk_simulator_valid S X c s

example (X : G) (x c : ZMod q) (hx : X = x • S.g) :
    realLaw S x c = simulatedLaw S X c := schnorr_hvzk_distribution S X x c hx

example (x c : ZMod q) :
    (realLaw S x c).map (fun t => (t.R, t.s)) =
      (simulatedLaw S (x • S.g) c).map (fun t => (t.R, t.s)) := schnorr_hvzk_pairs S x c

-- The real experiment samples r before the independent uniform verifier challenge.
example (x : ZMod q) :
    honestInteractionLaw S x (PMF.uniformOfFintype (ZMod q)) =
      simulatedInteractionLaw S (x • S.g) (PMF.uniformOfFintype (ZMod q)) :=
  schnorr_hvzk_independent_challenge S x _

example (x : ZMod q) (ν : PMF (ZMod q)) :
    honestInteractionLaw S x ν = simulatedInteractionLaw S (x • S.g) ν :=
  schnorr_hvzk_independent_challenge S x ν

example (x c : ZMod q) (t : Transcript q G) :
    t ∈ (realLaw S x c).support ↔ t.c = c ∧ Verify S (x • S.g) t :=
  real_support_iff S x c t

example (X : G) (c : ZMod q) (t : Transcript q G) (hc : t.c ≠ c) :
    t ∉ (simulatedLaw S X c).support := by
  intro ht
  exact hc ((simulated_support_iff S X c t).mp ht).1

example (P : Statement G) : ∃! x, P.Holds S x := statement_has_unique_witness S P

example (r c : ZMod q) : Verify S 0 (honestTranscript S 0 r c) := by
  simpa using schnorr_perfect_completeness S 0 r c

-- Removing distinct challenges permits accepting transcripts but an incorrect extractor.
example : Verify S S.g ⟨0, 0, 0⟩ ∧
    S.g ≠ extractWitness (q := q) 0 0 0 0 • S.g := by simp [Verify, extractWitness, S.g_ne_zero]
end Generic

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
def S5 : Setup 5 (ZMod 5) := oneGeneratorSetup 1 one_ne_zero (ZMod.card 5)
def S2 : Setup 2 (ZMod 2) := oneGeneratorSetup 1 one_ne_zero (ZMod.card 2)

example : Verify S5 3 ⟨2, 1, 0⟩ ∧ Verify S5 3 ⟨2, 2, 3⟩ := by constructor <;> unfold Verify <;> decide
example : extractWitness (q := 5) 1 2 0 3 = 3 :=
  extracted_witness_eq_secret S5 3 2 1 2 0 3 (by decide) (by unfold Verify; decide) (by unfold Verify; decide)
example : extractWitness (q := 2) 0 1 0 1 = 1 :=
  extracted_witness_eq_secret S2 1 0 0 1 0 1 (by decide) (by unfold Verify; decide) (by unfold Verify; decide)

-- Distinct commitments invalidate extraction even with distinct challenges.
example : Verify S5 1 ⟨0, 0, 0⟩ ∧ Verify S5 1 ⟨1, 1, 2⟩ := by constructor <;> unfold Verify <;> decide
example : extractWitness (q := 5) 0 1 0 2 = 2 := by
  unfold extractWitness
  rw [← div_eq_mul_inv]
  apply (div_eq_iff (by decide)).mpr
  decide
example : ¬ Verify S5 3 ⟨2, 1, 1⟩ := by unfold Verify; decide
example : simulateTranscript S2 0 0 0 = honestTranscript S2 0 0 0 := by decide
example : Nonempty (Setup 2 (ZMod 2)) :=
  crypto_schnorr_identification_master_suite.{0}.satisfiable 2
