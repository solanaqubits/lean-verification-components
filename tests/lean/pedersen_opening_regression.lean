import Verification.CryptoPedersenCommitmentOpeningExtractionContract

open CryptoPedersenCommitmentOpeningExtractionContract
namespace PedersenOpeningRegression
local instance : Fact (Nat.Prime 7) := ⟨by decide +kernel⟩
abbrev F := ZMod 7
abbrev L := scalarMap (q := 7) (1 : F) 2
-- Independent numeric transcripts, not defined through the honest constructor.
def t₁ : Transcript F (F × F) F := ⟨4, 0, 1, (5, 3)⟩
def t₂ : Transcript F (F × F) F := ⟨4, 0, 4, (0, 1)⟩
example : Verify L 4 t₁ := by decide +kernel
example : Verify L 4 t₂ := by decide +kernel
example : ValidFork L 4 t₁ t₂ := by decide +kernel
example : extractOpening t₁ t₂ = (3, 4) := by decide +kernel
example : checked_extract L 4 t₁ t₂ = .ok (3, 4) := by decide +kernel
example : L (3, 4) = 4 := by decide +kernel
example : L (extractOpening t₁ t₂) = 4 := special_soundness L 4 t₁ t₂ (by decide +kernel)
example : extractOpening t₂ t₁ = (3, 4) := by decide +kernel
example : checked_extract L 4 t₂ t₁ = .ok (3, 4) := by decide +kernel
example : checked_extract L 4 t₁ t₁ = .error .equalChallenges := by decide +kernel
example : extractOpening t₁ t₁ = (0, 0) := by decide +kernel
example : L (extractOpening t₁ t₁) ≠ 4 := by decide +kernel
example : ((t₂.challenge - t₁.challenge)⁻¹ • (t₁.response - t₂.response)) = (4, 3) := by decide +kernel
example : L ((t₂.challenge - t₁.challenge)⁻¹ • (t₁.response - t₂.response)) ≠ 4 := by decide +kernel

def otherAnnouncement : Transcript F (F × F) F := ⟨4, 1, 4, (1, 1)⟩
example : Verify L 4 otherAnnouncement := by decide +kernel
example : checked_extract L 4 t₁ otherAnnouncement = .error .announcementMismatch := by decide +kernel
example : L (extractOpening t₁ otherAnnouncement) ≠ 4 := by decide +kernel

def otherStatement : Transcript F (F × F) F := ⟨5, 0, 4, (4, 1)⟩
example : Verify L 5 otherStatement := by decide +kernel
example : checked_extract L 4 t₁ otherStatement = .error .statementMismatch := by decide +kernel
example : checked_extract L 5 t₁ otherStatement = .error .statementMismatch := by decide +kernel
example : checked_extract L 4 t₁ { t₂ with response := (1, 1) } =
    .error .rejectedResponse := by decide +kernel
example : checked_extract L 4 { t₁ with response := (1, 1) } t₂ =
    .error .rejectedResponse := by decide +kernel
example : checked_extract L 4 (honestTranscript L (3, 4) (2, 6) 0) t₂ =
    .ok (3, 4) := by decide +kernel
example (mask : F × F) : extractOpening (honestTranscript L (3, 4) mask 0)
    (honestTranscript L (3, 4) mask 4) = (3, 4) := honest_extracts _ _ _ _ _ (by decide +kernel)
example (m₁ m₂ : F × F) : extractOpening (honestTranscript L (3, 4) m₁ 0)
    (honestTranscript L (3, 4) m₁ 4) = extractOpening (honestTranscript L (3, 4) m₂ 0)
    (honestTranscript L (3, 4) m₂ 4) := honest_mask_independent _ _ _ _ _ _ (by decide +kernel)

-- Same commitment has distinct openings; special soundness does not assert uniqueness.
example : L (1, 5) = L (3, 4) := by decide +kernel
example : extractOpening (honestTranscript L (1, 5) (2, 6) 1)
    (honestTranscript L (1, 5) (2, 6) 4) = (1, 5) := by decide +kernel
example : ((1, 5) : F × F) ≠ (3, 4) := by decide +kernel
example : (3 - 1 : F) / (5 - 4) = 2 := by decide +kernel
example : (CryptoPedersenHomomorphicSum.scalarSetup (2 : F) (by decide +kernel)).h =
    ((3 - 1 : F) / (5 - 4)) • (1 : F) :=
  (collision_extracts_dlog (CryptoPedersenHomomorphicSum.scalarSetup (2 : F) (by decide +kernel))
    (3, 4) (1, 5) (by decide +kernel) (by decide +kernel)).2

abbrev VL := vectorMap (q := 7) (![1, 2] : Fin 2 → F) (3 : F)
def v₁ : Transcript F ((Fin 2 → F) × F) F := ⟨4, 0, 1, (![1, 5], 0)⟩
def v₂ : Transcript F ((Fin 2 → F) × F) F := ⟨4, 0, 4, (![0, 3], 1)⟩
example : ValidFork VL 4 v₁ v₂ := by decide +kernel
example : extractOpening v₁ v₂ = (![2, 4], 5) := by decide +kernel
example : checked_extract VL 4 v₁ v₂ = .ok (![2, 4], 5) := by
  apply (checked_extract_success_iff VL 4 v₁ v₂ _).mpr
  constructor <;> decide +kernel
example : CryptoCommitmentVectorPedersenGroup.commit_vec (![1, 2] : Fin 2 → F) 3
    (extractOpening v₁ v₂).1 (extractOpening v₁ v₂).2 = 4 :=
  vector_soundness _ _ _ _ _ (by decide +kernel)
example : checked_extract VL 4 v₁ v₁ = .error .equalChallenges := by decide +kernel
example : extractOpening v₂ v₁ = (![2, 4], 5) := by decide +kernel
example : vectorMap (q := 7) (fun i : Fin 0 => Fin.elim0 i) (3 : F) (0, 5) = 1 := by decide +kernel
example : scalarMap (q := 7) (0 : F) 0 (3, 4) = 0 := by decide +kernel
example : extractOpening (honestTranscript (scalarMap (q := 7) (0 : F) 0) (3, 4) (0, 0) 0)
    (honestTranscript (scalarMap (q := 7) (0 : F) 0) (3, 4) (0, 0) 1) = (3, 4) := by decide +kernel

-- Executable checks supplement, rather than replace, kernel examples.
def scenarios : List (String × Bool) := [
  ("scalar", decide (checked_extract L 4 t₁ t₂ = .ok (3, 4))),
  ("reverse", decide (checked_extract L 4 t₂ t₁ = .ok (3, 4))),
  ("zero challenge", decide (checked_extract L 4 (honestTranscript L (3, 4) (2, 6) 0) t₂ = .ok (3, 4))),
  ("equal challenge", decide (checked_extract L 4 t₁ t₁ = .error .equalChallenges)),
  ("different announcement", decide (checked_extract L 4 t₁ otherAnnouncement = .error .announcementMismatch)),
  ("different statement", decide (checked_extract L 4 t₁ otherStatement = .error .statementMismatch)),
  ("bad response", decide (checked_extract L 4 t₁ {t₂ with response := (1,1)} = .error .rejectedResponse)),
  ("sign mutation", decide (L ((t₂.challenge-t₁.challenge)⁻¹ • (t₁.response-t₂.response)) ≠ 4)),
  ("vector", decide (checked_extract VL 4 v₁ v₂ = .ok (![2,4],5))),
  ("nonunique", decide (L (1,5) = L (3,4))),
  ("dlog", decide ((3-1 : F)/(5-4) = 2)),
  ("empty vector", decide (vectorMap (q := 7) (fun i : Fin 0 => Fin.elim0 i) (3 : F) (0,5) = 1))]
#eval scenarios
end PedersenOpeningRegression
