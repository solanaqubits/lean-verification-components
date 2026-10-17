import Verification.MasterSuite
open CryptoPedersenCommitmentOpeningExtractionContract
example : CryptoPedersenCommitmentOpeningExtractionContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.pedersen_opening
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoPedersenCommitmentOpeningExtractionContractSuite := r.crypto_suite.pedersen_opening
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoPedersenCommitmentOpeningExtractionContractSuite := r.crypto_full_suite.pedersen_opening
example {q : ℕ} [Fact q.Prime] {W A : Type} [AddCommGroup W] [Module (ZMod q) W]
    [AddCommGroup A] [Module (ZMod q) A] (L : W →ₗ[ZMod q] A) C t₁ t₂
    (h : ValidFork L C t₁ t₂) : L (extractOpening t₁ t₂) = C :=
  verification_suite.soundness L C t₁ t₂ h
