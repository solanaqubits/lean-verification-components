import Verification.MasterSuite

example : CryptoBulletproofsRangeWitnessExtraction.CryptoBulletproofsRangeWitnessExtractionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.range_extraction

example : CryptoBulletproofsTreeExtraction.CryptoBulletproofsTreeExtractionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.ipa_tree

example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsRangeWitnessExtraction.CryptoBulletproofsRangeWitnessExtractionSuite :=
  r.crypto_suite.range_extraction

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsRangeWitnessExtraction.CryptoBulletproofsRangeWitnessExtractionSuite :=
  r.crypto_full_suite.range_extraction
