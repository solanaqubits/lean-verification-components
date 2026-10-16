import Verification.MasterSuite

example : CryptoBulletproofsRangeInterpolation.CryptoBulletproofsRangeInterpolationSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.range_grid

example : CryptoBulletproofsTreeExtraction.CryptoBulletproofsTreeExtractionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.ipa_tree

example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsRangeInterpolation.CryptoBulletproofsRangeInterpolationSuite :=
  r.crypto_suite.range_grid

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsRangeInterpolation.CryptoBulletproofsRangeInterpolationSuite :=
  r.crypto_full_suite.range_grid
