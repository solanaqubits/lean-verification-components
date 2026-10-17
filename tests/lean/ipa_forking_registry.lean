/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAForkingExtractionContract

example : CryptoBulletproofsIPAForkingExtractionContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.ipa_forking
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAForkingExtractionContractSuite := r.crypto_suite.ipa_forking
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAForkingExtractionContractSuite := r.crypto_full_suite.ipa_forking
example : CryptoBulletproofsIPAForkingExtractionContractSuite := verification_suite
