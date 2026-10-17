/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open CryptoBulletproofsIPAFiniteForkingProbabilityContract

example : CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).crypto_suite.ipa_probability
example (r : MasterSuite.VerificationMasterRegistry) :
    CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite := r.crypto_suite.ipa_probability
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite := r.crypto_full_suite.ipa_probability
example : CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite := verification_suite
