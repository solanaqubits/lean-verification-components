import Verification.MasterSuite

example : QuantumKnillLaflammeEnvironmentCriterion.QuantumKnillLaflammeEnvironmentCriterionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.knill_laflamme

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumKnillLaflammeEnvironmentCriterion.QuantumKnillLaflammeEnvironmentCriterionSuite := r.quantum_suite.knill_laflamme

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumKnillLaflammeEnvironmentCriterion.QuantumKnillLaflammeEnvironmentCriterionSuite :=
  r.quantum_physics_full_suite.knill_laflamme
