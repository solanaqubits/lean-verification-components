import Verification.MasterSuite

example : QuantumKnillLaflammeRecoveryNecessity.QuantumKnillLaflammeRecoveryNecessitySuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.recovery_necessity

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumKnillLaflammeRecoveryNecessity.QuantumKnillLaflammeRecoveryNecessitySuite := r.quantum_suite.recovery_necessity

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumKnillLaflammeRecoveryNecessity.QuantumKnillLaflammeRecoveryNecessitySuite :=
  r.quantum_physics_full_suite.recovery_necessity
