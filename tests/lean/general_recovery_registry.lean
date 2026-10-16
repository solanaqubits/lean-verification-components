import Verification.MasterSuite

example : QuantumKnillLaflammeGeneralRecoveryTheorem.QuantumKnillLaflammeGeneralRecoveryTheoremSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.general_recovery

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumKnillLaflammeGeneralRecoveryTheorem.QuantumKnillLaflammeGeneralRecoveryTheoremSuite := r.quantum_suite.general_recovery

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumKnillLaflammeGeneralRecoveryTheorem.QuantumKnillLaflammeGeneralRecoveryTheoremSuite :=
  r.quantum_physics_full_suite.general_recovery
