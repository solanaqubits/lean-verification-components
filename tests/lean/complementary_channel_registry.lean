import Verification.MasterSuite

example : QuantumComplementaryChannelContract.QuantumComplementaryChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.complementary_channel

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumComplementaryChannelContract.QuantumComplementaryChannelContractSuite := r.quantum_suite.complementary_channel

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumComplementaryChannelContract.QuantumComplementaryChannelContractSuite :=
  r.quantum_physics_full_suite.complementary_channel
