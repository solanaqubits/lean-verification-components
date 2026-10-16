import Verification.MasterSuite

example : QuantumErasureCorrectabilityContract.QuantumErasureCorrectabilityContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.erasure_correctability

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumErasureCorrectabilityContract.QuantumErasureCorrectabilityContractSuite := r.quantum_suite.erasure_correctability

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumErasureCorrectabilityContract.QuantumErasureCorrectabilityContractSuite :=
  r.quantum_physics_full_suite.erasure_correctability
