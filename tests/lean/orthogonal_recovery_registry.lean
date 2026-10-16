import Verification.MasterSuite

example : QuantumOrthogonalErrorRecoveryContract.QuantumOrthogonalErrorRecoveryContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.orthogonal_recovery

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumOrthogonalErrorRecoveryContract.QuantumOrthogonalErrorRecoveryContractSuite := r.quantum_suite.orthogonal_recovery

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumOrthogonalErrorRecoveryContract.QuantumOrthogonalErrorRecoveryContractSuite :=
  r.quantum_physics_full_suite.orthogonal_recovery
