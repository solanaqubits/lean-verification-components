import Verification.MasterSuite

example : QuantumReferencePreservingRecoveryContract.QuantumReferencePreservingRecoveryContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.reference_recovery

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumReferencePreservingRecoveryContract.QuantumReferencePreservingRecoveryContractSuite := r.quantum_suite.reference_recovery

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumReferencePreservingRecoveryContract.QuantumReferencePreservingRecoveryContractSuite :=
  r.quantum_physics_full_suite.reference_recovery
