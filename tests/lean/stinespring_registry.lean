import Verification.MasterSuite

example : QuantumStinespringDilationContract.QuantumStinespringDilationContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.stinespring

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumStinespringDilationContract.QuantumStinespringDilationContractSuite := r.quantum_suite.stinespring

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumStinespringDilationContract.QuantumStinespringDilationContractSuite :=
  r.quantum_physics_full_suite.stinespring
