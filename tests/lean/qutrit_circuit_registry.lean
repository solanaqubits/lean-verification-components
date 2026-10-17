import Verification.MasterSuite

example : QuantumQutritDecoderCircuitRefinement.QuantumQutritDecoderCircuitRefinementSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.qutrit_circuit_refinement

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumQutritDecoderCircuitRefinement.QuantumQutritDecoderCircuitRefinementSuite := r.quantum_suite.qutrit_circuit_refinement

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumQutritDecoderCircuitRefinement.QuantumQutritDecoderCircuitRefinementSuite :=
  r.quantum_physics_full_suite.qutrit_circuit_refinement
