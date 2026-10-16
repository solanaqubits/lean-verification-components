import Verification.MasterSuite

example : QuantumQutritSecretSharingExplicitDecoder.QuantumQutritSecretSharingExplicitDecoderSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.qutrit_explicit_decoder

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumQutritSecretSharingExplicitDecoder.QuantumQutritSecretSharingExplicitDecoderSuite := r.quantum_suite.qutrit_explicit_decoder

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumQutritSecretSharingExplicitDecoder.QuantumQutritSecretSharingExplicitDecoderSuite :=
  r.quantum_physics_full_suite.qutrit_explicit_decoder
