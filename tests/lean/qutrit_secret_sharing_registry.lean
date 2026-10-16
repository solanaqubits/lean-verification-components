import Verification.MasterSuite

example : QuantumQutritTwoOfThreeSecretSharingContract.QuantumQutritTwoOfThreeSecretSharingContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.qutrit_secret_sharing

example : QuantumCPTPChannelContract.QuantumCPTPChannelContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).quantum_suite.cptp_channel

example (r : MasterSuite.VerificationMasterRegistry) :
    QuantumQutritTwoOfThreeSecretSharingContract.QuantumQutritTwoOfThreeSecretSharingContractSuite := r.quantum_suite.qutrit_secret_sharing

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    QuantumQutritTwoOfThreeSecretSharingContract.QuantumQutritTwoOfThreeSecretSharingContractSuite :=
  r.quantum_physics_full_suite.qutrit_secret_sharing
