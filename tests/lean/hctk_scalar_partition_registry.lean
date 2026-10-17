import Verification.MasterSuite
open HCTKScalarPartition
example : HCTKScalarPartitionSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).quantum_suite.hctk_scalar
example (s : MasterSuite.QuantumPhysicsFullSuite) : HCTKScalarPartitionSuite := s.hctk_scalar
example (s : MasterHundredRegistry.MasterHundredFormalSuite) : HCTKScalarPartitionSuite :=
  s.quantum_physics_full_suite.hctk_scalar
example : total (partition (5 : ℝ) (2/5) 3) = 5 := verification_suite.partition_conservation _ _ _
example (xs : List ℝ) (s : State) : total (runTransfers s xs) = total s :=
  (verification_suite.trace_invariants xs s).1
