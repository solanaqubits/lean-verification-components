import Verification.MasterSuite

open DistributedTendermintQuorumIntersectionEpochTransitionContract
example : DistributedTendermintQuorumIntersectionEpochTransitionContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.epoch_quorum
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintQuorumIntersectionEpochTransitionContractSuite :=
  r.distributed_suite.epoch_quorum
example (r : MasterHundredRegistry.MasterHundredFormalSuite) : DistributedTendermintQuorumIntersectionEpochTransitionContractSuite :=
  r.distributed_systems_full_suite.epoch_quorum
example {V : Type} [Fintype V] [DecidableEq V] (w z : V → ℚ)
    (hw : Normalized w) (hz : Normalized z) B Q R q r
    (hq : isQuorum w q Q) (hr : isQuorum z r R)
    (hc : 2 - q - r < honestCommon w z B) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v :=
  verification_suite.intersection w z hw hz B Q R q r hq hr hc
example {V : Type} [Fintype V] (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z) :
    mass (common w z) Finset.univ = 1 - variation w z :=
  verification_suite.variation_identity w z hw hz
