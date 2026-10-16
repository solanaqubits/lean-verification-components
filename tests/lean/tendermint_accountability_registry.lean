import Verification.MasterSuite

example : DistributedTendermintAccountableSafety.DistributedTendermintAccountableSafetySuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_accountability

example : DistributedTendermintCoreSafety.DistributedTendermintCoreSafetySuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint

example (r : MasterSuite.VerificationMasterRegistry) :
    DistributedTendermintAccountableSafety.DistributedTendermintAccountableSafetySuite :=
  r.distributed_suite.tendermint_accountability

example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedTendermintAccountableSafety.DistributedTendermintAccountableSafetySuite :=
  r.distributed_systems_full_suite.tendermint_accountability
