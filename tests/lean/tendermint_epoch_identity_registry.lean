import Verification.MasterSuite

open DistributedTendermintEpochIdentityContract
example : DistributedTendermintEpochIdentityContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_epoch_identity
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintEpochIdentityContractSuite :=
  r.distributed_suite.tendermint_epoch_identity
example (r : MasterHundredRegistry.MasterHundredFormalSuite) : DistributedTendermintEpochIdentityContractSuite :=
  r.distributed_systems_full_suite.tendermint_epoch_identity
open DistributedTendermintUnbondingPeriodContract
example {V : Type} [DecidableEq V] [Fintype V] w h p α (s : EpochState V) :
    totalValue (applyHistorical w h p α s).ledger = totalValue s.ledger :=
  verification_suite.conservation w h p α s
example {V : Type} [DecidableEq V] w h p α (s : EpochState V) (hw : WellFormed s.ledger) :
    WellFormed (applyHistorical w h p α s).ledger := verification_suite.nonnegative w h p α s hw
