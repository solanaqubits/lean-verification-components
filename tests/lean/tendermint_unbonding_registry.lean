import Verification.MasterSuite

open DistributedTendermintUnbondingPeriodContract
example : DistributedTendermintUnbondingPeriodContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_unbonding
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintUnbondingPeriodContractSuite :=
  r.distributed_suite.tendermint_unbonding
example (r : MasterHundredRegistry.MasterHundredFormalSuite) : DistributedTendermintUnbondingPeriodContractSuite :=
  r.distributed_systems_full_suite.tendermint_unbonding
example {n : ℕ} w α (s : UnbondingState (Fin n)) rs :
    totalValue (processSlot w α s rs) = totalValue s := verification_suite.conservation w α s rs
example {n : ℕ} w α (s : UnbondingState (Fin n)) rs (hw : WellFormed s) :
    WellFormed (processSlot w α s rs) := verification_suite.nonnegative w α s rs hw
