import Verification.MasterSuite

open DistributedTendermintSlashingPenaltyContract
example : DistributedTendermintSlashingPenaltyContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_slashing
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintSlashingPenaltyContractSuite :=
  r.distributed_suite.tendermint_slashing
example (r : MasterHundredRegistry.MasterHundredFormalSuite) : DistributedTendermintSlashingPenaltyContractSuite :=
  r.distributed_systems_full_suite.tendermint_slashing
example (w : Fin 3 → ℚ) (B : Finset (Fin 3)) (α : ℚ) :
    totalStake (stakeSlashing w B α) + confiscated w B α = totalStake w :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_slashing.conservation w B α
