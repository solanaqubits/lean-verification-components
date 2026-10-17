import Verification.MasterSuite

open DistributedTendermintSlashingReplayProtection
example : DistributedTendermintSlashingReplayProtectionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.tendermint_replay
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintSlashingReplayProtectionSuite :=
  r.distributed_suite.tendermint_replay
example (r : MasterHundredRegistry.MasterHundredFormalSuite) : DistributedTendermintSlashingReplayProtectionSuite :=
  r.distributed_systems_full_suite.tendermint_replay
example {n : ℕ} (c : DistributedTendermintCoreSafety.Config n) reference e α
    (s : SlashingLedgerState (Fin n)) :
    applySlashingCertificate c reference e α (applySlashingCertificate c reference e α s) =
      applySlashingCertificate c reference e α s := verification_suite.replay c reference e α s
