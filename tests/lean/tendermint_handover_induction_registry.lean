import Verification.MasterSuite
open DistributedTendermintHandoverRoundInduction
open DistributedTendermintLockHandoverContract

example : DistributedTendermintHandoverRoundInductionSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.handover_induction
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintHandoverRoundInductionSuite :=
  r.distributed_suite.handover_induction
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedTendermintHandoverRoundInductionSuite := r.distributed_systems_full_suite.handover_induction
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) H A v
    (hh : Hits m c A) (hp : HonestPrevotes m c H A v) r x (hx : Polka m c H r x) : x = v :=
  DistributedTendermintHandoverRoundInduction.verification_suite.induction m c H A v hh hp r x hx
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) H A r x
    (hh : Hits m c A) (hc : HonestPrecommits m c H A) (hx : Commit m c H r x) : Polka m c H r x :=
  DistributedTendermintHandoverRoundInduction.verification_suite.certification m c H A r x hh hc hx
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) H A v
    (hh : Hits m c A) (hp : HonestPrevotes m c H A v) (hc : HonestPrecommits m c H A)
    r x (hx : Commit m c H r x) : x = v :=
  DistributedTendermintHandoverRoundInduction.verification_suite.agreement m c H A v hh hp hc r x hx
