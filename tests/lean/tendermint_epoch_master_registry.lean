import Verification.MasterSuite
open DistributedTendermintEpochTransitionSafetyMasterContract
open DistributedTendermintEpochIdentityContract DistributedTendermintUnbondingPeriodContract

example : DistributedTendermintEpochTransitionSafetyMasterContractSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).distributed_suite.epoch_transition_master
example (r : MasterSuite.VerificationMasterRegistry) :
    DistributedTendermintEpochTransitionSafetyMasterContractSuite := r.distributed_suite.epoch_transition_master
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedTendermintEpochTransitionSafetyMasterContractSuite := r.distributed_systems_full_suite.epoch_transition_master
example {V : Type} [Fintype V] [DecidableEq V] (C : EpochTransitionMasterContext V)
    (hs : SafetyConditions C) : Agreement C := verification_suite.safety C hs
example {V : Type} [Fintype V] [DecidableEq V] (C : EpochTransitionMasterContext V) p B
    (hr : CollectionReady C p B) : (globalBlame C.context.old B).Nonempty ∧
    C.ledger.confiscated < (pipeline C p).ledger.confiscated := verification_suite.slashing C p B hr
example {V : Type} [Fintype V] [DecidableEq V] (C : EpochTransitionMasterContext V) p :
    totalValue (pipeline C p).ledger = totalValue C.ledger := (verification_suite.conservation C p).1
example {V : Type} [Fintype V] [DecidableEq V] (C : EpochTransitionMasterContext V) p
    (hw : WellFormed C.ledger) : WellFormed (pipeline C p).ledger := verification_suite.nonnegative C p hw
