import Verification.MasterSuite
open DistributedTendermintLockHandoverContract

example : DistributedTendermintLockHandoverContractSuite :=
  (MasterSuite.verification_master_registry.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0}).distributed_suite.lock_handover
example (r : MasterSuite.VerificationMasterRegistry) : DistributedTendermintLockHandoverContractSuite :=
  r.distributed_suite.lock_handover
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedTendermintLockHandoverContractSuite := r.distributed_systems_full_suite.lock_handover
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) a u
    (ha : Accept m c a) (hu : u ∈ c.next.activeIds) :
    adopt m c a u none = some (inherited c a) := verification_suite.adoption m c a u ha hu
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) start s
    (hs : Reachable m c start s) (hr : s.round = 0) : s.value = start.value :=
  verification_suite.round_zero m c start s hs hr
example {V : Type} [Fintype V] [DecidableEq V] m (c : Context V) s a t
    (he : replaceLock m c s a = some t) :
    MayReplace m c s a ∧ t = { s with value := a.value, lockedRound := a.round } :=
  verification_suite.replacement m c s a t he
