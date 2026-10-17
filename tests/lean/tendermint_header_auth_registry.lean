/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.MasterSuite
open DistributedTendermintHeaderChainEpochAuthContract

example : DistributedTendermintHeaderChainEpochAuthContractSuite :=
  (MasterSuite.verification_master_registry.{0,0,0,0,0,0,0,0,0,0}).distributed_suite.header_chain_auth
example (r : MasterSuite.VerificationMasterRegistry) :
    DistributedTendermintHeaderChainEpochAuthContractSuite := r.distributed_suite.header_chain_auth
example (r : MasterHundredRegistry.MasterHundredFormalSuite) :
    DistributedTendermintHeaderChainEpochAuthContractSuite := r.distributed_systems_full_suite.header_chain_auth

open DistributedTendermintEpochIdentityContract DistributedTendermintUnbondingPeriodContract
open DistributedTendermintEpochTransitionSafetyMasterContract

example {V D : Type} [DecidableEq D] (codec : Codec V D) signed root tail
    (hv : verifyChain codec signed root tail = true) h a
    (hl : lookup h (root :: tail) = some a) :
    resolveHistory (checkedHistory codec signed root tail) h = some a.current :=
  DistributedTendermintHeaderChainEpochAuthContract.verification_suite.lookup
    codec signed root tail hv h a hl
example {V D : Type} [DecidableEq D] (codec : Codec V D) (binding : Binding codec)
    signed root left right (hl : verifyChain codec signed root left = true)
    (hr : verifyChain codec signed root right = true)
    (hc : CommitConsistency codec (root :: left) (root :: right)) h a b
    (ha : lookup h (root :: left) = some a) (hb : lookup h (root :: right) = some b) :
    resolveHistory (checkedHistory codec signed root left) h =
      resolveHistory (checkedHistory codec signed root right) h :=
  DistributedTendermintHeaderChainEpochAuthContract.verification_suite.uniqueness
    codec binding signed root left right hl hr hc h a b ha hb
example {V D : Type} [DecidableEq D] (codec : Codec V D) (binding : Binding codec)
    signed parent child (hp : RootValid codec parent)
    (hc : LinkValid codec parent child ∧ EntryValid codec signed child) : child.current = parent.next :=
  DistributedTendermintHeaderChainEpochAuthContract.verification_suite.substitution
    codec binding signed parent child hp hc
example {V D : Type} [DecidableEq D] [DecidableEq V] [Fintype V]
    (C : EpochTransitionMasterContext V) (codec : Codec V D) signed root tail (p : Input C) :
    totalValue (pipeline (bindHistory C codec signed root tail) p).ledger = totalValue C.ledger :=
  (DistributedTendermintHeaderChainEpochAuthContract.verification_suite.conservation_replay
    C codec signed root tail p).1
