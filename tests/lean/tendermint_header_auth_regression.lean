/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintHeaderChainEpochAuthContract
import Mathlib.Data.Fin.VecNotation
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintEpochIdentityContract DistributedTendermintUnbondingPeriodContract
open DistributedTendermintLockHandoverContract DistributedTendermintHandoverRoundInduction
open DistributedTendermintEpochTransitionSafetyMasterContract
open DistributedTendermintHeaderChainEpochAuthContract
namespace TendermintHeaderAuthRegression
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

/-- Exact tagged fixture encodings, not cryptographic hash implementations. -/
inductive Digest where
  | genesis
  | config (n : ℕ) (ids weights faulty : List ℕ) (first last : ℕ)
  | header (chain height epoch : ℕ) (current next parent : Digest)
  deriving DecidableEq, Repr

def configDigest (c : EpochConfig (Fin 3)) : Digest :=
  .config c.n (List.ofFn (fun i => (c.toGlobal i).val)) (List.ofFn c.weight)
    ((List.finRange c.n).filter (fun i => i ∈ c.byzantine) |>.map Fin.val)
    c.firstHeight c.lastHeight

def headerDigest (h : BlockHeader Digest) : Digest :=
  .header h.chainId h.height h.epochId h.validatorsHash h.nextValidatorsHash h.parentHeaderHash

def codec : Codec (Fin 3) Digest := ⟨configDigest, headerDigest⟩
theorem fixtureBinding : Binding codec := by
  constructor
  · intro a b he
    cases a with
    | mk an ai aw ab af al ao =>
      cases b with
      | mk bn bi bw bb bf bl bo =>
        obtain ⟨hn, hi, hw, hb, hf, hl⟩ := Digest.config.inj he
        dsimp at hn hi hw hb hf hl
        subst bn; subst bf; subst bl
        have hei : ai = bi := by
          ext i
          exact congrFun (List.ofFn_inj.mp hi) i
        have hew : aw = bw := List.ofFn_inj.mp hw
        have heb : ab = bb := by
          ext i
          have hm := congrArg (fun l : List ℕ => i.val ∈ l) hb
          simpa [Fin.val_inj] using hm
        subst bi; subst bw; subst bb
        rfl
  · intro a b he
    cases a; cases b
    simpa [codec, headerDigest] using he

def old : EpochConfig (Fin 3) :=
  ⟨2, ⟨![0,1], by decide +kernel⟩, ![8,6], {0}, 10, 17, by decide⟩
def next : EpochConfig (Fin 3) :=
  ⟨2, ⟨![2,1], by decide +kernel⟩, ![12,6], ∅, 18, 18, by decide⟩
def third : EpochConfig (Fin 3) :=
  ⟨2, ⟨![1,2], by decide +kernel⟩, ![6,12], ∅, 19, 40, by decide⟩
instance : NeZero old.n := ⟨by decide⟩
instance : NeZero next.n := ⟨by decide⟩
instance : NeZero third.n := ⟨by decide⟩
def root : Entry (Fin 3) Digest :=
  ⟨⟨7,17,0,configDigest old,configDigest next,.genesis⟩,old,next,∅⟩
def child : Entry (Fin 3) Digest :=
  ⟨⟨7,18,1,configDigest next,configDigest third,headerDigest root.header⟩,next,third,univ⟩
def tip : Entry (Fin 3) Digest :=
  ⟨⟨7,19,2,configDigest third,configDigest third,headerDigest child.header⟩,third,third,univ⟩
def signed : Authenticator (Fin 3) Digest := fun v h =>
  decide ((h = child.header ∧ v ∈ next.activeIds) ∨ (h = tip.header ∧ v ∈ third.activeIds))
def tail := [child,tip]

theorem verified : verifyChain codec signed root tail = true := by decide +kernel
example : verifyChain codec signed root [] = true := by decide +kernel
example : verifyChain codec signed root [child] = true := by decide +kernel
theorem prefixConsistency : CommitConsistency codec [root,child] (root :: tail) := by
  simp only [CommitConsistency,tail,List.mem_cons,forall_eq_or_imp]
  decide +kernel
example : resolveHistory (checkedHistory codec signed root [child]) 18 =
    resolveHistory (checkedHistory codec signed root tail) 18 :=
  authenticated_registry_agreement codec fixtureBinding signed root [child] tail
    (by decide +kernel) verified prefixConsistency 18 child child rfl rfl
example : child.current = root.next :=
  committed_config_no_substitution codec fixtureBinding signed root child
    (by decide +kernel) (by decide +kernel)
example : RootValid codec root := by decide +kernel
example : ¬ EntryValid codec signed root := by decide +kernel
example : EntryValid codec signed child ∧ EntryValid codec signed tip := by decide +kernel
example : child.header.epochId = 1 ∧ tip.header.epochId = 2 := by decide +kernel
example : resolveHistory (checkedHistory codec signed root tail) 17 = some old :=
  authenticated_lookup codec signed root tail verified 17 root rfl
example : resolveHistory (checkedHistory codec signed root tail) 18 = some next :=
  authenticated_lookup codec signed root tail verified 18 child rfl
example : resolveHistory (checkedHistory codec signed root tail) 19 = some third :=
  authenticated_lookup codec signed root tail verified 19 tip rfl
example : UnambiguousAt (checkedHistory codec signed root tail) 18 :=
  authenticated_lookup_bounds codec signed root tail verified 18 child rfl
-- Same covered height, different chain lengths; no extrapolation of the last interval.
example : resolveHistory (checkedHistory codec signed root [child]) 18 =
    resolveHistory (checkedHistory codec signed root tail) 18 := rfl
example : resolveHistory (checkedHistory codec signed root [child]) 19 = none :=
  uncovered_history_none codec signed root [child] 19 rfl
example : resolveHistory (checkedHistory codec signed root tail) 20 = none :=
  uncovered_history_none codec signed root tail 20 rfl
example : resolveHistory (checkedHistory codec signed root tail) 16 = none :=
  uncovered_history_none codec signed root tail 16 rfl

def wrongNext := {root with header := {root.header with nextValidatorsHash := configDigest third}}
def brokenParent := {child with header := {child.header with parentHeaderHash := .genesis}}
def wrongChain := {child with header := {child.header with chainId := 8}}
def skippedHeight := {child with header := {child.header with height := 19}}
def wrongEpoch := {child with header := {child.header with epochId := 2}}
def noSigners := {child with signers := ∅}
def exactTwoThirds : Entry (Fin 3) Digest := ⟨child.header,next,third,{0}⟩
def foreignSigner : Authenticator (Fin 3) Digest := fun v _ => decide (v = 0)
def noSignatures : Authenticator (Fin 3) Digest := fun _ _ => false
-- Keep the header, signatures, and local weights; alter the local-to-global identity map.
def changedIds : EpochConfig (Fin 3) :=
  ⟨2, ⟨![0,1], by decide +kernel⟩, ![12,6], ∅, 18, 18, by decide⟩
def forgedIds : Entry (Fin 3) Digest := {child with current := changedIds}
def changedWeights : EpochConfig (Fin 3) := {next with weight := ![13,6]}
def forgedWeights : Entry (Fin 3) Digest := {child with current := changedWeights}
def changedFaults : EpochConfig (Fin 3) := {next with byzantine := {0}}
def forgedFaults : Entry (Fin 3) Digest := {child with current := changedFaults}
example : verifyChain codec signed wrongNext tail = false := by decide +kernel
example : verifyChain codec signed root [brokenParent] = false := by decide +kernel
example : verifyChain codec signed root [wrongChain] = false := by decide +kernel
example : verifyChain codec signed root [skippedHeight] = false := by decide +kernel
example : verifyChain codec signed root [wrongEpoch] = false := by decide +kernel
example : verifyChain codec signed root [noSigners] = false := by decide +kernel
example : verifyChain codec signed root [exactTwoThirds] = false := by decide +kernel
example : verifyChain codec noSignatures root [child] = false := by decide +kernel
example : verifyChain codec foreignSigner root [child] = false := by decide +kernel
example : verifyChain codec signed root [forgedIds] = false := by decide +kernel
example : verifyChain codec signed root [forgedWeights] = false := by decide +kernel
example : verifyChain codec signed root [forgedFaults] = false := by decide +kernel
example : ¬ (LinkValid codec root forgedIds ∧ EntryValid codec signed forgedIds) :=
  forged_epoch_config_rejected codec signed root forgedIds (by decide +kernel)
example : checkedHistory codec signed root [brokenParent] 17 = [] :=
  rejected_chain_empty codec signed root [brokenParent] (by decide +kernel) 17
example : verifyFrom codec signed root [brokenParent] = false :=
  broken_parent_rejected codec signed root brokenParent [] (by decide +kernel)
example : verifyFrom codec signed root [wrongChain] = false :=
  wrong_chain_rejected codec signed root wrongChain [] (by decide +kernel)

-- An internally valid signed child with another current set is not authorized by the parent.
-- The relaxed predicate intentionally drops only the parent-selected current-set equality.
def replacedHeader := {child.header with validatorsHash := configDigest changedIds}
def replacement : Entry (Fin 3) Digest := {forgedIds with header := replacedHeader}
def allSigned : Authenticator (Fin 3) Digest := fun _ _ => true
def withoutNextBinding (a b : Entry (Fin 3) Digest) : Prop :=
  b.header.chainId = a.header.chainId ∧ b.header.height = a.header.height + 1 ∧
  b.header.parentHeaderHash = headerDigest a.header ∧ b.header.epochId = a.header.epochId + 1 ∧
  EntryValid codec allSigned b
instance (a b : Entry (Fin 3) Digest) : Decidable (withoutNextBinding a b) := by
  unfold withoutNextBinding; infer_instance
example : withoutNextBinding root replacement := by decide +kernel
example : ¬ LinkValid codec root replacement := by decide +kernel
example : replacement.current.toGlobal ⟨0,by decide⟩ ≠ root.next.toGlobal ⟨0,by decide⟩ := by decide +kernel
example : verifyChain codec allSigned root [replacement] = false := by decide +kernel
example : EntryValid codec allSigned brokenParent := by decide +kernel
example : ¬ LinkValid codec root brokenParent := by decide +kernel

-- Full signer quorums alone do not prove consistency between two competing branches.
def alternativeThird : EpochConfig (Fin 3) := {third with weight := ![7,12]}
def forkChild : Entry (Fin 3) Digest :=
  {child with
    next := alternativeThird
    header := {child.header with nextValidatorsHash := configDigest alternativeThird}}
def forkTip : Entry (Fin 3) Digest :=
  ⟨⟨7,19,2,configDigest alternativeThird,configDigest alternativeThird,headerDigest forkChild.header⟩,
    alternativeThird,alternativeThird,univ⟩
example : verifyChain codec allSigned root tail = true ∧
    verifyChain codec allSigned root [forkChild,forkTip] = true := by decide +kernel
example : tip.current.weight ⟨0,by decide⟩ = 6 ∧ forkTip.current.weight ⟨0,by decide⟩ = 7 := by decide +kernel
example : ¬ CommitConsistency codec (root :: tail) [root,forkChild,forkTip] := by
  intro hc
  have he := hc tip (by simp [tail]) forkTip (by simp) rfl rfl
  have hn : codec.headerHash tip.header ≠ codec.headerHash forkTip.header := by decide +kernel
  exact hn he

-- A colliding config encoder erases identity binding even with all structural checks enabled.
def collidingCodec : Codec (Fin 3) Digest := ⟨fun _ => .genesis,headerDigest⟩
def collidingRoot : Entry (Fin 3) Digest :=
  {root with header := {root.header with validatorsHash := .genesis,nextValidatorsHash := .genesis}}
def collidingChild : Entry (Fin 3) Digest :=
  {replacement with header := ⟨7,18,0,.genesis,.genesis,headerDigest collidingRoot.header⟩}
example : verifyChain collidingCodec allSigned collidingRoot [collidingChild] = true := by decide +kernel
example : collidingChild.current.toGlobal ⟨0,by decide⟩ ≠ collidingRoot.next.toGlobal ⟨0,by decide⟩ := by decide +kernel
example : ¬ Binding collidingCodec := by
  intro hb
  have he : changedIds = next := hb.config rfl
  have hx := congrArg (fun c : EpochConfig (Fin 3) => c.stakeMap 0) he
  have hn : changedIds.stakeMap 0 ≠ next.stakeMap 0 := by decide +kernel
  exact hn hx

-- Actual old-epoch equivocation, old validator absent from the new active set, deadline queue debit.
def w : Window := ⟨10, by decide⟩
def oldVotes : Finset (Vote 2) := {⟨0,0,.prevote,some 0⟩, ⟨0,0,.prevote,some 1⟩}
def payload : Payload 2 := ⟨some oldVotes, ⟨oldVotes.image (fun v => ⟨17,v⟩),∅⟩⟩
def before : UnbondingState (Fin 3) := ⟨17,.admission,![8,6,12],[],5,![0,0,0],∅⟩
def queued : UnbondingState (Fin 3) := {request_unbonding before 0 8 with now := 27}
def C : EpochTransitionMasterContext (Fin 3) where
  context := ⟨0,1,17,old,next⟩
  threshold := .strict
  faultSet := {0}
  sourcePolka := ⟨0,17,0,0,.prevote,{⟨0,0,.prevote,some 0⟩,⟨1,0,.prevote,some 0⟩}⟩
  sourceCommit := ⟨0,17,0,0,.precommit,{⟨0,0,.precommit,some 0⟩,⟨1,0,.precommit,some 0⟩}⟩
  adopted := fun _ => none
  transcript := ⟨1,17,∅⟩
  history := fun _ => []
  ledger := queued
  window := w
  rate := 1/2
def bound := bindHistory C codec signed root tail
def input : Input C := payload
instance : NeZero C.context.old.n := ⟨by decide⟩
instance : NeZero bound.context.old.n := ⟨by decide⟩
theorem admission : Admission C := by unfold Admission; decide +kernel
theorem wellFormed : WellFormed C.ledger :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
theorem attributed : attribute_evidence (C.context.old.atHeight 17) input.reference input.evidence =
    .ok {0} := by decide +kernel
theorem accepted : AcceptedEvidence bound input {0} :=
  authenticated_evidence C codec signed root tail verified root rfl rfl input {0} attributed
example : (globalBlame old {0}).Nonempty ∧ C.ledger.confiscated <
    (pipeline bound input).ledger.confiscated :=
  authenticated_slashing C codec signed root tail verified root rfl rfl input {0}
    attributed admission wellFormed ⟨0, by decide +kernel, by decide +kernel, by decide +kernel⟩
example : (pipeline C input).ledger.confiscated = 5 := by decide +kernel
example : (0 : Fin 3) ∉ next.activeIds := by decide +kernel
example : bound.context.old.toGlobal 0 = 0 ∧ bound.context.next.toGlobal ⟨0,by decide⟩ = 2 := by decide +kernel
example : (pipeline bound input).ledger.confiscated = 9 := by decide +kernel
example : (pipeline bound input).ledger.completed 0 = 4 := by decide +kernel
example : (pipeline bound input).ledger.processed = {(17,0)} := by decide +kernel
example : (pipeline bound input).ledger.queue = [] := by decide +kernel
example : totalValue (pipeline bound input).ledger = 31 := by decide +kernel
example : totalValue (pipeline bound input).ledger = totalValue bound.ledger := pipeline_conservation _ _
example : WellFormed (pipeline bound input).ledger := pipeline_wellFormed _ _ wellFormed
example : (pipeline bound input).ledger.active 2 = bound.ledger.active 2 ∧
    subjectValue (pipeline bound input).ledger 2 = subjectValue bound.ledger 2 :=
  cross_epoch_innocent_index_reuse_protection bound input {0} 2 accepted (by decide +kernel)
example : settle bound.window (applyHistorical bound.window 17 ⟨2,input⟩ bound.rate (debit bound input)) =
    pipeline bound input := duplicate_before_settlement bound input
example : applyHistorical bound.window 17 ⟨2,input⟩ bound.rate (pipeline bound input) =
    pipeline bound input := duplicate_after_settlement bound input

def corruptBound := bindHistory C codec signed root [brokenParent]
def pastWindow := {bound with ledger := {bound.ledger with now := 28}}
example : (pipeline corruptBound input).ledger.confiscated = 5 := by decide +kernel
example : (pipeline corruptBound input).ledger.completed 0 = 8 := by decide +kernel
example : (pipeline pastWindow input).ledger.confiscated = 5 := by decide +kernel
example : (pipeline pastWindow input).ledger.completed 0 = 8 := by decide +kernel

#eval [
  ("three epochs", verifyChain codec signed root tail),
  ("trusted anchor", verifyChain codec signed root []),
  ("strict quorum", decide (EntryValid codec signed child)),
  ("bad next commitment", !verifyChain codec signed wrongNext tail),
  ("broken parent", !verifyChain codec signed root [brokenParent]),
  ("wrong chain", !verifyChain codec signed root [wrongChain]),
  ("height gap", !verifyChain codec signed root [skippedHeight]),
  ("wrong epoch", !verifyChain codec signed root [wrongEpoch]),
  ("empty signers", !verifyChain codec signed root [noSigners]),
  ("exact two thirds", !verifyChain codec signed root [exactTwoThirds]),
  ("no signatures", !verifyChain codec noSignatures root [child]),
  ("foreign signer", !verifyChain codec foreignSigner root [child]),
  ("forged identities", !verifyChain codec signed root [forgedIds]),
  ("forged weights", !verifyChain codec signed root [forgedWeights]),
  ("forged fault annotation", !verifyChain codec signed root [forgedFaults]),
  ("removed next binding admits replacement", decide (withoutNextBinding root replacement)),
  ("full check rejects replacement", !verifyChain codec allSigned root [replacement]),
  ("unlinked signed entry", decide (EntryValid codec allSigned brokenParent)),
  ("full signer fork", verifyChain codec allSigned root [forkChild,forkTip]),
  ("colliding config substitution", verifyChain collidingCodec allSigned collidingRoot [collidingChild]),
  ("actual historical evidence", decide (attribute_evidence (old.atHeight 17)
    input.reference input.evidence = .ok {0})),
  ("old subject exited", decide ((0 : Fin 3) ∉ next.activeIds)),
  ("without checked history no debit", decide ((pipeline C input).ledger.confiscated = 5)),
  ("authenticated debit", decide ((pipeline bound input).ledger.confiscated = 9)),
  ("deadline payout", decide ((pipeline bound input).ledger.completed 0 = 4)),
  ("innocent new owner", decide ((pipeline bound input).ledger.active 2 = 12)),
  ("value conservation", decide (totalValue (pipeline bound input).ledger = 31)),
  ("processed global key", decide ((pipeline bound input).ledger.processed = {(17,0)})),
  ("rejected chain no debit", decide ((pipeline corruptBound input).ledger.confiscated = 5)),
  ("rejected chain payout", decide ((pipeline corruptBound input).ledger.completed 0 = 8)),
  ("expired evidence no debit", decide ((pipeline pastWindow input).ledger.confiscated = 5))]
end TendermintHeaderAuthRegression
