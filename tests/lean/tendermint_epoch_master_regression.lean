import Verification.DistributedTendermintEpochTransitionSafetyMasterContract
import Mathlib.Data.Fin.VecNotation
open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintEpochIdentityContract DistributedTendermintUnbondingPeriodContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintLockHandoverContract DistributedTendermintHandoverRoundInduction
open DistributedTendermintEpochTransitionSafetyMasterContract
namespace TendermintEpochMasterRegression
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

def old : EpochConfig (Fin 3) :=
  ⟨2, ⟨![0, 1], by decide +kernel⟩, ![8, 6], {0}, 10, 19, by decide⟩
def next : EpochConfig (Fin 3) :=
  ⟨2, ⟨![2, 1], by decide +kernel⟩, ![12, 6], ∅, 20, 29, by decide⟩
instance : NeZero old.n := ⟨by decide⟩
instance : NeZero next.n := ⟨by decide⟩
def w : Window := ⟨10, by decide⟩
def oldVotes : Finset (Vote 2) := {⟨0, 0, .prevote, some 0⟩, ⟨0, 0, .prevote, some 1⟩}
def payload : Payload 2 := ⟨some oldVotes, ⟨oldVotes.image (fun v => ⟨17, v⟩), ∅⟩⟩
def history : HistoryRegistry (Fin 3) := fun h => if h = 17 then [old] else []
def before : UnbondingState (Fin 3) := ⟨17, .admission, ![8, 6, 12], [], 5, ![0, 0, 0], ∅⟩
def queued : UnbondingState (Fin 3) := {request_unbonding before 0 8 with now := 27}
def oldPolka : Certificate 2 :=
  ⟨0, 17, 0, 0, .prevote, {⟨0, 0, .prevote, some 0⟩, ⟨1, 0, .prevote, some 0⟩}⟩
def oldCommit : Certificate 2 :=
  ⟨0, 17, 0, 0, .precommit, {⟨0, 0, .precommit, some 0⟩, ⟨1, 0, .precommit, some 0⟩}⟩
def badHistory : Transcript 2 :=
  ⟨1, 17, {⟨0, 1, .precommit, some 9⟩, ⟨1, 1, .precommit, some 9⟩}⟩
def C : EpochTransitionMasterContext (Fin 3) where
  context := ⟨0, 1, 17, old, next⟩
  threshold := .strict
  faultSet := {0}
  sourcePolka := oldPolka
  sourceCommit := oldCommit
  adopted := fun _ => none
  transcript := badHistory
  history := history
  ledger := queued
  window := w
  rate := 1/2
instance : NeZero C.context.next.n := ⟨by decide⟩
instance : NeZero C.context.old.n := ⟨by decide⟩
def input : Input C := payload

theorem accepted : AcceptedEvidence C input {0} := ⟨rfl, by decide +kernel⟩
theorem ready : CollectionReady C input {0} := by
  refine ⟨accepted, ?_, ?_, 0, ?_, ?_, ?_⟩
  · unfold Admission; decide +kernel
  · exact ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel

example : C.context.old.toGlobal 0 = 0 ∧ C.context.next.toGlobal 0 = 2 := by decide +kernel
example : (0 : Fin 3) ∉ C.context.next.activeIds := by decide +kernel
example : queued.active 0 = 0 ∧ queued.queue = [⟨0, 8, 17⟩] := by decide +kernel
example : available C.ledger 17 0 = 8 := by decide +kernel
example : (debit C input).ledger.queue = [⟨0, 4, 17⟩] := by decide +kernel
example : (pipeline C input).ledger.queue = [] := by decide +kernel
example : (pipeline C input).ledger.confiscated = 9 := by decide +kernel
example : (pipeline C input).ledger.completed 0 = 4 := by decide +kernel
example : (pipeline C input).ledger.active 2 = 12 := by decide +kernel
example : subjectValue (pipeline C input).ledger 2 = 12 := by decide +kernel
example : totalValue (pipeline C input).ledger = 31 := by decide +kernel
example : (pipeline C input).ledger.processed = {(17, 0)} := by decide +kernel
example : (pipeline C input).ledger.phase = .withdrawal := by decide +kernel
example : (pipeline C input).ledger.now = 27 := by decide +kernel
example : (globalBlame C.context.old {0}).Nonempty ∧
    C.ledger.confiscated < (pipeline C input).ledger.confiscated :=
  cross_epoch_accountable_slashing_branch C input {0} ready
example : totalValue (pipeline C input).ledger = totalValue C.ledger := pipeline_conservation _ _
example : WellFormed (pipeline C input).ledger := pipeline_wellFormed _ _ ready.2.2.1
example : (pipeline C input).ledger.active 2 = C.ledger.active 2 ∧
    subjectValue (pipeline C input).ledger 2 = subjectValue C.ledger 2 :=
  cross_epoch_innocent_index_reuse_protection C input {0} 2 accepted (by decide +kernel)
example : (pipeline C input).ledger.completed 0 = C.ledger.completed 0 + (1-C.rate)*8 :=
  master_deadline_payout C input {0} ⟨0, 8, 17⟩ accepted ready.2.1 rfl
    (by decide +kernel) (by decide +kernel) (by decide) rfl rfl
example : settle C.window (applyHistorical C.window 17 ⟨2, input⟩ C.rate (debit C input)) =
    pipeline C input := duplicate_before_settlement C input
example : applyHistorical C.window 17 ⟨2, input⟩ C.rate (pipeline C input) =
    pipeline C input := duplicate_after_settlement C input
example : Commit C.threshold C.context C.transcript 1 9 := by decide +kernel
example : ¬ Agreement C := by intro h; have hx := h 1 9 (by decide +kernel); change 9 = 0 at hx; omega
-- Coverage is supplied explicitly, not inferred from the target conflict.
theorem covered : ConflictCovered C := fun _ _ _ _ => ⟨input, {0}, ready⟩
example : Agreement C ∨ ∃ p B, CollectionReady C p B ∧ (globalBlame C.context.old B).Nonempty ∧
    C.ledger.confiscated < (pipeline C p).ledger.confiscated :=
  cross_epoch_safety_or_slashing_dichotomy C covered

def full := {C with rate := 1}
def late := {C with ledger := {C.ledger with now := 28}}
def future := {C with ledger := {C.ledger with now := 16}}
def closed := {C with ledger := close_admission C.ledger}
def stale := {C with ledger := {C.ledger with processed := {(17, 0)}}}
def zeroStake := {C with ledger := {C.ledger with active := fun _ => 0, queue := []}}
def absent := {C with history := fun _ => []}
def ambiguous := {C with history := fun _ => [old, next]}
def noRef : Input C := {input with reference := none}
def wrongHeight : Input C := {input with evidence := ⟨oldVotes.image (fun v => ⟨18, v⟩), ∅⟩}
def laterTranche := {C with ledger := {C.ledger with queue := [⟨0, 8, 16⟩]}}
def honestQueue := {C with ledger := {C.ledger with queue := [⟨0, 8, 17⟩, ⟨2, 12, 17⟩], active := ![0,6,0]}}
instance : NeZero late.context.old.n := ⟨by decide⟩
instance : NeZero honestQueue.context.old.n := ⟨by decide⟩
example : (pipeline full input).ledger.confiscated = 13 ∧ (pipeline full input).ledger.completed 0 = 0 := by decide +kernel
example : (debit late input).ledger = late.ledger := expired_debit_noop _ _ (by decide +kernel)
example : (pipeline late input).ledger.confiscated = 5 ∧ (pipeline late input).ledger.completed 0 = 8 := by decide +kernel
example : ¬ CollectionReady late input {0} := expired_collection_impossible _ _ _ (by decide +kernel)
example : ¬ ConflictCovered late := uncovered_expired_conflict late 1 9 (by decide +kernel)
  (by decide +kernel) (by decide +kernel)
example : (debit future input).ledger.confiscated = 5 := by decide +kernel
example : (debit closed input).ledger.confiscated = 5 := by decide +kernel
example : (debit stale input).ledger.confiscated = 5 := by decide +kernel
example : (debit zeroStake input).ledger.confiscated = 5 := by decide +kernel
example : (pipeline absent input).ledger.completed 0 = 8 := by decide +kernel
example : (pipeline ambiguous input).ledger.confiscated = 5 := by decide +kernel
example : (debit C noRef).ledger.confiscated = 5 := by decide +kernel
example : (debit C wrongHeight).ledger.confiscated = 5 := by decide +kernel
example : available laterTranche.ledger 17 0 = 0 := by decide +kernel
example : (pipeline laterTranche input).ledger.completed 0 = 8 := by decide +kernel
example : (pipeline honestQueue input).ledger.completed 2 = 12 := by decide +kernel
example : subjectValue (pipeline honestQueue input).ledger 2 = subjectValue honestQueue.ledger 2 :=
  (cross_epoch_innocent_index_reuse_protection honestQueue input {0} 2 accepted (by decide +kernel)).2

-- A genuinely satisfiable safe path with a complete adopted lock and later-round commits.
def H : Transcript 1 := ⟨1, 5, {⟨0, 0, .prevote, some 7⟩, ⟨0, 0, .precommit, some 7⟩,
  ⟨0, 3, .prevote, some 7⟩, ⟨0, 3, .precommit, some 7⟩}⟩
def safe : EpochTransitionMasterContext (Fin 1) where
  context := unitContext
  threshold := .strict
  faultSet := ∅
  sourcePolka := unitCertificate 0 17 .prevote 7
  sourceCommit := unitCertificate 0 17 .precommit 7
  adopted := fun u => adopt .strict unitContext (unitCertificate 0 17 .prevote 7) u none
  transcript := H
  history := fun _ => [unitConfig]
  ledger := ⟨15, .admission, fun _ => 0, [⟨0, 8, 5⟩], 0, fun _ => 0, ∅⟩
  window := w
  rate := 1/2
def honestInput : Input safe := ⟨some ∅, ⟨∅, ∅⟩⟩
theorem safety : SafetyConditions safe := by
  constructor <;> decide +kernel
example : Agreement safe := cross_epoch_master_safety_branch safe safety
example : ∀ r x, Commit safe.threshold safe.context safe.transcript r x → x = 7 :=
  cross_epoch_master_safety_branch safe safety
example : Commit safe.threshold safe.context safe.transcript 0 7 := by decide +kernel
example : Commit safe.threshold safe.context safe.transcript 3 7 := by decide +kernel
example : (pipeline safe honestInput).ledger.completed 0 = 8 := by decide +kernel
example : (pipeline safe honestInput).ledger.confiscated = 0 := by decide +kernel
example : subjectValue (pipeline safe honestInput).ledger 0 = 8 := by decide +kernel

-- Actual same-configuration fork evidence feeds the attribution checker.
def forkVotes : Finset (Vote 1) := {⟨0, 0, .prevote, some 0⟩, ⟨0, 0, .prevote, some 1⟩,
  ⟨0, 0, .precommit, some 0⟩, ⟨0, 0, .precommit, some 1⟩}
def forkView : EvidenceView 1 := ⟨forkVotes.image (fun v => ⟨5, v⟩), ∅⟩
example : checkPacket unitConfig 5 ⟨1, ⟨some forkVotes, forkView⟩⟩ =
    some (globalBlame unitConfig (culprits (unitConfig.atHeight 5) forkView.votes)) ∧
    (globalBlame unitConfig (culprits (unitConfig.atHeight 5) forkView.votes)).Nonempty :=
  historical_fork_global_blame unitConfig 5 forkVotes forkView ⟨by decide +kernel, by decide +kernel⟩ 0 0 0 1
    (by decide +kernel) (by decide +kernel) (by decide)

-- Nonzero admissible weight shift: TV=1/4, common honest mass=3/4.
def weightedOld : EpochConfig (Fin 3) :=
  ⟨3, Function.Embedding.refl _, ![2,1,1], ∅, 0, 100, by decide⟩
def weightedNext : EpochConfig (Fin 3) :=
  ⟨3, Function.Embedding.refl _, ![1,1,2], ∅, 0, 100, by decide⟩
def allVotes (p : DistributedTendermintCoreSafety.Phase) (r : ℕ) : Finset (Vote 3) :=
  univ.image (fun i => ⟨i, r, p, some 7⟩)
def weightedContext : Context (Fin 3) := ⟨0,1,5,weightedOld,weightedNext⟩
def weightedPolka : Certificate 3 := ⟨0,5,17,7,.prevote,allVotes .prevote 17⟩
def weightedSafe : EpochTransitionMasterContext (Fin 3) where
  context := weightedContext
  threshold := .strict
  faultSet := ∅
  sourcePolka := weightedPolka
  sourceCommit := ⟨0,5,17,7,.precommit,allVotes .precommit 17⟩
  adopted := fun u => adopt .strict weightedContext weightedPolka u none
  transcript := ⟨1,5,allVotes .prevote 0 ∪ allVotes .precommit 0 ∪
    allVotes .prevote 4 ∪ allVotes .precommit 4⟩
  history := fun _ => [weightedOld]
  ledger := ⟨15,.admission,fun _ => 1,[],0,fun _ => 0,∅⟩
  window := w
  rate := 1/2
theorem weighted_safety : SafetyConditions weightedSafe := by constructor <;> decide +kernel
example : variation (epochWeights weightedOld) (epochWeights weightedNext) = 1/4 := by decide +kernel
example : honestCommon (epochWeights weightedOld) (epochWeights weightedNext) ∅ = 3/4 := by decide +kernel
example : Agreement weightedSafe := cross_epoch_master_safety_branch weightedSafe weighted_safety
example : Commit weightedSafe.threshold weightedSafe.context weightedSafe.transcript 0 7 := by decide +kernel
example : Commit weightedSafe.threshold weightedSafe.context weightedSafe.transcript 4 7 := by decide +kernel

#eval [
  ("nonzero weight shift", decide (variation (epochWeights weightedOld) (epochWeights weightedNext) = 1/4)),
  ("shifted later commit", decide (Commit weightedSafe.threshold weightedSafe.context weightedSafe.transcript 4 7)),
  ("historical attribution", decide (attribute_evidence (old.atHeight 17) input.reference input.evidence = .ok {0})),
  ("global identity", decide (globalBlame old {0} = {0} ∧ globalBlame next {0} = {2})),
  ("left membership", decide ((0 : Fin 3) ∉ next.activeIds)),
  ("queued liability", decide (available C.ledger 17 0 = 8)),
  ("half debit", decide ((pipeline C input).ledger.confiscated = 9)),
  ("deadline payout", decide ((pipeline C input).ledger.completed 0 = 4)),
  ("innocent balance", decide ((pipeline C input).ledger.active 2 = 12)),
  ("conservation", decide (totalValue (pipeline C input).ledger = 31)),
  ("processed", decide ((pipeline C input).ledger.processed = {(17, 0)})),
  ("full debit", decide ((pipeline full input).ledger.confiscated = 13)),
  ("expired no debit", decide ((pipeline late input).ledger.confiscated = 5)),
  ("expired payout", decide ((pipeline late input).ledger.completed 0 = 8)),
  ("future", decide ((debit future input).ledger.confiscated = 5)),
  ("closed", decide ((debit closed input).ledger.confiscated = 5)),
  ("stale", decide ((debit stale input).ledger.confiscated = 5)),
  ("zero stake", decide ((debit zeroStake input).ledger.confiscated = 5)),
  ("missing history", decide ((debit absent input).ledger.confiscated = 5)),
  ("ambiguous history", decide ((debit ambiguous input).ledger.confiscated = 5)),
  ("missing reference", decide ((debit C noRef).ledger.confiscated = 5)),
  ("wrong height", decide ((debit C wrongHeight).ledger.confiscated = 5)),
  ("not liable tranche", decide ((pipeline laterTranche input).ledger.completed 0 = 8)),
  ("honest payout", decide ((pipeline honestQueue input).ledger.completed 2 = 12)),
  ("safe round zero", decide (Commit safe.threshold safe.context safe.transcript 0 7)),
  ("safe later round", decide (Commit safe.threshold safe.context safe.transcript 3 7)),
  ("safe withdrawal", decide ((pipeline safe honestInput).ledger.completed 0 = 8))]
end TendermintEpochMasterRegression
