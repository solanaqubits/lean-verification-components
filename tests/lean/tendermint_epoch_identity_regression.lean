import Verification.DistributedTendermintEpochIdentityContract
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintUnbondingPeriodContract DistributedTendermintEpochIdentityContract
namespace TendermintEpochIdentityRegression
set_option maxRecDepth 4096
set_option synthInstance.maxSize 2048

def old : EpochConfig (Fin 3) :=
  ⟨2, ⟨![0, 1], by decide +kernel⟩, ![8, 6], {0}, 10, 19, by decide⟩
def next : EpochConfig (Fin 3) :=
  ⟨2, ⟨![2, 1], by decide +kernel⟩, ![12, 6], ∅, 20, 29, by decide⟩
def expanded : EpochConfig (Fin 3) :=
  ⟨3, Function.Embedding.refl _, ![0, 6, 12], ∅, 30, 39, by decide⟩
def window : Window := ⟨10, by decide⟩
def votes (i : Fin 2) : Finset (Vote 2) :=
  {⟨i, 0, .prevote, some 0⟩, ⟨i, 0, .prevote, some 1⟩}
def payload (h : ℕ) (i : Fin 2) : Payload 2 :=
  ⟨some (votes i), ⟨(votes i).image (fun v => ⟨h, v⟩), ∅⟩⟩
def packet : Packet := ⟨2, payload 17 0⟩
def history : HistoryRegistry (Fin 3) := fun h => if h = 17 then [old] else []
def initialLedger : UnbondingState (Fin 3) :=
  ⟨17, .admission, ![8, 6, 12], [], 5, ![0, 0, 0], ∅⟩
def requested := request_unbonding initialLedger 0 8
def base : EpochState (Fin 3) := ⟨old, history, {requested with now := 27}⟩
def changed := epoch_transition base next
def after := applyHistorical window 17 packet (1/2) changed
def full := applyHistorical window 17 packet 1 changed
def paid := finalize_unbonding window (close_admission after.ledger)
def honestPaid := finalize_unbonding window (close_admission changed.ledger)
def observed (s : EpochState (Fin 3)) :=
  (s.ledger.active 0, s.ledger.active 1, s.ledger.active 2,
   s.ledger.queue, s.ledger.confiscated, s.ledger.processed)
def runPacket (p : Packet) (s : EpochState (Fin 3)) := applyHistorical window 17 p (1/2) s

def perm : Equiv.Perm (Fin 2) := Equiv.swap 0 1
def permuted := reindex old perm
def permHistory : HistoryRegistry (Fin 3) := fun h => if h = 17 then [permuted] else []
def permState := { changed with history := permHistory }
def permPacket : Packet := ⟨2, payload 17 1⟩
def missing := {changed with history := fun _ => []}
def ambiguous := {changed with history := fun _ => [old, next]}
def duplicate := {changed with history := fun _ => [old, old]}
def outOfBounds := {changed with history := fun _ => [next]}
def largePacket : Packet := ⟨3, ⟨some ∅, ⟨∅, ∅⟩⟩⟩
def noReference : Packet := ⟨2, {payload 17 0 with reference := none}⟩
def future := {changed with ledger := {changed.ledger with now := 16}}
def expired := {changed with ledger := {changed.ledger with now := 28}}
def closed := {changed with ledger := close_admission changed.ledger}

instance : NeZero old.n := ⟨by decide⟩
instance : NeZero next.n := ⟨by decide⟩
instance : NeZero permuted.n := ⟨by decide⟩

example : old.toGlobal 0 = 0 ∧ next.toGlobal 0 = 2 := by decide +kernel
example : old.toGlobal 0 ≠ next.toGlobal 0 := by decide +kernel
example : (2 : Fin 3) ∉ old.activeIds := by decide +kernel
example : old.stakeMap 0 = 8 ∧ old.stakeMap 1 = 6 ∧ old.stakeMap 2 = 0 := by decide +kernel
example : resolveHistory history 17 = some old := by rfl
example : checkPacket old 17 packet = some {0} := by decide +kernel
example : historicalBlame history 17 packet = some {0} := by decide +kernel
example : attribute_evidence (old.atHeight 17) (some (votes 0)) (payload 17 0).evidence =
    .ok {0} := by decide +kernel
example : globalBlame old {0} = {0} := by decide +kernel
example : globalBlame next {0} = {2} := by decide +kernel
-- Mutation witness: interpreting an old index through the current map charges a different subject.
example : globalBlame old {0} ≠ globalBlame next {0} := by decide +kernel
example : changed.ledger = base.ledger := rfl
example : changed.history = base.history := rfl
example : changed.ledger.queue = [⟨0, 8, 17⟩] := by decide +kernel
example : after.ledger.queue = [⟨0, 4, 17⟩] := by decide +kernel
example : after.ledger.active 2 = 12 := by decide +kernel
example : after.ledger.active 1 = 6 := by decide +kernel
example : after.ledger.confiscated = 9 := by decide +kernel
example : after.ledger.processed = {(17, 0)} := by decide +kernel
example : (17, (2 : Fin 3)) ∉ after.ledger.processed := by decide +kernel
example : paid.completed 0 = 4 ∧ paid.completed 2 = 0 := by decide +kernel
example : honestPaid.completed 0 = 8 := by decide +kernel
example : full.ledger.queue = [⟨0, 0, 17⟩] ∧ full.ledger.confiscated = 13 := by decide +kernel
example : observed (runPacket packet after) = observed after := by decide +kernel
example : runPacket packet after = after := historical_replay _ _ _ _ _
example : observed (runPacket packet (epoch_transition after expanded)) = observed after := by decide +kernel
example : observed (applyHistorical window 17 packet 1 after) = observed after := by decide +kernel
example : permuted.toGlobal 1 = old.toGlobal 0 := by decide +kernel
example : permuted.weight 1 = 8 ∧ permuted.weight 0 = 6 := by decide +kernel
example : attribute_evidence (permuted.atHeight 17) (some (votes 1)) (payload 17 1).evidence =
    .ok {1} := by decide +kernel
example : historicalBlame permHistory 17 permPacket = some {0} := by decide +kernel
example : observed (runPacket permPacket permState) = observed after := by decide +kernel
example : permuted.stakeMap 0 = old.stakeMap 0 := permutation_stakeMap _ _ _
example : historicalBlame missing.history 17 packet = none := by rfl
example : observed (runPacket packet missing) = observed missing := by decide +kernel
example : observed (runPacket packet ambiguous) = observed ambiguous := by decide +kernel
example : observed (runPacket packet duplicate) = observed duplicate := by decide +kernel
example : observed (runPacket packet outOfBounds) = observed outOfBounds := by decide +kernel
example : checkPacket old 17 largePacket = none := by rfl
example : observed (runPacket largePacket changed) = observed changed := by decide +kernel
example : observed (runPacket ⟨2, payload 18 0⟩ changed) = observed changed := by decide +kernel
example : observed (runPacket noReference changed) = observed changed := by decide +kernel
example : observed (runPacket packet future) = observed future := by decide +kernel
example : observed (runPacket packet expired) = observed expired := by decide +kernel
example : observed (runPacket packet closed) = observed closed := by decide +kernel
example : observed (applyHistorical window 17 packet 0 changed) = observed changed := by decide +kernel
example : observed (applyHistorical window 17 packet 2 changed) = observed changed := by decide +kernel
example : totalValue after.ledger = 31 := by decide +kernel
example : totalValue after.ledger = totalValue changed.ledger := historical_conservation _ _ _ _ _
example : totalValue paid = 31 := by decide +kernel
example : ownedQueue after.ledger 2 = ownedQueue changed.ledger 2 := by decide +kernel
-- Being distinct from one culprit does not prove innocence of all culprits.
example : old.toGlobal 0 ≠ old.toGlobal 1 ∧ old.toGlobal 1 ∈ globalBlame old {0, 1} := by decide +kernel
example : WellFormed after.ledger := historical_wellFormed _ _ _ _ _
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

def actions : List (Action 2) :=
  [.faulty ⟨0, 0, .prevote, some 0⟩, .faulty ⟨0, 0, .prevote, some 1⟩]
def reached : State 2 := (run (old.atHeight 17) initial actions).getD initial
theorem execution : run (old.atHeight 17) initial actions = some reached := by
  change run (⟨![8, 6], {0}, 17⟩ : Config 2) initial actions = some reached
  decide +kernel
theorem reachable : Reachable (old.atHeight 17) reached := run_reachable _ _ Reachable.init execution
example : reached.votes = votes 0 := by decide +kernel
example : old.toGlobal 1 ∉ globalBlame old {0} := historical_honest_unaccused old 17 reachable
  (payload 17 0).evidence {0} 1 (by decide +kernel) (by decide +kernel)
example : changed.ledger.confiscated < after.ledger.confiscated :=
  unbonding_slashing_cross_epoch_soundness window 17 (1/2) base next old (payload 17 0)
    {0} 0 rfl (by decide +kernel) (by decide +kernel)
    ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩
    (by decide) (by decide +kernel) (by decide +kernel)
example : after.ledger.active 2 = changed.ledger.active 2 :=
  (new_validator_reused_index_safety window 17 (1/2) changed old (payload 17 0) {0} 2
    rfl (by decide +kernel) (by decide +kernel)).1
example : paid.completed 0 = 4 := by
  have he := historical_deadline_precedence window 17 (1/2) changed old (payload 17 0)
    {0} ⟨0, 8, 17⟩ rfl (by decide +kernel) (by decide +kernel) rfl
    (by decide +kernel) (by decide +kernel) (by decide) rfl rfl
  change paid.completed 0 = (0 : ℚ) + (1 - 1/2) * 8 at he
  norm_num at he
  exact he

#eval [("accepted", decide (historicalBlame history 17 packet = some {0})),
  ("reused index", decide (after.ledger.active 2 = 12)),
  ("old queue", decide (after.ledger.queue = [⟨0, 4, 17⟩])),
  ("deadline", decide (paid.completed 0 = 4)),
  ("full", decide (full.ledger.confiscated = 13)),
  ("replay", decide (observed (runPacket packet (epoch_transition after expanded)) = observed after)),
  ("permutation", decide (observed (runPacket permPacket permState) = observed after)),
  ("missing", decide (observed (runPacket packet missing) = observed missing)),
  ("ambiguous", decide (observed (runPacket packet ambiguous) = observed ambiguous)),
  ("duplicate", decide (observed (runPacket packet duplicate) = observed duplicate)),
  ("bounds", decide (observed (runPacket packet outOfBounds) = observed outOfBounds)),
  ("dimension", decide (observed (runPacket largePacket changed) = observed changed)),
  ("envelope", decide (observed (runPacket ⟨2, payload 18 0⟩ changed) = observed changed)),
  ("reference", decide (observed (runPacket noReference changed) = observed changed)),
  ("future", decide (observed (runPacket packet future) = observed future)),
  ("expired", decide (observed (runPacket packet expired) = observed expired)),
  ("phase", decide (observed (runPacket packet closed) = observed closed)),
  ("rate", decide (observed (applyHistorical window 17 packet 2 changed) = observed changed)),
  ("conservation", decide (totalValue paid = 31)),
  ("reachable", (run (old.atHeight 17) initial actions).isSome)]
end TendermintEpochIdentityRegression
