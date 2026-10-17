import Verification.DistributedTendermintLockHandoverContract
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintEpochIdentityContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintLockHandoverContract
namespace TendermintLockHandoverRegression
set_option maxRecDepth 4096

abbrev old : EpochConfig (Fin 3) :=
  ⟨3, Function.Embedding.refl _, ![2, 1, 1], ∅, 10, 19, by decide⟩
abbrev next : EpochConfig (Fin 3) :=
  ⟨3, ⟨![2, 1, 0], by decide +kernel⟩, ![1, 1, 2], ∅, 10, 19, by decide⟩
abbrev ctx : Context (Fin 3) := ⟨4, 5, 12, old, next⟩
def packet (e r v : ℕ) (p : Phase) (S : Finset (Fin 3)) : Certificate 3 :=
  ⟨e, 12, r, v, p, S.image (fun i => ⟨i, r, p, some v⟩)⟩
def polkaOld := packet 4 17 7 .prevote {0, 1}
def commitOld := packet 4 17 7 .precommit {0, 1}
def commitNew := packet 5 0 7 .precommit {1, 2}
def freshPolka := packet 5 1 9 .prevote {1, 2}
def start := inherited ctx polkaOld
def advanced : LocalState := { start with round := 2 }
def changed : LocalState := { advanced with value := 9, lockedRound := 1 }
def states : Fin 3 → Option LocalState := fun u => adopt .strict ctx polkaOld u none

theorem accepted : Accept .strict ctx polkaOld := by decide +kernel
theorem adopted : Adoptions ctx ∅ commitOld polkaOld states :=
  adoptions_from_execution .strict ctx ∅ commitOld polkaOld accepted
theorem honest : HonestRoundZero ctx ∅ states commitNew.votes := by decide +kernel

example : Normalized (epochWeights old) ∧ Normalized (epochWeights next) := by decide +kernel
example : epochWeights old = epochWeights next := funext (by decide +kernel)
example : certificateSigners old polkaOld = {0, 1} := by decide +kernel
example : certificateSigners next commitNew = {0, 1} := by decide +kernel
example : mass (epochWeights old) (certificateSigners old commitOld) = 3/4 := by decide +kernel
example : checkHandover .strict ctx polkaOld = true := by decide +kernel
example : checkHandover .weak ctx polkaOld = true := by decide +kernel
example : checkHandover .strict ctx commitOld = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with epoch := 5 } = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with height := 13 } = false := by decide +kernel
example : checkHandover .strict { ctx with targetEpoch := 6 } polkaOld = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with votes := ∅ } = false := by decide +kernel
example : checkHandover .strict ctx (packet 4 17 7 .prevote {0}) = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with votes := polkaOld.votes ∪ polkaOld.votes }
    = true := by decide +kernel
example : (inherited ctx polkaOld).sourceRound = 17 ∧ start.lockedRound = 0 := by decide +kernel
example : adopt .strict ctx polkaOld 0 none = some start :=
  honest_node_lock_propagation .strict ctx polkaOld 0 accepted (by decide +kernel)
example : adopt .strict ctx polkaOld 0 (some start) = some start := by decide +kernel
example : adopt .strict ctx polkaOld 0 (some changed) = some changed := by decide +kernel
example : adopt .strict ctx commitOld 0 none = none := by decide +kernel
example : adopt .strict ctx polkaOld 0 (adopt .strict ctx polkaOld 0 none) =
    adopt .strict ctx polkaOld 0 none := adoption_replay_idempotent _ _ _ _ _
example : emit start (0 : Fin 3) .prevote (some 7) = some ⟨0, 0, .prevote, some 7⟩ :=
  by decide +kernel
example : emit start (0 : Fin 3) .precommit (some 9) = none :=
  inherited_conflict_rejected ctx polkaOld 0 .precommit 9 (by decide +kernel)
example : emit start (0 : Fin 3) .prevote (some 9) = none := by decide +kernel
example : emit start (0 : Fin 3) .prevote none = some ⟨0, 0, .prevote, none⟩ := by decide +kernel
example : commitNew.value = commitOld.value :=
  round_zero_safety_handover .strict ctx ∅ polkaOld commitOld commitNew states accepted
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) adopted honest
example : commitNew.value = commitOld.value :=
  round_zero_safety_handover .weak ctx ∅ polkaOld commitOld commitNew states
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) honest
example : MayReplace .strict ctx advanced freshPolka := by decide +kernel
example : replaceLock .strict ctx advanced freshPolka = some changed := by decide +kernel
example : replaceLock .strict ctx start freshPolka = none := round_zero_no_replacement _ _ _ _ rfl
example : replaceLock .strict ctx advanced { freshPolka with round := 0 } = none :=
  stale_polka_rejected _ _ _ _ (by decide +kernel)
example : replaceLock .strict ctx advanced { freshPolka with round := 2 } = none :=
  future_polka_rejected _ _ _ _ (by decide +kernel)
example : replaceLock .strict ctx advanced { freshPolka with epoch := 4 } = none := by decide +kernel
example : replaceLock .strict ctx advanced { freshPolka with height := 13 } = none := by decide +kernel
example : replaceLock .strict ctx advanced { freshPolka with phase := .precommit } = none :=
  by decide +kernel
example : replaceLock .strict ctx advanced { freshPolka with votes := ∅ } = none := by decide +kernel
example : replaceLock .strict ctx changed freshPolka = none := by decide +kernel
example : execute .strict ctx advanced (.advance 0) = none := by decide +kernel
example : execute .strict ctx start (.advance 2) = some advanced := by decide +kernel
example : execute .strict ctx advanced (.replace freshPolka) = some changed := by decide +kernel
example : ∃ a, MayReplace .strict ctx advanced a ∧ changed.value = a.value ∧
    advanced.lockedRound < a.round :=
  changed_value_has_certificate .strict ctx advanced (.replace freshPolka) changed
    (by decide +kernel) (by decide +kernel)
theorem changed_reachable : Reachable .strict ctx start changed :=
  .step (s := advanced) (.step .initial (.advance 2) (by decide +kernel))
    (.replace freshPolka) (by decide +kernel)
example : ∃ pre a, Reachable .strict ctx start pre ∧ MayReplace .strict ctx pre a ∧
    changed.value = a.value ∧ pre.lockedRound < a.round :=
  reachable_changed_value_justified .strict ctx start changed changed_reachable (by decide +kernel)
example : changed.epoch = start.epoch ∧ changed.height = start.height := by decide +kernel
example (s : LocalState) (h : Reachable .strict ctx start s) (hr : s.round = 0) : s.value = 7 :=
  reachable_round_zero_value .strict ctx start s h hr
example : changed.value ≠ start.value := by decide +kernel
example : ¬ Overlap .weak boundaryOld boundaryNew ∅ := by decide +kernel
example : Overlap .strict boundaryOld boundaryNew ∅ := by decide +kernel
example : Quorum .weak boundaryOld {0, 1} ∧ ¬ Quorum .strict boundaryOld {0, 1} := by decide +kernel
example : (old.atHeight 12).quorum {0, 1} := by decide +kernel
example : Quorum .strict (normalize (legacyWeights (old.atHeight 12))) {0, 1} ↔
    (old.atHeight 12).quorum {0, 1} := core_quorum_bridge _ _ (by decide +kernel)
example : (7 : ℕ) ≠ 9 := handover_omission_counterexample.2.2.2.2.2.2

abbrev narrow : EpochConfig (Fin 3) :=
  ⟨1, ⟨fun _ => 0, by intro a b _; exact Subsingleton.elim a b⟩,
    fun _ => 1, ∅, 10, 19, by decide⟩
example : adopt .strict { ctx with next := narrow } polkaOld 2 none = none := by decide +kernel
example : checkHandover .strict { ctx with old := { old with weight := fun _ => 0 } }
    polkaOld = false := by decide +kernel
example : checkHandover .strict { ctx with height := 20 }
    { polkaOld with height := 20 } = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with value := 9 } = false := by decide +kernel
example : checkHandover .strict ctx { polkaOld with round := 18 } = false := by decide +kernel

#eval [
  ("accepted", checkHandover .strict ctx polkaOld),
  ("weak accepted", checkHandover .weak ctx polkaOld),
  ("wrong phase", !checkHandover .strict ctx commitOld),
  ("wrong epoch", !checkHandover .strict ctx { polkaOld with epoch := 5 }),
  ("wrong height", !checkHandover .strict ctx { polkaOld with height := 13 }),
  ("wrong transition", !checkHandover .strict { ctx with targetEpoch := 6 } polkaOld),
  ("insufficient", !checkHandover .strict ctx (packet 4 17 7 .prevote {0})),
  ("permuted IDs", decide (certificateSigners next commitNew = certificateSigners old commitOld)),
  ("adopt", decide (adopt .strict ctx polkaOld 0 none = some start)),
  ("no reset", decide (adopt .strict ctx polkaOld 0 (some changed) = some changed)),
  ("prevote conflict", decide (emit start (0 : Fin 3) .prevote (some 9) = none)),
  ("precommit conflict", decide (emit start (0 : Fin 3) .precommit (some 9) = none)),
  ("nil", decide (voteAllowed start none)),
  ("newer polka", decide (replaceLock .strict ctx advanced freshPolka = some changed)),
  ("round zero", decide (replaceLock .strict ctx start freshPolka = none)),
  ("stale", decide (replaceLock .strict ctx advanced { freshPolka with round := 0 } = none)),
  ("future", decide (replaceLock .strict ctx advanced { freshPolka with round := 2 } = none)),
  ("foreign replacement", decide (replaceLock .strict ctx advanced { freshPolka with epoch := 4 } = none)),
  ("replay", decide (replaceLock .strict ctx changed freshPolka = none)),
  ("no rewind", decide (execute .strict ctx advanced (.advance 0) = none)),
  ("threshold boundary", decide (Quorum .weak boundaryOld {0, 1} ∧ ¬ Quorum .strict boundaryOld {0, 1})),
  ("omission", decide (¬ Adoptions unitContext ∅ (unitCertificate 0 4 .precommit 7)
      (unitCertificate 0 4 .prevote 7) omissionStates))]
end TendermintLockHandoverRegression
