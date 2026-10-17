import Verification.DistributedTendermintHandoverRoundInduction
open Finset DistributedTendermintCoreSafety DistributedTendermintEpochIdentityContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintLockHandoverContract DistributedTendermintHandoverRoundInduction
namespace TendermintHandoverInductionRegression
set_option maxRecDepth 4096

def good : Transcript 1 := ⟨1, 5,
  {⟨0, 0, .prevote, some 7⟩, ⟨0, 0, .precommit, some 7⟩,
   ⟨0, 1, .prevote, some 7⟩, ⟨0, 1, .precommit, some 7⟩,
   ⟨0, 3, .prevote, some 7⟩, ⟨0, 3, .precommit, some 7⟩,
   ⟨0, 2, .prevote, none⟩, ⟨0, 2, .precommit, none⟩}⟩
def sourcePolka := unitCertificate 0 17 .prevote 7
def sourceCommit := unitCertificate 0 17 .precommit 7
def adopted : Fin 1 → Option LocalState := fun u => adopt .strict unitContext sourcePolka u none
def start := inherited unitContext sourcePolka
def advanced : LocalState := { start with round := 3 }
def replaced : LocalState := { advanced with lockedRound := 1 }
def localPolka := unitCertificate 1 1 .prevote 7

theorem accepted : Accept .strict unitContext sourcePolka := by decide +kernel
theorem adoptions : Adoptions unitContext ∅ sourceCommit sourcePolka adopted :=
  adoptions_from_execution .strict unitContext ∅ sourceCommit sourcePolka accepted
theorem advanced_recorded : RecordedReachable .strict unitContext good start advanced :=
  .step .initial (.advance 3) trivial (by decide +kernel)
theorem replaced_recorded : RecordedReachable .strict unitContext good start replaced :=
  .step advanced_recorded (.replace localPolka) (by decide +kernel) (by decide +kernel)

example : Hits .strict unitContext {0} := by decide +kernel
example : Hits .weak unitContext {0} := by decide +kernel
example : ¬ Hits .strict unitContext ∅ := by decide +kernel
example : inheritedSigners unitContext ∅ sourceCommit sourcePolka adopted = {0} := by decide +kernel
example : inheritedSigners unitContext {0} sourceCommit sourcePolka adopted = ∅ := by decide +kernel
example : inheritedSigners unitContext ∅ sourceCommit sourcePolka (fun _ => none) = ∅ := by decide +kernel
example : Hits .strict unitContext (inheritedSigners unitContext ∅ sourceCommit sourcePolka adopted) :=
  inherited_signers_hit_every_quorum .strict unitContext ∅ sourceCommit sourcePolka adopted
    accepted (by decide +kernel) (by decide +kernel) (by decide +kernel) adoptions
example : HonestPrevotes .strict unitContext good {0} 7 := by decide +kernel
example : HonestPrecommits .strict unitContext good {0} := by decide +kernel
example : Polka .strict unitContext good 0 7 := by decide +kernel
example : Polka .strict unitContext good 1 7 := by decide +kernel
example : Commit .strict unitContext good 3 7 := by decide +kernel
example : ¬ Polka .strict unitContext good 2 7 := by decide +kernel
example : ¬ Commit .strict unitContext good 2 7 := by decide +kernel
example : ¬ EarlierPolka .strict unitContext good 0 7 := no_earlier_round_zero _ _ _ _
example : EarlierPolka .strict unitContext good 1 7 := by decide +kernel
example : EarlierPolka .strict unitContext good 3 7 := by decide +kernel
example : ∀ r x, Polka .strict unitContext good r x → x = 7 :=
  no_conflicting_polka_by_well_founded_induction .strict unitContext good {0} 7
    (by decide +kernel) (by decide +kernel)
example : ∀ r x, Commit .strict unitContext good r x → x = 7 := by
  intro r x hc
  exact all_rounds_agreement .strict unitContext good {0} 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) r x hc
example : ∀ r x, Commit .weak unitContext good r x → x = 7 := by
  intro r x hc
  exact all_rounds_agreement .weak unitContext good {0} 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) r x hc
example : Polka .strict unitContext good 3 7 :=
  precommit_requires_polka_lemma .strict unitContext good {0} 3 7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (7 : ℕ) = sourceCommit.value :=
  cross_epoch_arbitrary_round_safety .strict unitContext ∅ sourcePolka sourceCommit adopted good
    accepted (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    adoptions (by decide +kernel) (by decide +kernel) 3 7 (by decide +kernel)
example : (7 : ℕ) = 7 := round_zero_specialization .strict unitContext good {0} 7
  (by decide +kernel) (by decide +kernel) (by decide +kernel) 7 (by decide +kernel)
example : ¬ Observed .strict unitContext { good with epoch := 2 } .prevote 1 7 :=
  foreign_context_rejected _ _ _ _ _ _ (Or.inl (by decide +kernel))
example : ¬ Observed .strict unitContext { good with height := 6 } .precommit 3 7 :=
  foreign_context_rejected _ _ _ _ _ _ (Or.inr (by decide +kernel))
example : Registered unitContext good localPolka := by decide +kernel
example : ¬ Registered unitContext good { localPolka with height := 6 } := by decide +kernel
example : ¬ Registered unitContext good { localPolka with epoch := 0 } := by decide +kernel
example : ¬ Registered unitContext good (unitCertificate 1 1 .prevote 9) := by decide +kernel
example : Polka .strict unitContext good localPolka.round localPolka.value :=
  registered_replacement_polka .strict unitContext good advanced localPolka
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : Reachable .strict unitContext start replaced :=
  recorded_reachable_refines .strict unitContext good start replaced replaced_recorded
example : replaced.value = start.value ∨ EarlierPolka .strict unitContext good replaced.round replaced.value :=
  recorded_value_origin .strict unitContext good start replaced (by decide +kernel) replaced_recorded
example : replaceLock .strict unitContext advanced (unitCertificate 1 3 .prevote 9) = none :=
  future_polka_rejected _ _ _ _ (by decide +kernel)
example : HonestPrevotes .strict unitContext bareCommit {0} 7 :=
  uncertified_precommit_counterexample.2.1
example : Commit .strict unitContext bareCommit 3 9 := uncertified_precommit_counterexample.2.2.1
example : ¬ HonestPrecommits .strict unitContext bareCommit {0} :=
  uncertified_precommit_counterexample.2.2.2.2.1
example : WeakPrevotes .strict unitContext circularHistory {0} 7 := nonstrict_round_counterexample.2.1
example : HonestPrecommits .strict unitContext circularHistory {0} := nonstrict_round_counterexample.2.2.1
example : ¬ HonestPrevotes .strict unitContext circularHistory {0} 7 :=
  nonstrict_round_counterexample.2.2.2.2.1
example : Polka .strict unitContext circularHistory 1 9 := by decide +kernel
example : ¬ Polka .strict unitContext circularHistory 0 9 := by decide +kernel
example : ¬ EarlierPolka .strict unitContext circularHistory 1 9 := by decide +kernel
example : Polka .strict unitContext { good with votes := good.votes ∪ good.votes } 3 7 := by decide +kernel
example : ¬ Polka .strict unitContext { good with votes := ∅ } 3 7 := by decide +kernel

/-- A locally checked alternative replacement is possible when the global prevote rule fails. -/
def alternative : LocalState := { advanced with value := 9, lockedRound := 1 }
theorem alternative_recorded : RecordedReachable .strict unitContext circularHistory start alternative :=
  .step (s := advanced) (.step .initial (.advance 3) trivial (by decide +kernel))
    (.replace (unitCertificate 1 1 .prevote 9)) (by decide +kernel) (by decide +kernel)
example : EarlierPolka .strict unitContext circularHistory 3 9 :=
  recorded_prevote_rule .strict unitContext circularHistory start alternative (by decide +kernel)
    alternative_recorded 0 3 9 (by decide +kernel) (by decide +kernel)

#eval [
  ("strict hits", decide (Hits .strict unitContext {0})),
  ("weak hits", decide (Hits .weak unitContext {0})),
  ("empty anchor rejected", decide (¬ Hits .strict unitContext ∅)),
  ("adopted", decide (inheritedSigners unitContext ∅ sourceCommit sourcePolka adopted = {0})),
  ("prevote discipline", decide (HonestPrevotes .strict unitContext good {0} 7)),
  ("precommit discipline", decide (HonestPrecommits .strict unitContext good {0})),
  ("later commit", decide (Commit .strict unitContext good 3 7)),
  ("nil no polka", decide (¬ Polka .strict unitContext good 2 7)),
  ("no earlier zero", decide (¬ EarlierPolka .strict unitContext good 0 7)),
  ("earlier one", decide (EarlierPolka .strict unitContext good 1 7)),
  ("foreign epoch", decide (¬ Polka .strict unitContext { good with epoch := 2 } 1 7)),
  ("foreign height", decide (¬ Commit .strict unitContext { good with height := 6 } 3 7)),
  ("registered", decide (Registered unitContext good localPolka)),
  ("unregistered conflict", decide (¬ Registered unitContext good (unitCertificate 1 1 .prevote 9))),
  ("self justification rejected", decide (¬ HonestPrevotes .strict unitContext circularHistory {0} 7)),
  ("weak circular rule", decide (WeakPrevotes .strict unitContext circularHistory {0} 7)),
  ("bare commit", decide (Commit .strict unitContext bareCommit 3 9)),
  ("missing certification", decide (¬ HonestPrecommits .strict unitContext bareCommit {0})),
  ("no earlier conflict", decide (¬ EarlierPolka .strict unitContext circularHistory 1 9)),
  ("duplicate set", decide (certificateSigners unitConfig
    ({ good with votes := good.votes ∪ good.votes }.certificate .prevote 3 7) = {0}))]
end TendermintHandoverInductionRegression
