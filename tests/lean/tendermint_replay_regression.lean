import Verification.DistributedTendermintSlashingReplayProtection
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintCoreSafety DistributedTendermintAccountableSafety
open DistributedTendermintSlashingPenaltyContract DistributedTendermintSlashingReplayProtection
namespace TendermintReplayRegression
set_option maxRecDepth 4096

def cfg : Config 3 := ⟨![8, 6, 4], univ, 17⟩
def equiv (v : Fin 3) (r : ℕ) : Finset (Vote 3) :=
  {⟨v, r, .prevote, some 0⟩, ⟨v, r, .prevote, some 1⟩}
def votes₁ := equiv 0 0 ∪ equiv 1 0
def votes₂ := equiv 1 0 ∪ equiv 2 0
def votesOther := equiv 0 2 ∪ equiv 1 2
def view (h : ℕ) (votes : Finset (Vote 3)) : EvidenceView 3 :=
  ⟨votes.image (fun v => ⟨h, v⟩), ∅⟩
def initialLedger : SlashingLedgerState (Fin 3) := ⟨![8, 6, 4], 5, ∅⟩
def step (votes : Finset (Vote 3)) (s : SlashingLedgerState (Fin 3)) :=
  applySlashingCertificate cfg (some votes) (view 17 votes) (1/2) s
def first := step votes₁ initialLedger
def replayed := step votes₁ first
def alternate := step votesOther first
def overlap := step votes₂ first

def observed (s : SlashingLedgerState (Fin 3)) :=
  (s.balances 0, s.balances 1, s.balances 2, s.confiscated, s.processed)

example : attribute_evidence cfg (some votes₁) (view 17 votes₁) = .ok {0, 1} := by decide +kernel
example : attribute_evidence cfg (some votes₂) (view 17 votes₂) = .ok {1, 2} := by decide +kernel
example : attribute_evidence cfg (some votesOther) (view 17 votesOther) = .ok {0, 1} := by decide +kernel
example : view 17 votes₁ ≠ view 17 votesOther := by decide +kernel
example : first.balances 0 = 4 ∧ first.balances 1 = 3 ∧ first.balances 2 = 4 := by decide +kernel
example : first.confiscated = 12 := by decide +kernel
example : first.processed = {(17, 0), (17, 1)} := by decide +kernel
example : replayed = first := replay_idempotence cfg (some votes₁) (view 17 votes₁) (1/2) initialLedger
example : observed replayed = (4, 3, 4, 12, {(17, 0), (17, 1)}) := by decide +kernel
example : observed alternate = observed first := by decide +kernel
example : alternate = first :=
  checked_same_offenders_noop cfg (some votes₁) (some votesOther)
    (view 17 votes₁) (view 17 votesOther) (1/2) (1/2) initialLedger {0, 1}
    (by decide +kernel) (by decide +kernel) (by norm_num) (by norm_num)
example : observed overlap = (4, 3, 2, 14, {(17, 0), (17, 1), (17, 2)}) := by decide +kernel
example : accountedTotal overlap = 23 := by decide +kernel
example : freshOffenders first 17 ({1, 2} : Finset (Fin 3)) = {2} := by decide +kernel
example : overlap.balances 1 = first.balances 1 :=
  checked_overlap cfg (some votes₁) (some votes₂) (view 17 votes₁) (view 17 votes₂)
    (1/2) (1/2) initialLedger {0, 1} {1, 2} (by decide +kernel)
    (by decide +kernel) (by norm_num) (by norm_num) 1 (by decide)
example : applySlashingCertificate cfg (some ∅) (view 17 ∅) (1/2) initialLedger = initialLedger := by
  rw [accepted_certificate cfg _ _ _ _ ∅ (by decide +kernel) (by norm_num)]
  exact empty_certificate _ _ _
example : applySlashingCertificate cfg none (view 17 votes₁) (1/2) initialLedger = initialLedger :=
  invalid_certificate_noop cfg _ _ _ _ .insufficientEvidence rfl
example : applySlashingCertificate cfg (some votes₁) (view 18 votes₁) (1/2) initialLedger = initialLedger :=
  invalid_certificate_noop cfg _ _ _ _ .invalidEvidence (by decide +kernel)
example : applySlashingCertificate cfg (some votes₁) (view 17 (equiv 0 0)) (1/2) initialLedger = initialLedger :=
  invalid_certificate_noop cfg _ _ _ _ .insufficientEvidence (by decide +kernel)
example : applySlashingCertificate cfg (some votes₁) (view 17 votes₂) (1/2) initialLedger = initialLedger :=
  invalid_certificate_noop cfg _ _ _ _ .invalidEvidence (by decide +kernel)
example : applySlashingCertificate cfg (some votes₁) (view 17 votes₁) 0 initialLedger = initialLedger :=
  invalid_rate_noop cfg _ _ _ _ (by norm_num)
example : applySlashingCertificate cfg (some votes₁) (view 17 votes₁) (-1) initialLedger = initialLedger :=
  invalid_rate_noop cfg _ _ _ _ (by norm_num)
example : applySlashingCertificate cfg (some votes₁) (view 17 votes₁) 2 initialLedger = initialLedger :=
  invalid_rate_noop cfg _ _ _ _ (by norm_num)
example : first.balances = stakeSlashing initialLedger.balances {0, 1} (1/2) :=
  checked_first_step cfg _ _ _ _ {0, 1} (by decide +kernel) (by norm_num) rfl

def full := applySlashingCertificate cfg (some votes₁) (view 17 votes₁) 1 initialLedger
example : observed full = (0, 0, 4, 19, {(17, 0), (17, 1)}) := by decide +kernel
example : (∀ v, 0 ≤ full.balances v) ∧ 0 ≤ full.confiscated := by decide +kernel
-- Changing the rate cannot bypass an already processed key.
example : observed (applySlashingCertificate cfg (some votes₁) (view 17 votes₁) 1 first) =
    observed first := by decide +kernel
-- A new, externally authenticated height is a different policy key.
def nextHeight := applySlashingCertificate {cfg with height := 18}
  (some votes₁) (view 18 votes₁) (1/2) first
example : observed nextHeight =
    (2, 3/2, 4, 31/2, {(17, 0), (17, 1), (18, 0), (18, 1)}) := by decide +kernel
-- A zero current balance still consumes the permitted per-height key.
def zeroLedger : SlashingLedgerState (Fin 3) := ⟨![0, 6, 4], 0, ∅⟩
example : (17, 0) ∈ (step votes₁ zeroLedger).processed := by decide +kernel
example : stakeSlashing (stakeSlashing initialLedger.balances {0, 1} (1/2)) {0, 1} (1/2) 0 = 2 := by decide +kernel
example : replayed.balances 0 ≠ 2 := by decide +kernel
-- Non-vacuous executable protocol trace: all messages are legal faulty emissions.
def actions : List (Action 3) :=
  [.faulty ⟨0, 0, .prevote, some 0⟩, .faulty ⟨0, 0, .prevote, some 1⟩,
   .faulty ⟨1, 0, .prevote, some 0⟩, .faulty ⟨1, 0, .prevote, some 1⟩]
def reached := (run cfg initial actions).getD initial
theorem execution : run cfg initial actions = some reached := by decide +kernel
theorem reachable : Reachable cfg reached := run_reachable cfg actions Reachable.init execution
example : reached.votes = votes₁ := by decide +kernel
example : attribute_evidence cfg (some reached.votes) (view 17 votes₁) = .ok {0, 1} := by decide +kernel

def requests : List (CertificateRequest 3) :=
  [⟨cfg, some votes₁, view 17 votes₁⟩, ⟨cfg, none, view 17 votes₂⟩,
   ⟨cfg, some votesOther, view 17 votesOther⟩, ⟨cfg, some votes₂, view 17 votes₂⟩]
example : observed (runCertificates (1/2) initialLedger requests) = observed overlap := by decide +kernel
example : accountedTotal (runCertificates (1/2) initialLedger requests) = accountedTotal initialLedger :=
  run_conservation _ _ _
example : WellFormed (runCertificates (1/2) initialLedger requests) :=
  run_wellFormed _ _ _ ⟨by decide +kernel, by norm_num [initialLedger]⟩

#eval [("first", decide (observed first = (4, 3, 4, 12, {(17, 0), (17, 1)}))),
  ("replay", decide (observed replayed = observed first)),
  ("alternate certificate", decide (observed alternate = observed first)),
  ("overlap", decide (observed overlap = (4, 3, 2, 14, {(17, 0), (17, 1), (17, 2)}))),
  ("pool conservation", decide (accountedTotal overlap = 23)),
  ("full", decide (observed full = (0, 0, 4, 19, {(17, 0), (17, 1)}))),
  ("new height", decide (nextHeight.balances 0 = 2)),
  ("zero stake key", decide ((17, 0) ∈ (step votes₁ zeroLedger).processed)),
  ("sequence", decide (observed (runCertificates (1/2) initialLedger requests) = observed overlap)),
  ("reachable", (run cfg initial actions).isSome)]
end TendermintReplayRegression
