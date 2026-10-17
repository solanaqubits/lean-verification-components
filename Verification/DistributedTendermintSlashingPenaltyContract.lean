/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintAccountableSafety
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-! Exact rational accounting for one penalty application to a certified finite set.
The authenticated reference and its coverage retain module 179's assumptions.
No unbonding, transaction replay ledger, stake rounding or network timing is modeled. -/
namespace DistributedTendermintSlashingPenaltyContract
open Finset
open DistributedTendermintCoreSafety DistributedTendermintAccountableSafety

variable {V : Type*} [Fintype V] [DecidableEq V]

def stakeMass (w : V → ℚ) (B : Finset V) : ℚ := ∑ v ∈ B, w v

def totalStake (w : V → ℚ) : ℚ := stakeMass w univ

/-- Uniform penalty on a finite certified set; no rounding to natural-number stake. -/
def stakeSlashing (w : V → ℚ) (B : Finset V) (α : ℚ) : V → ℚ :=
  fun v => if v ∈ B then (1 - α) * w v else w v

def confiscated (w : V → ℚ) (B : Finset V) (α : ℚ) : ℚ :=
  ∑ v ∈ B, (w v - stakeSlashing w B α v)

/-- Weight outside the certified set. This complement may contain undetected faults. -/
def honestWeight (w : V → ℚ) (B : Finset V) : ℚ := stakeMass w Bᶜ

omit [Fintype V] in
theorem non_faulty_stake_invariant (w : V → ℚ) (B : Finset V) (α : ℚ)
    (u : V) (hu : u ∉ B) : stakeSlashing w B α u = w u := by
  simp [stakeSlashing, hu]

omit [Fintype V] in
theorem faulty_stake (w : V → ℚ) (B : Finset V) (α : ℚ)
    (v : V) (hv : v ∈ B) : stakeSlashing w B α v = (1 - α) * w v := by
  simp [stakeSlashing, hv]

omit [Fintype V] in
theorem slashing_nonnegative (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : α ≤ 1) : ∀ v, 0 ≤ stakeSlashing w B α v := by
  intro v
  by_cases hv : v ∈ B
  · rw [faulty_stake w B α v hv]
    exact mul_nonneg (sub_nonneg.mpr hα) (hw v)
  · rw [non_faulty_stake_invariant w B α v hv]
    exact hw v

omit [Fintype V] in
theorem slashing_le_initial (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : 0 ≤ α) : ∀ v, stakeSlashing w B α v ≤ w v := by
  intro v
  by_cases hv : v ∈ B
  · rw [faulty_stake w B α v hv]
    have := mul_nonneg hα (hw v)
    nlinarith
  · rw [non_faulty_stake_invariant w B α v hv]

omit [Fintype V] in
theorem confiscated_eq (w : V → ℚ) (B : Finset V) (α : ℚ) :
    confiscated w B α = α * stakeMass w B := by
  unfold confiscated stakeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [faulty_stake w B α v hv]
  ring

omit [Fintype V] in
theorem faulty_mass_after (w : V → ℚ) (B : Finset V) (α : ℚ) :
    stakeMass (stakeSlashing w B α) B = (1 - α) * stakeMass w B := by
  unfold stakeMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  exact faulty_stake w B α v hv

theorem honest_mass_invariant (w : V → ℚ) (B : Finset V) (α : ℚ) :
    honestWeight (stakeSlashing w B α) B = honestWeight w B := by
  unfold honestWeight stakeMass
  apply Finset.sum_congr rfl
  intro v hv
  exact non_faulty_stake_invariant w B α v (mem_compl.mp hv)

theorem mass_partition (w : V → ℚ) (B : Finset V) :
    stakeMass w B + honestWeight w B = totalStake w := by
  exact Finset.sum_add_sum_compl B w

theorem total_after (w : V → ℚ) (B : Finset V) (α : ℚ) :
    totalStake (stakeSlashing w B α) = totalStake w - α * stakeMass w B := by
  have h := mass_partition (stakeSlashing w B α) B
  rw [faulty_mass_after, honest_mass_invariant] at h
  have := mass_partition w B
  nlinarith

/-- Remaining balances plus an accounting pool equal the original total. -/
theorem slashing_conservation (w : V → ℚ) (B : Finset V) (α : ℚ) :
    totalStake (stakeSlashing w B α) + confiscated w B α = totalStake w := by
  rw [total_after, confiscated_eq]
  ring

omit [Fintype V] in
theorem confiscated_nonnegative (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : 0 ≤ α) : 0 ≤ confiscated w B α := by
  rw [confiscated_eq]
  exact mul_nonneg hα (Finset.sum_nonneg fun v _ => hw v)

omit [Fintype V] in
theorem faulty_mass_strict_decrease (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hα : 0 < α) (hB : 0 < stakeMass w B) :
    stakeMass (stakeSlashing w B α) B < stakeMass w B := by
  rw [faulty_mass_after]
  have := mul_pos hα hB
  nlinarith

theorem slashing_lower_bound (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hα : 0 < α) (hB : totalStake w / 3 < stakeMass w B) :
    α * (totalStake w / 3) < confiscated w B α := by
  rw [confiscated_eq]
  exact mul_lt_mul_of_pos_left hB hα

theorem post_total_positive (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : α ≤ 1) (hH : 0 < honestWeight w B) :
    0 < totalStake (stakeSlashing w B α) := by
  have hB : 0 ≤ stakeMass (stakeSlashing w B α) B :=
    Finset.sum_nonneg fun v _ => slashing_nonnegative w B α hw hα v
  have h := mass_partition (stakeSlashing w B α) B
  rw [honest_mass_invariant] at h
  linarith

/-- Strict improvement needs both positive honest mass and actual positive confiscation. -/
theorem relative_honest_dominance_increase (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 < stakeMass w B) (hH : 0 < honestWeight w B) :
    honestWeight w B / totalStake w <
      honestWeight (stakeSlashing w B α) B / totalStake (stakeSlashing w B α) := by
  have hW : 0 < totalStake w := by
    have := mass_partition w B
    linarith
  have hW' := post_total_positive w B α hw hα1 hH
  rw [honest_mass_invariant, div_lt_div_iff₀ hW hW', total_after]
  have := mul_pos hH (mul_pos hα hB)
  nlinarith

omit [Fintype V] in
/-- Any protected subset disjoint from the certified set retains its entire mass. -/
theorem protected_mass_invariant (w : V → ℚ) (B H : Finset V) (α : ℚ)
    (hdis : ∀ v ∈ H, v ∉ B) :
    stakeMass (stakeSlashing w B α) H = stakeMass w H := by
  apply Finset.sum_congr rfl
  intro v hv
  exact non_faulty_stake_invariant w B α v (hdis v hv)

theorem protected_share_strict_increase (w : V → ℚ) (B H : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : 0 < α) (hα1 : α ≤ 1)
    (hB : 0 < stakeMass w B) (hH : 0 < stakeMass w H)
    (hdis : ∀ v ∈ H, v ∉ B) :
    stakeMass w H / totalStake w <
      stakeMass (stakeSlashing w B α) H / totalStake (stakeSlashing w B α) := by
  have hi := protected_mass_invariant w B H α hdis
  have hbefore : stakeMass w H ≤ totalStake w :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H) (fun v _ _ => hw v)
  have hafter : stakeMass (stakeSlashing w B α) H ≤ totalStake (stakeSlashing w B α) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ H)
      (fun v _ _ => slashing_nonnegative w B α hw hα1 v)
  have hW : 0 < totalStake w := lt_of_lt_of_le hH hbefore
  have hW' : 0 < totalStake (stakeSlashing w B α) := by rw [hi] at hafter; linarith
  rw [hi, div_lt_div_iff₀ hW hW', total_after]
  have := mul_pos hH (mul_pos hα hB)
  nlinarith

/-- The strict two-thirds quorum remains strict, even if the penalty is zero. -/
theorem honest_quorum_preserved (w : V → ℚ) (B : Finset V) (α : ℚ)
    (hw : ∀ v, 0 ≤ w v) (hα : 0 ≤ α)
    (hq : 2 * totalStake w < 3 * honestWeight w B) :
    2 * totalStake (stakeSlashing w B α) <
      3 * honestWeight (stakeSlashing w B α) B := by
  rw [total_after, honest_mass_invariant]
  have hB : 0 ≤ stakeMass w B := Finset.sum_nonneg fun v _ => hw v
  have := mul_nonneg hα hB
  linarith

/-- The conflicting-commit threshold and a complementary honest supermajority
are separate scenarios, never simultaneous assumptions for one partition. -/
theorem threshold_and_honest_quorum_incompatible (w : V → ℚ) (B : Finset V)
    (hB : totalStake w / 3 < stakeMass w B) :
    ¬ 2 * totalStake w < 3 * honestWeight w B := by
  have := mass_partition w B
  linarith

omit [Fintype V] in
@[simp] theorem empty_slashing (w : V → ℚ) (α : ℚ) : stakeSlashing w ∅ α = w := by
  funext v
  simp [stakeSlashing]

omit [Fintype V] in
@[simp] theorem zero_slashing (w : V → ℚ) (B : Finset V) : stakeSlashing w B 0 = w := by
  funext v
  simp [stakeSlashing]

omit [Fintype V] in
theorem full_confiscation (w : V → ℚ) (B : Finset V) (v : V) (hv : v ∈ B) :
    stakeSlashing w B 1 v = 0 := by simp [stakeSlashing, hv]

omit [Fintype V] in
/-- Duplicate identities in a single certificate are charged once. This does not
assert idempotence of applying two separate slashing transactions. -/
theorem duplicate_set_same_penalty (w : V → ℚ) (B : Finset V) (α : ℚ) :
    stakeSlashing w (B ∪ B) α = stakeSlashing w B α := by rw [union_self]

/-- Exact embedding of module 179's natural-number voting weights. -/
def stakeOfConfig {n : ℕ} (c : Config n) : Fin n → ℚ := fun v => c.weight v

theorem config_mass {n : ℕ} (c : Config n) (B : Finset (Fin n)) :
    stakeMass (stakeOfConfig c) B = (c.mass B : ℚ) := by
  simp [stakeMass, stakeOfConfig, Config.mass]

theorem config_total {n : ℕ} (c : Config n) :
    totalStake (stakeOfConfig c) = (c.total : ℚ) := config_mass c univ

theorem config_nonnegative {n : ℕ} (c : Config n) : ∀ v, 0 ≤ stakeOfConfig c v := by
  intro v
  change (0 : ℚ) ≤ (c.weight v : ℚ)
  positivity

/-- No arbitrary caller-provided blame set is silently treated as certified. -/
def slashEvidence {n : ℕ} (c : Config n) (reference : Option (Finset (Vote n)))
    (e : EvidenceView n) (α : ℚ) : Except AttributionError (Fin n → ℚ) :=
  match attribute_evidence c reference e with
  | .error err => .error err
  | .ok B => .ok (stakeSlashing (stakeOfConfig c) B α)

theorem checked_slashing_result {n : ℕ} (c : Config n)
    (reference : Option (Finset (Vote n))) (e : EvidenceView n) (B : Finset (Fin n))
    (α : ℚ) (hc : attribute_evidence c reference e = .ok B) :
    slashEvidence c reference e α = .ok (stakeSlashing (stakeOfConfig c) B α) := by
  simp [slashEvidence, hc]

theorem rejected_evidence_no_penalty {n : ℕ} (c : Config n)
    (reference : Option (Finset (Vote n))) (e : EvidenceView n) (α : ℚ)
    (err : AttributionError) (hc : attribute_evidence c reference e = .error err) :
    slashEvidence c reference e α = .error err := by
  simp [slashEvidence, hc]

/-- Certificate validity prevents framing relative to the authenticated history;
absence from B alone is not claimed to prove that a validator is honest. -/
theorem certified_honest_stake_invariant {n : ℕ} (c : Config n)
    {s : State n} (hr : Reachable c s) (e : EvidenceView n) (B : Finset (Fin n))
    (hc : attribute_evidence c (some s.votes) e = .ok B) (α : ℚ)
    (v : Fin n) (hv : v ∉ c.byzantine) :
    stakeSlashing (stakeOfConfig c) B α v = stakeOfConfig c v :=
  non_faulty_stake_invariant _ _ _ _ (attribution_honest c hr e B hc v hv)

/-- Actual honest validators, rather than merely unaccused validators, gain share
when checked attribution removes positive stake and positive honest stake remains. -/
theorem certified_honest_share_increase {n : ℕ} (c : Config n)
    {s : State n} (hr : Reachable c s) (e : EvidenceView n) (B : Finset (Fin n))
    (hc : attribute_evidence c (some s.votes) e = .ok B) (α : ℚ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hB : 0 < stakeMass (stakeOfConfig c) B)
    (hH : 0 < stakeMass (stakeOfConfig c) c.byzantineᶜ) :
    stakeMass (stakeOfConfig c) c.byzantineᶜ / totalStake (stakeOfConfig c) <
      stakeMass (stakeSlashing (stakeOfConfig c) B α) c.byzantineᶜ /
        totalStake (stakeSlashing (stakeOfConfig c) B α) := by
  apply protected_share_strict_increase _ _ _ _ (config_nonnegative c) hα hα1 hB hH
  intro v hv
  exact attribution_honest c hr e B hc v (mem_compl.mp hv)

/-- Two conflicting commits in the checked view produce the strict rational
penalty bound through module 179, with no assumption of an honest supermajority. -/
theorem checked_slashing_lower_bound {n : ℕ} (c : Config n)
    (reference : Finset (Vote n)) (e : EvidenceView n) (B : Finset (Fin n))
    (hc : attribute_evidence c (some reference) e = .ok B)
    {r r' u v : ℕ} (hu : commit c e.votes r u) (hv : commit c e.votes r' v)
    (hne : u ≠ v) (α : ℚ) (hα : 0 < α) :
    α * ((c.total : ℚ) / 3) < confiscated (stakeOfConfig c) B α := by
  obtain ⟨_, hB⟩ := (attribute_success_iff c reference e B).mp hc
  have bound := accountable_safety_attribution c e.votes hu hv hne
  rw [hB] at bound
  have rat_bound : (c.total : ℚ) < 3 * (c.mass B : ℚ) := by exact_mod_cast bound
  rw [← config_total c] at rat_bound ⊢
  apply slashing_lower_bound _ _ _ hα
  rw [config_mass]
  linarith

structure DistributedTendermintSlashingPenaltyContractSuite : Prop where
  nonnegative : ∀ {n} (w : Fin n → ℚ) B α, (∀ v, 0 ≤ w v) → α ≤ 1 →
    ∀ v, 0 ≤ stakeSlashing w B α v
  unchanged_outside : ∀ {n} (w : Fin n → ℚ) B α v, v ∉ B → stakeSlashing w B α v = w v
  strict_decrease : ∀ {n} (w : Fin n → ℚ) B α, 0 < α → 0 < stakeMass w B →
    stakeMass (stakeSlashing w B α) B < stakeMass w B
  quorum : ∀ {n} (w : Fin n → ℚ) B α, (∀ v, 0 ≤ w v) → 0 ≤ α →
    2 * totalStake w < 3 * honestWeight w B →
      2 * totalStake (stakeSlashing w B α) < 3 * honestWeight (stakeSlashing w B α) B
  conservation : ∀ {n} (w : Fin n → ℚ) B α,
    totalStake (stakeSlashing w B α) + confiscated w B α = totalStake w
  strict_penalty : ∀ {n} (w : Fin n → ℚ) B α, 0 < α → totalStake w / 3 < stakeMass w B →
    α * (totalStake w / 3) < confiscated w B α
  dominance : ∀ {n} (w : Fin n → ℚ) B α, (∀ v, 0 ≤ w v) → 0 < α → α ≤ 1 →
    0 < stakeMass w B → 0 < honestWeight w B →
      honestWeight w B / totalStake w <
        honestWeight (stakeSlashing w B α) B / totalStake (stakeSlashing w B α)
  attribution_bound : ∀ {n} (c : Config n) reference e B,
    attribute_evidence c (some reference) e = .ok B →
    ∀ {r r' u v}, commit c e.votes r u → commit c e.votes r' v → u ≠ v →
    ∀ α : ℚ, 0 < α → α * ((c.total : ℚ) / 3) < confiscated (stakeOfConfig c) B α

theorem verification_suite : DistributedTendermintSlashingPenaltyContractSuite where
  nonnegative := slashing_nonnegative
  unchanged_outside := non_faulty_stake_invariant
  strict_decrease := faulty_mass_strict_decrease
  quorum := honest_quorum_preserved
  conservation := slashing_conservation
  strict_penalty := slashing_lower_bound
  dominance := relative_honest_dominance_increase
  attribution_bound := checked_slashing_lower_bound

end DistributedTendermintSlashingPenaltyContract
