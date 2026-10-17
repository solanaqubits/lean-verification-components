/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.DistributedTendermintEpochIdentityContract

/-! Finite weighted intersection across stable identities. No lock handover is asserted. -/
namespace DistributedTendermintQuorumIntersectionEpochTransitionContract
open Finset
open DistributedTendermintEpochIdentityContract

variable {V : Type*} [Fintype V] [DecidableEq V]

def mass (w : V → ℚ) (S : Finset V) : ℚ := ∑ v ∈ S, w v

def Normalized (w : V → ℚ) : Prop := (∀ v, 0 ≤ w v) ∧ mass w univ = 1

def isQuorum (w : V → ℚ) (q : ℚ) (Q : Finset V) : Prop := q ≤ mass w Q

instance (w : V → ℚ) : Decidable (Normalized w) :=
  inferInstanceAs (Decidable ((∀ v, 0 ≤ w v) ∧ mass w univ = 1))

instance (w : V → ℚ) (q : ℚ) (Q : Finset V) : Decidable (isQuorum w q Q) :=
  inferInstanceAs (Decidable (q ≤ mass w Q))

def common (w z : V → ℚ) (v : V) : ℚ := min (w v) (z v)

def variation (w z : V → ℚ) : ℚ := (∑ v, |w v - z v|) / 2

def honestCommon (w z : V → ℚ) (B : Finset V) : ℚ := mass (common w z) (univ \ B)

def honestIntersection (B Q R : Finset V) : Finset V := (Q ∩ R) \ B

/-- Directed loss on honest subjects, with no absolute-value or factor-two ambiguity. -/
def honestLoss (w z : V → ℚ) (B : Finset V) : ℚ :=
  ∑ v ∈ univ \ B, max (w v - z v) 0

lemma mass_indicator (w : V → ℚ) (S : Finset V) :
    mass w S = ∑ v, if v ∈ S then w v else 0 := by
  simp [mass]

omit [Fintype V] [DecidableEq V] in
lemma mass_nonnegative (w : V → ℚ) (hw : ∀ v, 0 ≤ w v) S : 0 ≤ mass w S :=
  Finset.sum_nonneg fun v _ => hw v

lemma complement_mass (w : V → ℚ) (hw : Normalized w) Q :
    mass w (univ \ Q) = 1 - mass w Q := by
  have he := Finset.sum_inter_add_sum_sdiff univ Q w
  simp only [univ_inter] at he
  change mass w Q + mass w (univ \ Q) = mass w univ at he
  rw [hw.2] at he
  linarith

omit [Fintype V] [DecidableEq V] in
lemma common_nonnegative (w z : V → ℚ) (hw : ∀ v, 0 ≤ w v) (hz : ∀ v, 0 ≤ z v) v :
    0 ≤ common w z v := le_min (hw v) (hz v)

/-- The complement cover is valid even when the complements overlap. -/
theorem complement_cover (w z : V → ℚ) (hw : ∀ v, 0 ≤ w v) (hz : ∀ v, 0 ≤ z v)
    B Q R :
    honestCommon w z B ≤ mass (common w z) (honestIntersection B Q R) +
      mass w (univ \ Q) + mass z (univ \ R) := by
  unfold honestCommon
  simp only [mass_indicator, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro v _
  have hn := common_nonnegative w z hw hz v
  have h₁ : common w z v ≤ w v := min_le_left _ _
  have h₂ : common w z v ≤ z v := min_le_right _ _
  by_cases hb : v ∈ B <;> by_cases hq : v ∈ Q <;> by_cases hr : v ∈ R <;>
    simp [honestIntersection, hb, hq, hr] <;> linarith [hw v, hz v]

theorem quorum_intersection_weight_bound (w z : V → ℚ)
    (hw : Normalized w) (hz : Normalized z) B Q R q r
    (hq : isQuorum w q Q) (hr : isQuorum z r R) :
    honestCommon w z B + q + r - 2 ≤ mass (common w z) (honestIntersection B Q R) := by
  have he := complement_cover w z hw.1 hz.1 B Q R
  rw [complement_mass w hw, complement_mass z hz] at he
  unfold isQuorum at hq hr
  linarith

omit [Fintype V] in
lemma positive_intersection (w z : V → ℚ) B Q R
    (hp : 0 < mass (common w z) (honestIntersection B Q R)) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  obtain ⟨v, hv, hp⟩ := Finset.exists_lt_of_sum_lt
    (show (∑ _v ∈ honestIntersection B Q R, (0 : ℚ)) <
      ∑ v ∈ honestIntersection B Q R, common w z v by simpa [mass] using hp)
  exact ⟨v, (mem_sdiff.mp hv).1, (mem_sdiff.mp hv).2,
    lt_of_lt_of_le hp (min_le_left _ _), lt_of_lt_of_le hp (min_le_right _ _)⟩

theorem honest_node_in_intersection (w z : V → ℚ)
    (hw : Normalized w) (hz : Normalized z) B Q R q r
    (hq : isQuorum w q Q) (hr : isQuorum z r R)
    (hc : 2 - q - r < honestCommon w z B) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  apply positive_intersection
  have he := quorum_intersection_weight_bound w z hw hz B Q R q r hq hr
  linarith

lemma min_abs_identity (a b : ℚ) : 2 * min a b = a + b - |a - b| := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring

omit [DecidableEq V] in
theorem common_variation_identity (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z) :
    mass (common w z) univ = 1 - variation w z := by
  have he : 2 * mass (common w z) univ = mass w univ + mass z univ - ∑ v, |w v - z v| := by
    simp only [mass, common, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun v _ => min_abs_identity (w v) (z v)
  rw [hw.2, hz.2] at he
  unfold variation
  linarith

theorem honest_common_identity (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z) B :
    honestCommon w z B = 1 - variation w z - mass (common w z) B := by
  have he := Finset.sum_inter_add_sum_sdiff univ B (common w z)
  simp only [univ_inter] at he
  change mass (common w z) B + honestCommon w z B = mass (common w z) univ at he
  rw [common_variation_identity w z hw hz] at he
  linarith

theorem variation_weight_bound (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z)
    B Q R q r (hq : isQuorum w q Q) (hr : isQuorum z r R) :
    q + r - 1 - variation w z - mass (common w z) B ≤
      mass (common w z) (honestIntersection B Q R) := by
  have he := quorum_intersection_weight_bound w z hw hz B Q R q r hq hr
  rw [honest_common_identity w z hw hz] at he
  linarith

theorem variation_sufficient (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z)
    B Q R q r (hq : isQuorum w q Q) (hr : isQuorum z r R)
    (hc : variation w z + mass (common w z) B < q + r - 1) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  apply honest_node_in_intersection w z hw hz B Q R q r hq hr
  rw [honest_common_identity w z hw hz]
  linarith

/-- The sum of both Byzantine masses is a valid but unnecessarily strong bound. -/
theorem two_fault_masses_sufficient (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z)
    B Q R q r (hq : isQuorum w q Q) (hr : isQuorum z r R)
    (hc : mass w B + mass z B + variation w z < q + r - 1) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  apply variation_sufficient w z hw hz B Q R q r hq hr
  have hm : mass (common w z) B ≤ mass w B :=
    Finset.sum_le_sum fun v _ => min_le_left _ _
  have hn := mass_nonnegative z hz.1 B
  linarith

lemma min_loss_identity (a b : ℚ) : min a b = a - max (a - b) 0 := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right (sub_nonpos.mpr h)]; ring
  · rw [min_eq_right h, max_eq_left (sub_nonneg.mpr h)]; ring

theorem honest_loss_identity (w z : V → ℚ) (hw : Normalized w) B :
    honestCommon w z B = 1 - mass w B - honestLoss w z B := by
  have he : honestCommon w z B = mass w (univ \ B) - honestLoss w z B := by
    simp only [honestCommon, mass, honestLoss, ← Finset.sum_sub_distrib, common]
    exact Finset.sum_congr rfl fun v _ => min_loss_identity (w v) (z v)
  rw [he, complement_mass w hw]

theorem directed_loss_sufficient (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z)
    B Q R q r (hq : isQuorum w q Q) (hr : isQuorum z r R)
    (hc : mass w B + honestLoss w z B < q + r - 1) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  apply honest_node_in_intersection w z hw hz B Q R q r hq hr
  rw [honest_loss_identity w z hw]
  linarith

theorem static_epoch_equivalence (w : V → ℚ) (hw : Normalized w) B :
    honestCommon w w B = 1 - mass w B ∧ variation w w = 0 := by
  constructor
  · simpa [honestCommon, mass, common] using complement_mass w hw B
  · simp [variation]

/-- Non-strict quorums require strict slack in the fault bound. -/
theorem static_epoch_specialization (w : V → ℚ) (hw : Normalized w) B Q R
    (hq : isQuorum w (2 / 3) Q) (hr : isQuorum w (2 / 3) R) (hb : mass w B < 1 / 3) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v := by
  obtain ⟨v, hv, hb', hp, _⟩ := honest_node_in_intersection w w hw hw B Q R (2 / 3) (2 / 3)
    hq hr (by rw [(static_epoch_equivalence w hw B).1]; linarith)
  exact ⟨v, hv, hb', hp⟩

/-- Strict Tendermint quorums permit equality in the common honest mass threshold. -/
theorem strict_tendermint_intersection (w z : V → ℚ) (hw : Normalized w) (hz : Normalized z)
    B Q R (hq : (2 : ℚ) / 3 < mass w Q) (hr : (2 : ℚ) / 3 < mass z R)
    (hc : (2 : ℚ) / 3 ≤ honestCommon w z B) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v := by
  apply honest_node_in_intersection w z hw hz B Q R (mass w Q) (mass z R)
    (le_refl _) (le_refl _)
  linarith

/-- Normalization is used only under a positive total-weight premise. -/
def normalize (w : V → ℚ) (v : V) : ℚ := w v / mass w univ

omit [DecidableEq V] in
lemma normalize_mass (w : V → ℚ) Q : mass (normalize w) Q = mass w Q / mass w univ := by
  simp [mass, normalize, div_eq_mul_inv, Finset.sum_mul]

omit [DecidableEq V] in
theorem normalize_normalized (w : V → ℚ) (hw : ∀ v, 0 ≤ w v)
    (ht : 0 < mass w univ) : Normalized (normalize w) := by
  refine ⟨fun v => div_nonneg (hw v) ht.le, ?_⟩
  rw [normalize_mass, div_self (ne_of_gt ht)]

omit [DecidableEq V] in
theorem normalization_scale_invariant (w : V → ℚ) k (hk : 0 < k) :
    normalize (fun v => k * w v) = normalize w := by
  funext v
  simp only [normalize, mass, ← Finset.mul_sum]
  exact mul_div_mul_left _ _ (ne_of_gt hk)

def epochWeights (c : EpochConfig V) : V → ℚ := normalize c.stakeMap

theorem epochWeights_normalized (c : EpochConfig V) (ht : 0 < mass c.stakeMap univ) :
    Normalized (epochWeights c) := normalize_normalized _ (stakeMap_nonnegative c) ht

theorem epoch_reindex_invariance (c : EpochConfig V) (e : Equiv.Perm (Fin c.n)) :
    epochWeights (reindex c e) = epochWeights c := by
  have he : (reindex c e).stakeMap = c.stakeMap := funext (permutation_stakeMap c e)
  unfold epochWeights
  rw [he]

open DistributedTendermintCoreSafety (Config)

def legacyWeights {n : ℕ} (c : Config n) : Fin n → ℚ := fun i => c.weight i

lemma legacy_mass {n : ℕ} (c : Config n) Q :
    mass (legacyWeights c) Q = (c.mass Q : ℚ) := by
  simp [mass, legacyWeights, Config.mass]

lemma legacy_total {n : ℕ} (c : Config n) :
    mass (legacyWeights c) univ = (c.total : ℚ) := legacy_mass c univ

/-- Exact correspondence with the strict integer quorum predicate used by module 179. -/
theorem legacy_quorum_equivalence {n : ℕ} (c : Config n) Q (ht : 0 < c.total) :
    (2 : ℚ) / 3 < mass (normalize (legacyWeights c)) Q ↔ c.quorum Q := by
  rw [normalize_mass, legacy_mass, legacy_total]
  have hp : (0 : ℚ) < c.total := by exact_mod_cast ht
  rw [lt_div_iff₀ hp]
  constructor
  · intro h
    have he : (2 : ℚ) * c.total < 3 * c.mass Q := by linarith
    exact_mod_cast he
  · intro h
    have he : (2 : ℚ) * c.total < 3 * c.mass Q := by exact_mod_cast h
    linarith

/-- The static global result recovers the old natural-weight safety lemma's conclusion. -/
theorem static_legacy_specialization {n : ℕ} (c : Config n) Q R
    (hb : 3 * c.mass c.byzantine ≤ c.total) (hq : c.quorum Q) (hr : c.quorum R) :
    ∃ v ∈ Q ∩ R, v ∉ c.byzantine ∧ 0 < c.weight v := by
  have ht := DistributedTendermintCoreSafety.quorum_total_positive c hq
  have hp : (0 : ℚ) < c.total := by exact_mod_cast ht
  have hn := normalize_normalized (legacyWeights c) (fun i => by simp [legacyWeights])
    (by rw [legacy_total]; exact hp)
  have hm : mass (normalize (legacyWeights c)) c.byzantine ≤ (1 : ℚ) / 3 := by
    rw [normalize_mass, legacy_mass, legacy_total, div_le_iff₀ hp]
    have he : (3 : ℚ) * c.mass c.byzantine ≤ c.total := by exact_mod_cast hb
    linarith
  obtain ⟨v, hv, hnb, hvp, _⟩ := strict_tendermint_intersection
    (normalize (legacyWeights c)) (normalize (legacyWeights c)) hn hn c.byzantine Q R
    ((legacy_quorum_equivalence c Q ht).mpr hq) ((legacy_quorum_equivalence c R ht).mpr hr)
    (by rw [(static_epoch_equivalence _ hn c.byzantine).1]; linarith)
  refine ⟨v, hv, hnb, ?_⟩
  change 0 < (c.weight v : ℚ) / mass (legacyWeights c) univ at hvp
  rw [legacy_total] at hvp
  have hv' := (div_pos_iff_of_pos_right hp).mp hvp
  exact_mod_cast hv'

/-- Application to two historical configurations on the common finite global ID universe. -/
theorem epoch_quorum_intersection (c d : EpochConfig V)
    (hc : 0 < mass c.stakeMap univ) (hd : 0 < mass d.stakeMap univ) B Q R q r
    (hq : isQuorum (epochWeights c) q Q) (hr : isQuorum (epochWeights d) r R)
    (hb : 2 - q - r < honestCommon (epochWeights c) (epochWeights d) B) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < epochWeights c v ∧ 0 < epochWeights d v :=
  honest_node_in_intersection _ _ (epochWeights_normalized c hc)
    (epochWeights_normalized d hd) B Q R q r hq hr hb

theorem epoch_positive_active (c : EpochConfig V) v (hp : 0 < epochWeights c v) :
    v ∈ c.activeIds := by
  by_contra hn
  have hz := stakeMap_supported c v hn
  simp [epochWeights, normalize, hz] at hp

theorem epoch_shared_subject (c d : EpochConfig V)
    (hc : 0 < mass c.stakeMap univ) (hd : 0 < mass d.stakeMap univ) B Q R q r
    (hq : isQuorum (epochWeights c) q Q) (hr : isQuorum (epochWeights d) r R)
    (hb : 2 - q - r < honestCommon (epochWeights c) (epochWeights d) B) :
    ∃ v ∈ Q ∩ R, v ∉ B ∧ v ∈ c.activeIds ∧ v ∈ d.activeIds := by
  obtain ⟨v, hv, hn, hp, hz⟩ := epoch_quorum_intersection c d hc hd B Q R q r hq hr hb
  exact ⟨v, hv, hn, epoch_positive_active c v hp, epoch_positive_active d v hz⟩

omit [DecidableEq V] in
theorem variation_nonnegative (w z : V → ℚ) : 0 ≤ variation w z := by
  exact div_nonneg (Finset.sum_nonneg fun v _ => abs_nonneg (w v - z v)) (by norm_num)

omit [DecidableEq V] in
theorem variation_symmetric (w z : V → ℚ) : variation w z = variation z w := by
  unfold variation
  congr 1
  exact Finset.sum_congr rfl fun v _ => abs_sub_comm (w v) (z v)

/-- Rational witness at the exact TV boundary for non-strict two-thirds quorums. -/
def boundaryOld (i : Fin 4) : ℚ := if i = 3 then 0 else 1 / 3

def boundaryNew (i : Fin 4) : ℚ := if i = 0 then 0 else 1 / 3

theorem insufficient_overlap_counterexample :
    Normalized boundaryOld ∧ Normalized boundaryNew ∧
    variation boundaryOld boundaryNew = 1 / 3 ∧
    isQuorum boundaryOld (2 / 3) {0, 1} ∧ isQuorum boundaryNew (2 / 3) {2, 3} ∧
    honestIntersection (∅ : Finset (Fin 4)) {0, 1} {2, 3} = ∅ := by decide +kernel

/-- Strict quorums can also split, here at TV = 2/5 and with no Byzantine subjects. -/
def splitOld (i : Fin 4) : ℚ := if i = 0 then 2 / 5 else if i = 3 then 0 else 3 / 10

def splitNew (i : Fin 4) : ℚ := if i = 3 then 2 / 5 else if i = 0 then 0 else 3 / 10

theorem strict_overlap_counterexample :
    Normalized splitOld ∧ Normalized splitNew ∧
    variation splitOld splitNew = 2 / 5 ∧
    (2 : ℚ) / 3 < mass splitOld {0, 1} ∧ (2 : ℚ) / 3 < mass splitNew {2, 3} ∧
    honestIntersection (∅ : Finset (Fin 4)) {0, 1} {2, 3} = ∅ := by decide +kernel

structure DistributedTendermintQuorumIntersectionEpochTransitionContractSuite : Prop where
  bound : ∀ {V : Type} [Fintype V] [DecidableEq V] (w z : V → ℚ),
    Normalized w → Normalized z → ∀ B Q R q r,
    isQuorum w q Q → isQuorum z r R →
    honestCommon w z B + q + r - 2 ≤ mass (common w z) (honestIntersection B Q R)
  intersection : ∀ {V : Type} [Fintype V] [DecidableEq V] (w z : V → ℚ),
    Normalized w → Normalized z → ∀ B Q R q r,
    isQuorum w q Q → isQuorum z r R → 2 - q - r < honestCommon w z B →
    ∃ v ∈ Q ∩ R, v ∉ B ∧ 0 < w v ∧ 0 < z v
  variation_identity : ∀ {V : Type} [Fintype V] (w z : V → ℚ),
    Normalized w → Normalized z → mass (common w z) univ = 1 - variation w z
  static_recovery : ∀ {n : ℕ} (c : Config n) Q R,
    3 * c.mass c.byzantine ≤ c.total → c.quorum Q → c.quorum R →
    ∃ v ∈ Q ∩ R, v ∉ c.byzantine ∧ 0 < c.weight v
  reindex_invariance : ∀ {V : Type} [Fintype V] [DecidableEq V] (c : EpochConfig V) e,
    epochWeights (reindex c e) = epochWeights c
  boundary : Normalized boundaryOld ∧ Normalized boundaryNew ∧
    variation boundaryOld boundaryNew = 1 / 3 ∧
    isQuorum boundaryOld (2 / 3) {0, 1} ∧ isQuorum boundaryNew (2 / 3) {2, 3} ∧
    honestIntersection (∅ : Finset (Fin 4)) {0, 1} {2, 3} = ∅

theorem verification_suite : DistributedTendermintQuorumIntersectionEpochTransitionContractSuite :=
  ⟨quorum_intersection_weight_bound, honest_node_in_intersection, common_variation_identity,
    static_legacy_specialization, epoch_reindex_invariance, insufficient_overlap_counterexample⟩

end DistributedTendermintQuorumIntersectionEpochTransitionContract
