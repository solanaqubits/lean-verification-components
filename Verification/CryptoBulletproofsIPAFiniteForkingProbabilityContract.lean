/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsIPAForkingExtractionContract
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr

/-! Finite uniform sampling with replacement at a fixed prefix and fixed prover
state. Counts are of ordered outcomes, not repeated entries in a query log.
No adaptive rewind, random-oracle reduction, or whole-tree probability is claimed. -/
namespace CryptoBulletproofsIPAFiniteForkingProbabilityContract
open scoped BigOperators
open CryptoBulletproofsIPAForkingExtractionContract

section Counting
variable {F : Type} [Field F] [DecidableEq F]

/-- Choices remaining after one square class has been used. -/
def remaining (A : Finset F) (x : F) : Finset F := A.filter (fun y => y ^ 2 ≠ x ^ 2)

/-- Prefix extension retains order; different first elements give disjoint sets. -/
def extend (A : Finset F) (f : F → Finset (List F)) : Finset (List F) :=
  A.biUnion (fun x => (f x).image (List.cons x))

omit [Field F] in
theorem card_extend (A : Finset F) (f : F → Finset (List F)) :
    (extend A f).card = ∑ x ∈ A, (f x).card := by
  rw [extend, Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro x _
    exact Finset.card_image_of_injective _ (fun _ _ h => (List.cons.inj h).2)
  · intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro l hx hy
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hx
    obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hy
    exact hxy (List.cons.inj (ha.trans hb.symm)).1

/-- The independent uniform experiment has all ordered lists of n draws. -/
def samples (C : Finset F) : ℕ → Finset (List F)
  | 0 => {[]}
  | n + 1 => extend C (fun _ => samples C n)

/-- Accepted draws, with every square class used at most once. -/
def successes (A : Finset F) : ℕ → Finset (List F)
  | 0 => {[]}
  | n + 1 => extend A (fun x => successes (remaining A x) n)

omit [Field F] in
theorem card_samples (C : Finset F) (n : ℕ) : (samples C n).card = C.card ^ n := by
  induction n with
  | zero => simp [samples]
  | succ n ih => simp [samples, card_extend, ih, pow_succ, Nat.mul_comm]

theorem remaining_card_lower (A : Finset F) (x : F) : A.card - 2 ≤ (remaining A x).card := by
  have h := square_fiber_card_le_two A (x ^ 2)
  have he := Finset.card_filter_add_card_filter_not (s := A) (p := fun y => y ^ 2 = x ^ 2)
  change A.card - 2 ≤ (A.filter (fun y => ¬ y ^ 2 = x ^ 2)).card
  omega

/-- Natural-number lower bound, with truncated subtraction before casting. -/
def lowerCount (m : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => m * lowerCount (m - 2) n

theorem lowerCount_mono (n : ℕ) {m t : ℕ} (h : m ≤ t) : lowerCount m n ≤ lowerCount t n := by
  induction n generalizing m t with
  | zero => simp [lowerCount]
  | succ n ih => exact Nat.mul_le_mul h (ih (Nat.sub_le_sub_right h 2))

theorem success_count_lower (A : Finset F) (n : ℕ) : lowerCount A.card n ≤ (successes A n).card
    := by
  induction n generalizing A with
  | zero => simp [lowerCount, successes]
  | succ n ih =>
    rw [successes, card_extend, lowerCount]
    calc
      A.card * lowerCount (A.card - 2) n = ∑ _x ∈ A, lowerCount (A.card - 2) n := by simp
      _ ≤ ∑ x ∈ A, (successes (remaining A x) n).card := by
        apply Finset.sum_le_sum
        intro x _
        exact (lowerCount_mono n (remaining_card_lower A x)).trans (ih _)

theorem lowerCount_four (m : ℕ) :
    lowerCount m 4 = m * (m - 2) * (m - 4) * (m - 6) := by
  simp [lowerCount, Nat.sub_sub, Nat.mul_assoc]

theorem four_count_lower (A : Finset F) :
    A.card * (A.card - 2) * (A.card - 4) * (A.card - 6) ≤ (successes A 4).card := by
  simpa [lowerCount_four] using success_count_lower A 4

theorem mem_samples (C : Finset F) (n : ℕ) (l : List F) :
    l ∈ samples C n ↔ l.length = n ∧ ∀ x ∈ l, x ∈ C := by
  induction n generalizing l with
  | zero => cases l <;> simp [samples]
  | succ n ih =>
    cases l with
    | nil => simp [samples, extend]
    | cons a l => simp [samples, extend, ih, List.length_cons, and_assoc, and_left_comm, and_comm]

theorem mem_successes (A : Finset F) (n : ℕ) (l : List F) :
    l ∈ successes A n ↔ l.length = n ∧ (∀ x ∈ l, x ∈ A) ∧
      l.Pairwise (fun x y => x ^ 2 ≠ y ^ 2) := by
  induction n generalizing A l with
  | zero => cases l <;> simp [successes]
  | succ n ih =>
    cases l with
    | nil => simp [successes, extend]
    | cons a l =>
      simp only [successes, extend, Finset.mem_biUnion, Finset.mem_image, List.cons.injEq]
      simp only [exists_eq_right_right, ih]
      simp only [remaining, Finset.mem_filter, List.length_cons, Nat.succ_inj,
        List.pairwise_cons, List.mem_cons, forall_eq_or_imp]
      constructor
      · rintro ⟨ha, hl, hm, hp⟩
        exact ⟨hl, ⟨ha, fun x hx => (hm x hx).1⟩, ⟨fun x hx => Ne.symm (hm x hx).2, hp⟩⟩
      · rintro ⟨hl, ⟨ha, hm⟩, ⟨hn, hp⟩⟩
        exact ⟨ha, hl, fun x hx => ⟨hm x hx, Ne.symm (hn x hx)⟩, hp⟩

theorem successes_subset_samples {A C : Finset F} (h : A ⊆ C) (n : ℕ) :
    successes A n ⊆ samples C n := by
  intro l hl
  obtain ⟨hlen, hm, _⟩ := (mem_successes A n l).mp hl
  exact (mem_samples C n l).mpr ⟨hlen, fun x hx => h (hm x hx)⟩

/-- Uniform probability on C^4, represented by its cardinal denominator. -/
def successProbability (C A : Finset F) : ℚ := (successes A 4).card / (C.card : ℚ) ^ 4

def rowRate (C A : Finset F) : ℚ := (A.card : ℚ) / C.card

theorem probability_nonnegative (C A : Finset F) : 0 ≤ successProbability C A := by
  unfold successProbability; positivity

theorem probability_le_one {C A : Finset F} (hC : C.Nonempty) (hA : A ⊆ C) :
    successProbability C A ≤ 1 := by
  have hp : (0 : ℚ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hb := Finset.card_le_card (successes_subset_samples hA 4)
  rw [card_samples] at hb
  apply (div_le_one (pow_pos hp 4)).mpr
  exact_mod_cast hb

theorem fixed_prefix_probability_lower (C A : Finset F) (hC : C.Nonempty) (hm : 6 ≤ A.card) :
    (A.card : ℚ) * (A.card - 2) * (A.card - 4) * (A.card - 6) / (C.card : ℚ) ^ 4 ≤
      successProbability C A := by
  have h := four_count_lower A
  have hr : (A.card : ℚ) * (A.card - 2) * (A.card - 4) * (A.card - 6) ≤ (successes A 4).card := by
    have hc : ((A.card * (A.card - 2) * (A.card - 4) * (A.card - 6) : ℕ) : ℚ) ≤ (successes A
      4).card := by exact_mod_cast h
    push_cast [Nat.cast_sub (show 2 ≤ A.card by omega), Nat.cast_sub (show 4 ≤ A.card by omega),
      Nat.cast_sub hm] at hc
    exact hc
  have hn : (0 : ℚ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  exact div_le_div_of_nonneg_right hr (le_of_lt (pow_pos hn 4))

theorem seven_probability_positive (C A : Finset F) (hC : C.Nonempty) (hm : 7 ≤ A.card) :
    0 < successProbability C A := by
  have hm' : (6 : ℚ) < A.card := by exact_mod_cast (show 6 < A.card by omega)
  have hn : (0 : ℚ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have h := fixed_prefix_probability_lower C A hC (by omega)
  have h2 : (0 : ℚ) < A.card - 2 := by linarith
  have h4 : (0 : ℚ) < A.card - 4 := by linarith
  have h6 : (0 : ℚ) < A.card - 6 := by linarith
  have h0 : (0 : ℚ) < A.card := by linarith
  have : (0 : ℚ) < (A.card : ℚ) * (A.card - 2) * (A.card - 4) * (A.card - 6) / (C.card : ℚ) ^ 4
    := by positivity
  exact this.trans_le h

/-- Rate form of the four-draw lower bound. It is used only above 6/N. -/
def rateBound (N : ℕ) (t : ℚ) : ℚ := t * (t - 2 / N) * (t - 4 / N) * (t - 6 / N)

theorem rateBound_nonnegative (N : ℕ) (hN : 0 < N) (t : ℚ) (ht : 6 / N ≤ t) :
    0 ≤ rateBound N t := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have h2 : (2 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have h4 : (4 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have ht0 : 0 ≤ t := (by positivity : (0 : ℚ) ≤ 6 / N).trans ht
  unfold rateBound
  exact mul_nonneg (mul_nonneg (mul_nonneg ht0 (sub_nonneg.mpr (h2.trans ht)))
    (sub_nonneg.mpr (h4.trans ht))) (sub_nonneg.mpr ht)

theorem rateBound_positive (N : ℕ) (hN : 0 < N) (t : ℚ) (ht : 6 / N < t) :
    0 < rateBound N t := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have h2 : (2 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have h4 : (4 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have ht0 : 0 < t := (by positivity : (0 : ℚ) ≤ 6 / N).trans_lt ht
  exact mul_pos (mul_pos (mul_pos ht0 (sub_pos.mpr (h2.trans_lt ht)))
    (sub_pos.mpr (h4.trans_lt ht))) (sub_pos.mpr ht)

theorem rateBound_mono (N : ℕ) (hN : 0 < N) {t u : ℚ} (ht : 6 / N ≤ t) (hu : t ≤ u) :
    rateBound N t ≤ rateBound N u := by
  have hn : (0 : ℚ) < N := by exact_mod_cast hN
  have h2 : (2 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have h4 : (4 : ℚ) / N ≤ 6 / N := by exact div_le_div_of_nonneg_right (by norm_num) hn.le
  have ht0 : 0 ≤ t := (by positivity : (0 : ℚ) ≤ 6 / N).trans ht
  unfold rateBound
  have ht2 : 0 ≤ t - 2 / N := sub_nonneg.mpr (h2.trans ht)
  have ht4 : 0 ≤ t - 4 / N := sub_nonneg.mpr (h4.trans ht)
  have ht6 : 0 ≤ t - 6 / N := sub_nonneg.mpr ht
  have hu0 : 0 ≤ u := ht0.trans hu
  have hu2 : 0 ≤ u - 2 / N := by linarith
  have hu4 : 0 ≤ u - 4 / N := by linarith
  gcongr

omit [Field F] [DecidableEq F] in
theorem rowRate_bounds {C A : Finset F} (hC : C.Nonempty) (hA : A ⊆ C) :
    0 ≤ rowRate C A ∧ rowRate C A ≤ 1 := by
  have hn : (0 : ℚ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  refine ⟨by unfold rowRate; positivity, (div_le_one hn).mpr ?_⟩
  exact_mod_cast Finset.card_le_card hA

theorem fixed_prefix_rate_lower (C A : Finset F) (hC : C.Nonempty) (hm : 6 ≤ A.card) :
    rateBound C.card (rowRate C A) ≤ successProbability C A := by
  have hn : (C.card : ℚ) ≠ 0 := ne_of_gt (by exact_mod_cast Finset.card_pos.mpr hC)
  have he : rateBound C.card (rowRate C A) =
      (A.card : ℚ) * (A.card - 2) * (A.card - 4) * (A.card - 6) / (C.card : ℚ) ^ 4 := by
    unfold rateBound rowRate
    field_simp
  rw [he]
  exact fixed_prefix_probability_lower C A hC hm

theorem heavy_prefix_rate_lower (C A : Finset F) (hC : C.Nonempty) (θ : ℚ)
    (hθ : 6 / C.card ≤ θ) (ha : θ ≤ rowRate C A) :
    rateBound C.card θ ≤ successProbability C A := by
  have hn : (0 : ℚ) < C.card := by exact_mod_cast Finset.card_pos.mpr hC
  have hm : 6 ≤ A.card := by
    have hh : (6 : ℚ) / C.card ≤ A.card / C.card := hθ.trans ha
    have := (div_le_div_iff_of_pos_right hn).mp hh
    exact_mod_cast this
  exact (rateBound_mono C.card (Finset.card_pos.mpr hC) hθ ha).trans
    (fixed_prefix_rate_lower C A hC hm)

/-- Every sampled success is directly a distinct-square fork in the old API. -/
theorem sampled_success_isFork (A : Finset F) (a b c d : F)
    (h : [a, b, c, d] ∈ successes A 4) : IsFork A ![a, b, c, d] := by
  have hh := (mem_successes A 4 [a, b, c, d]).mp h
  simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp] at hh
  refine ⟨?_, ?_⟩
  · intro i; fin_cases i <;> simp_all
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem positive_probability_has_fork (C A : Finset F) (h : 0 < successProbability C A) :
    ∃ u, IsFork A u := by
  have hc : 0 < (successes A 4).card := by
    by_contra hh
    have hz : (successes A 4).card = 0 := by omega
    simp [successProbability, hz] at h
  obtain ⟨l, hl⟩ := Finset.card_pos.mp hc
  obtain ⟨a, b, c, d, rfl⟩ := List.length_eq_four.mp ((mem_successes A 4 l).mp hl).1
  exact ⟨![a, b, c, d], sampled_success_isFork A a b c d hl⟩

end Counting

section Prefixes
variable {S : Type}

/-- Uniform average over a finite nonempty family of fixed states/prefixes. -/
def average (s : Finset S) (f : S → ℚ) : ℚ := (∑ x ∈ s, f x) / s.card

def heavy (s : Finset S) (p : S → ℚ) (θ : ℚ) : Finset S := s.filter (fun x => θ ≤ p x)

def heavyFraction (s : Finset S) (p : S → ℚ) (θ : ℚ) : ℚ := (heavy s p θ).card / (s.card : ℚ)

theorem heavy_sum_bound (s : Finset S) (p : S → ℚ) (θ : ℚ)
    (hp : ∀ x ∈ s, p x ≤ 1) :
    (∑ x ∈ s, p x) ≤ (heavy s p θ).card + ((s.card : ℚ) - (heavy s p θ).card) * θ := by
  have hh : (∑ x ∈ s.filter (fun x => θ ≤ p x), p x) ≤ (heavy s p θ).card := by
    calc
      _ ≤ ∑ _x ∈ s.filter (fun x => θ ≤ p x), (1 : ℚ) :=
        Finset.sum_le_sum (fun x hx => hp x (Finset.mem_filter.mp hx).1)
      _ = _ := by simp [heavy]
  have hl : (∑ x ∈ s.filter (fun x => ¬ θ ≤ p x), p x) ≤
      ((s.filter (fun x => ¬ θ ≤ p x)).card : ℚ) * θ := by
    calc
      _ ≤ ∑ _x ∈ s.filter (fun x => ¬ θ ≤ p x), θ := Finset.sum_le_sum
        (fun _ hx => le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hx).2))
      _ = _ := by simp
  have he := Finset.sum_filter_add_sum_filter_not s (fun x => θ ≤ p x) p
  have hc : ((s.filter (fun x => θ ≤ p x)).card : ℚ) +
      (s.filter (fun x => ¬ θ ≤ p x)).card = s.card := by
    exact_mod_cast Finset.card_filter_add_card_filter_not (s := s) (p := fun x => θ ≤ p x)
  have hc' : ((s.filter (fun x => ¬ θ ≤ p x)).card : ℚ) = s.card - (heavy s p θ).card := by
    unfold heavy; linarith
  rw [hc'] at hl
  linarith

theorem heavy_prefix_fraction_lower (s : Finset S) (hs : s.Nonempty) (p : S → ℚ)
    (θ : ℚ) (hθ : θ < 1) (hp : ∀ x ∈ s, p x ≤ 1) :
    (average s p - θ) / (1 - θ) ≤ heavyFraction s p θ := by
  have hn : (0 : ℚ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hb := heavy_sum_bound s p θ hp
  apply (div_le_iff₀ (by linarith : (0 : ℚ) < 1 - θ)).mpr
  unfold average heavyFraction
  apply (mul_le_mul_iff_left₀ hn).mp
  field_simp
  nlinarith

theorem average_lower_on_heavy (s : Finset S) (hs : s.Nonempty) (p f : S → ℚ)
    (θ b : ℚ) (hf : ∀ x ∈ s, 0 ≤ f x)
    (hb : ∀ x ∈ heavy s p θ, b ≤ f x) :
    heavyFraction s p θ * b ≤ average s f := by
  have hn : (0 : ℚ) < s.card := by exact_mod_cast Finset.card_pos.mpr hs
  have hh : ((heavy s p θ).card : ℚ) * b ≤ ∑ x ∈ heavy s p θ, f x := by
    simpa using Finset.sum_le_sum hb
  have hl : 0 ≤ ∑ x ∈ s.filter (fun x => ¬ θ ≤ p x), f x :=
    Finset.sum_nonneg (fun x hx => hf x (Finset.mem_filter.mp hx).1)
  have he := Finset.sum_filter_add_sum_filter_not s (fun x => θ ≤ p x) f
  have ht : ((heavy s p θ).card : ℚ) * b ≤ ∑ x ∈ s, f x := by
    unfold heavy at hh ⊢; linarith
  unfold heavyFraction average
  rw [div_mul_eq_mul_div]
  exact (div_le_div_iff_of_pos_right hn).mpr ht

/-- First select a uniform prefix, then four independent uniform challenges.
This is a one-node experiment, not a probability for a recursively ready tree. -/
theorem average_forking_probability_lower {F : Type} [Field F] [DecidableEq F]
    (s : Finset S) (hs : s.Nonempty) (C : Finset F) (hC : C.Nonempty)
    (A : S → Finset F) (hA : ∀ x ∈ s, A x ⊆ C) (θ : ℚ)
    (hθ : 6 / C.card ≤ θ) (hθ1 : θ < 1) :
    (average s (fun x => rowRate C (A x)) - θ) / (1 - θ) * rateBound C.card θ ≤
      average s (fun x => successProbability C (A x)) := by
  have hb := rateBound_nonnegative C.card (Finset.card_pos.mpr hC) θ hθ
  calc
    _ ≤ heavyFraction s (fun x => rowRate C (A x)) θ * rateBound C.card θ :=
      mul_le_mul_of_nonneg_right
        (heavy_prefix_fraction_lower s hs _ θ hθ1 (fun x hx => (rowRate_bounds hC (hA x hx)).2)) hb
    _ ≤ _ := average_lower_on_heavy s hs _ _ θ _
      (fun x _ => probability_nonnegative C (A x)) (fun x hx =>
        heavy_prefix_rate_lower C (A x) hC θ hθ (Finset.mem_filter.mp hx).2)

theorem average_forking_probability_positive {F : Type} [Field F] [DecidableEq F]
    (s : Finset S) (hs : s.Nonempty) (C : Finset F) (hC : C.Nonempty)
    (A : S → Finset F) (hA : ∀ x ∈ s, A x ⊆ C) (θ : ℚ)
    (hθ : 6 / C.card < θ) (hθ1 : θ < 1)
    (hmean : θ < average s (fun x => rowRate C (A x))) :
    0 < average s (fun x => successProbability C (A x)) := by
  have hb := rateBound_positive C.card (Finset.card_pos.mpr hC) θ hθ
  have hp : 0 < (average s (fun x => rowRate C (A x)) - θ) / (1 - θ) :=
    div_pos (sub_pos.mpr hmean) (sub_pos.mpr hθ1)
  exact (mul_pos hp hb).trans_le (average_forking_probability_lower s hs C hC A hA θ hθ.le hθ1)

/-- Counting interpretation of the two-stage uniform experiment. -/
theorem average_probability_eq_count {F : Type} [Field F] [DecidableEq F]
    (s : Finset S) (C : Finset F) (A : S → Finset F) :
    average s (fun x => successProbability C (A x)) =
      (∑ x ∈ s, ((successes (A x) 4).card : ℚ)) / ((s.card : ℚ) * (C.card : ℚ)^4) := by
  unfold average successProbability
  rw [← Finset.sum_div, div_div, mul_comm]

end Prefixes
section Extraction
open CryptoBulletproofsInnerProduct CryptoBulletproofsTreeExtraction
variable {q : ℕ} [Fact q.Prime] {G : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] {k : ℕ}

/-- The probability space uses exactly the existing nonzero, accepted replies. -/
def replySet (calls : List (ZMod q))
    (replies : ZMod q → Option (IPATranscriptTree q G k)) : Finset (ZMod q) :=
  (acceptedChallenges calls replies).toFinset

omit [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G] in
theorem replySet_subset_calls (calls : List (ZMod q))
    (replies : ZMod q → Option (IPATranscriptTree q G k)) :
    replySet calls replies ⊆ calls.toFinset := by
  intro x hx
  exact List.mem_toFinset.mpr ((mem_acceptedChallenges calls replies x).mp (List.mem_toFinset.mp
    hx)).1

omit [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G] in
theorem replySet_nonzero (calls : List (ZMod q))
    (replies : ZMod q → Option (IPATranscriptTree q G k)) (x : ZMod q)
    (hx : x ∈ replySet calls replies) : x ≠ 0 :=
  ((mem_acceptedChallenges calls replies x).mp (List.mem_toFinset.mp hx)).2.1

/-- Successful sampled challenges can be assembled without selecting other
branches. Completed, context-valid child trees remain explicit premises. -/
theorem sampled_fork_extracts (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q G k))
    (u : Fin 4 → ZMod q) (hu : IsFork (replySet calls replies) u)
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t) :
    ∃ r, checked_extract s (.node s msg u (fun i => (replies (u i)).getD (emptyTree k))) = .ok r ∧
      ResultValid s r := by
  have hm (i : Fin 4) := (mem_acceptedChallenges calls replies (u i)).mp
    (List.mem_toFinset.mp (hu.1 i))
  have hn : ∀ i, u i ≠ 0 := fun i => (hm i).2.1
  have ht : ValidAcceptingTree s (.node s msg u (fun i => (replies (u i)).getD (emptyTree k))) := by
    simp only [ValidAcceptingTree, dif_pos hn, true_and]
    refine ⟨hu.2, ?_⟩
    intro i
    cases hr : replies (u i) with
    | none => have hi := (hm i).2.2; simp [hr] at hi
    | some t => simpa [hr] using hv (u i) (hn i) t hr
  exact ⟨_, by simp [checked_extract, ht], tree_extraction_soundness s _ ht⟩

/-- Positive one-node probability yields an accepting tree and the old
witness-or-relation contract only when all counted replies are valid children. -/
theorem positive_probability_extracts (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q G k))
    (hp : 0 < successProbability calls.toFinset (replySet calls replies))
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t) :
    ∃ t r, checked_extract s t = .ok r ∧ ResultValid s r := by
  obtain ⟨u, hu⟩ := positive_probability_has_fork _ _ hp
  obtain ⟨r, hr, hvalid⟩ := sampled_fork_extracts s msg calls replies u hu hv
  exact ⟨_, r, hr, hvalid⟩

omit [DecidableEq G] in
theorem finite_probability_dichotomy (s : Statement q G (k + 1)) (msg : RoundMessages G)
    (calls : List (ZMod q)) (replies : ZMod q → Option (IPATranscriptTree q G k))
    (hp : 0 < successProbability calls.toFinset (replySet calls replies))
    (hv : ∀ x (hx : x ≠ 0) t, replies x = some t →
      ValidAcceptingTree (child_statement s msg (Units.mk0 x hx)) t) :
    (∃ a b : Vec (k + 1) (ZMod q), s.P = ipa_target s.U s.G s.H a b) ∨
      (∃ c, c ≠ 0 ∧ evaluate s c = 0) := by
  classical
  obtain ⟨_, r, _, h⟩ := positive_probability_extracts s msg calls replies hp hv
  cases r with
  | witness a b => exact Or.inl ⟨a, b, h⟩
  | relation c => exact Or.inr ⟨c, h⟩
end Extraction

structure CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite : Prop where
  counting : ∀ (F : Type) [Field F] [DecidableEq F] (A : Finset F),
    A.card * (A.card - 2) * (A.card - 4) * (A.card - 6) ≤ (successes A 4).card
  probability : ∀ (F : Type) [Field F] [DecidableEq F] (C A : Finset F),
    C.Nonempty → 6 ≤ A.card →
    (A.card : ℚ) * (A.card - 2) * (A.card - 4) * (A.card - 6) / (C.card : ℚ)^4 ≤
      successProbability C A
  positivity : ∀ (F : Type) [Field F] [DecidableEq F] (C A : Finset F),
    C.Nonempty → 7 ≤ A.card → 0 < successProbability C A
  heavy_prefixes : ∀ (S : Type) [DecidableEq S] (s : Finset S) (p : S → ℚ) (θ : ℚ),
    s.Nonempty → θ < 1 → (∀ x ∈ s, p x ≤ 1) →
      (average s p - θ) / (1 - θ) ≤ heavyFraction s p θ
  combined : ∀ (S : Type) [DecidableEq S] (F : Type) [Field F] [DecidableEq F]
    (s : Finset S) (C : Finset F) (A : S → Finset F) (θ : ℚ),
    s.Nonempty → C.Nonempty → (∀ x ∈ s, A x ⊆ C) → 6 / C.card ≤ θ → θ < 1 →
    (average s (fun x => rowRate C (A x)) - θ) / (1 - θ) * rateBound C.card θ ≤
      average s (fun x => successProbability C (A x))
  extraction : ∀ (q : ℕ) [Fact q.Prime] (G : Type) [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] (k : ℕ) (s : CryptoBulletproofsTreeExtraction.Statement q G (k + 1))
    (msg : CryptoBulletproofsInnerProduct.RoundMessages G) (calls : List (ZMod q))
    (replies : ZMod q → Option (CryptoBulletproofsTreeExtraction.IPATranscriptTree q G k)),
    0 < successProbability calls.toFinset (replySet calls replies) →
    (∀ x (hx : x ≠ 0) t, replies x = some t →
      CryptoBulletproofsTreeExtraction.ValidAcceptingTree
        (CryptoBulletproofsTreeExtraction.child_statement s msg (Units.mk0 x hx)) t) →
    ∃ t r, CryptoBulletproofsTreeExtraction.checked_extract s t = .ok r ∧
      CryptoBulletproofsTreeExtraction.ResultValid s r

theorem verification_suite : CryptoBulletproofsIPAFiniteForkingProbabilityContractSuite where
  counting := fun _ _ _ => four_count_lower
  probability := fun _ _ _ => fixed_prefix_probability_lower
  positivity := fun _ _ _ => seven_probability_positive
  heavy_prefixes := fun _ _ s p θ hs hθ hp => heavy_prefix_fraction_lower s hs p θ hθ hp
  combined := fun _ _ _ _ _ s C A θ hs hC hA hθ hθ1 =>
    average_forking_probability_lower s hs C hC A hA θ hθ hθ1
  extraction := fun _ _ _ _ _ _ _ => positive_probability_extracts

end CryptoBulletproofsIPAFiniteForkingProbabilityContract
