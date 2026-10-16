/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoBulletproofsRangeReduction
import Verification.CryptoBulletproofsWitnessExtraction
import Verification.CryptoBulletproofsTreeExtraction
import Verification.CryptoBulletproofsRangeInterpolation

/-! Conditional algebraic composition from supplied openings of A, S and V.
Openings carry no bit/range assumption. Rewinding, obtaining these openings,
computational binding and Fiat–Shamir/ROM are not established here. -/
namespace CryptoBulletproofsRangeWitnessExtraction
open scoped BigOperators
open CryptoBulletproofsInnerProduct CryptoBulletproofsRangeReduction
namespace Tree
export CryptoBulletproofsTreeExtraction (Statement IPATranscriptTree ValidAcceptingTree
  extractTree tree_extraction_soundness TreeExtractionResult)
end Tree
variable {q : ℕ} [Fact (Nat.Prime q)] {k : ℕ}
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]

structure OpeningCertificate (q k : ℕ) where
  a : Vec k (ZMod q)
  b : Vec k (ZMod q)
  s : Vec k (ZMod q)
  t : Vec k (ZMod q)
  alpha : ZMod q
  rho : ZMod q
  v : ZMod q
  gamma : ZMod q

def ValidOpenings (p : Generators q A k) (Ac Sc V : A) (c : OpeningCertificate q k) : Prop :=
  Ac = vector_commit p c.a c.b c.alpha ∧ Sc = vector_commit p c.s c.t c.rho ∧
    V = value_commit p c.v c.gamma

/-- Coefficients always refer to the ORIGINAL generators, including blinding. -/
structure RelationCoefficients (q k : ℕ) where
  g : Vec k (ZMod q)
  h : Vec k (ZMod q)
  base : ZMod q
  blind : ZMod q
  ipa : ZMod q
  deriving DecidableEq

instance : Zero (RelationCoefficients q k) := ⟨⟨0, 0, 0, 0, 0⟩⟩

def relation_eval (p : Generators q A k) (c : RelationCoefficients q k) : A :=
  multiscalar_mul c.g p.G + multiscalar_mul c.h p.H + c.base • p.B +
    c.blind • p.Hblind + c.ipa • p.U

def lift_scaled (y : ZMod q) (g h : Vec k (ZMod q)) (blind ipa : ZMod q) :
    RelationCoefficients q k := ⟨g, fun i => h i * (y⁻¹) ^ i.val, 0, blind, ipa⟩

theorem lift_scaled_eval (p : Generators q A k) (y : ZMod q)
    (g h : Vec k (ZMod q)) (blind ipa : ZMod q) :
    relation_eval p (lift_scaled y g h blind ipa) =
      multiscalar_mul g p.G + multiscalar_mul h (scaled_H p.H y) +
        blind • p.Hblind + ipa • p.U := by
  simp [relation_eval, lift_scaled, multiscalar_mul, scaled_H, smul_smul]

theorem lift_scaled_zero_iff (y : ZMod q) (hy : y ≠ 0)
    (g h : Vec k (ZMod q)) (blind ipa : ZMod q) :
    lift_scaled y g h blind ipa = 0 ↔ g = 0 ∧ h = 0 ∧ blind = 0 ∧ ipa = 0 := by
  constructor
  · intro he
    have hg := congrArg RelationCoefficients.g he
    have hh := congrArg RelationCoefficients.h he
    have hb := congrArg RelationCoefficients.blind he
    have hu := congrArg RelationCoefficients.ipa he
    refine ⟨hg, ?_, hb, hu⟩
    funext i
    have hi := congrFun hh i
    change h i * (y⁻¹) ^ i.val = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_right (pow_ne_zero _ (inv_ne_zero hy))
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [lift_scaled]
    rfl

/-- Shared A,S,V are outside this structure; T1,T2 depend on Y,Z but not X. -/
structure TranscriptFamily (q : ℕ) (A : Type) (k : ℕ) where
  y : Fin (2 ^ k) → ZMod q
  z : Fin 3 → ZMod q
  x : Fin (2 ^ k) → Fin 3 → Fin 3 → ZMod q
  T1 : Fin (2 ^ k) → Fin 3 → A
  T2 : Fin (2 ^ k) → Fin 3 → A
  tx : Fin (2 ^ k) → Fin 3 → Fin 3 → ZMod q
  taux : Fin (2 ^ k) → Fin 3 → Fin 3 → ZMod q
  mu : Fin (2 ^ k) → Fin 3 → Fin 3 → ZMod q
  trees : Fin (2 ^ k) → Fin 3 → Fin 3 → Tree.IPATranscriptTree q A k

def branch_statement (p : Generators q A k) (Ac Sc : A) (f : TranscriptFamily q A k)
    (i : Fin (2 ^ k)) (j l : Fin 3) : Tree.Statement q A k :=
  ⟨p.U, p.G, scaled_H p.H (f.y i),
    range_target p Ac Sc (f.y i) (f.z j) (f.x i j l) (f.mu i j l) (f.tx i j l)⟩

def ValidFamily (p : Generators q A k) (Ac Sc V : A) (f : TranscriptFamily q A k) : Prop :=
  Function.Injective f.y ∧ (∀ i, f.y i ≠ 0) ∧ Function.Injective f.z ∧
  (∀ i j, Function.Injective (f.x i j)) ∧
  (∀ i j l, value_commit p (f.tx i j l) (f.taux i j l) =
    (f.z j) ^ 2 • V + delta_fn (f.y i) (f.z j) (2 ^ k) • p.B +
      f.x i j l • f.T1 i j + (f.x i j l) ^ 2 • f.T2 i j) ∧
  (∀ i j l, Tree.ValidAcceptingTree (branch_statement p Ac Sc f i j l) (f.trees i j l))

def discrepancy (c : OpeningCertificate q k) (y z x mu tx : ZMod q)
    (a b : Vec k (ZMod q)) : RelationCoefficients q k :=
  lift_scaled y (a - l_poly c.a c.s z x) (b - r_poly c.b c.t y z x)
    (mu - c.alpha - x * c.rho) (dot a b - tx)

/-- Zero discrepancy forces coordinate agreement; it is not an input assumption. -/
theorem discrepancy_zero_iff (c : OpeningCertificate q k) (y z x mu tx : ZMod q)
    (hy : y ≠ 0) (a b : Vec k (ZMod q)) :
    discrepancy c y z x mu tx a b = 0 ↔
      a = l_poly c.a c.s z x ∧ b = r_poly c.b c.t y z x ∧
      mu = c.alpha + x * c.rho ∧ dot a b = tx := by
  simp only [discrepancy, lift_scaled_zero_iff y hy, sub_sub, sub_eq_zero]

/-- Differences of two openings of the SAME target give an explicit relation. -/
theorem discrepancy_annihilates (p : Generators q A k) (c : OpeningCertificate q k)
    (y z x mu tx : ZMod q) (hy : y ≠ 0) (a b : Vec k (ZMod q))
    (he : range_target p (vector_commit p c.a c.b c.alpha)
      (vector_commit p c.s c.t c.rho) y z x mu tx = ipa_target p.U p.G (scaled_H p.H y) a b) :
    relation_eval p (discrepancy c y z x mu tx a b) = 0 := by
  have hi := range_ipa_target_invariant p c.a c.b c.s c.t c.alpha c.rho y z x hy
  have hsum (u v : Vec k (ZMod q)) (G : Vec k A) :
      multiscalar_mul (u - v) G = multiscalar_mul u G - multiscalar_mul v G := by
    simp [multiscalar_mul, sub_smul, Finset.sum_sub_distrib]
  rw [discrepancy, lift_scaled_eval, hsum, hsum]
  calc
    _ = (ipa_target p.U p.G (scaled_H p.H y) a b -
        ipa_target p.U p.G (scaled_H p.H y) (l_poly c.a c.s z x) (r_poly c.b c.t y z x)) -
      (range_target p (vector_commit p c.a c.b c.alpha) (vector_commit p c.s c.t c.rho)
        y z x mu tx -
       range_target p (vector_commit p c.a c.b c.alpha) (vector_commit p c.s c.t c.rho)
        y z x (c.alpha + x * c.rho) (dot (l_poly c.a c.s z x) (r_poly c.b c.t y z x))) := by
      simp only [ipa_target, range_target, sub_smul, add_smul]
      change _ = (_ + dot a b • p.U -
        (_ + dot (l_poly c.a c.s z x) (r_poly c.b c.t y z x) • p.U)) - _
      abel
    _ = 0 := by rw [he, hi]; abel

def local_coeff (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (i : Fin (2 ^ k)) (j l : Fin 3) : RelationCoefficients q k :=
  match Tree.extractTree (f.trees i j l) with
  | .relation cs => lift_scaled (f.y i) cs.1 cs.2.1 0 cs.2.2
  | .witness a b => discrepancy c (f.y i) (f.z j) (f.x i j l) (f.mu i j l) (f.tx i j l) a b

theorem local_coeff_annihilates (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (hc : ValidOpenings p Ac Sc V c) (hf : ValidFamily p Ac Sc V f)
    (i : Fin (2 ^ k)) (j l : Fin 3) : relation_eval p (local_coeff c f i j l) = 0 := by
  have ht := Tree.tree_extraction_soundness _ _ (hf.2.2.2.2.2 i j l)
  unfold local_coeff
  cases he : Tree.extractTree (f.trees i j l) with
  | relation cs =>
    rw [he] at ht
    rw [lift_scaled_eval]
    simpa [CryptoBulletproofsTreeExtraction.ResultValid,
      CryptoBulletproofsTreeExtraction.evaluate, branch_statement] using ht.2
  | witness a b =>
    rw [he] at ht
    apply discrepancy_annihilates p c _ _ _ _ _ (hf.2.1 i) a b
    simpa [CryptoBulletproofsTreeExtraction.ResultValid, branch_statement, hc.1, hc.2.1] using ht

theorem local_coeff_zero_tx (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (hf : ValidFamily p Ac Sc V f) (i : Fin (2 ^ k)) (j l : Fin 3)
    (hz : local_coeff c f i j l = 0) :
    f.tx i j l = dot (l_poly c.a c.s (f.z j) (f.x i j l))
      (r_poly c.b c.t (f.y i) (f.z j) (f.x i j l)) := by
  have ht := Tree.tree_extraction_soundness _ _ (hf.2.2.2.2.2 i j l)
  unfold local_coeff at hz
  cases he : Tree.extractTree (f.trees i j l) with
  | relation cs =>
    rw [he] at hz ht
    obtain ⟨hg, hh, _, hu⟩ := (lift_scaled_zero_iff _ (hf.2.1 i) _ _ _ _).mp hz
    exact False.elim (ht.1 (by rcases cs with ⟨g, h, u⟩; simp_all))
  | witness a b =>
    rw [he] at hz
    obtain ⟨ha, hb, _, hu⟩ := (lift_scaled_zero_iff _ (hf.2.1 i) _ _ _ _).mp hz
    rw [sub_eq_zero.mp ha, sub_eq_zero.mp hb] at hu
    exact (sub_eq_zero.mp hu).symm

def grid_coeff (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (i : Fin (2 ^ k)) (j : Fin 3) : RelationCoefficients q k :=
  ⟨0, 0, t0 c.a c.b (f.y i) (f.z j) - (f.z j) ^ 2 * c.v - delta_fn (f.y i) (f.z j) (2 ^ k),
    CryptoBulletproofsWitnessExtraction.interpolate_quad (f.x i j) (f.taux i j) 0 -
      (f.z j) ^ 2 * c.gamma, 0⟩

theorem group_constant_zero (x : Fin 3 → ZMod q) (hx : Function.Injective x)
    (a b c : A) (he : ∀ l, a + x l • b + (x l) ^ 2 • c = 0) : a = 0 := by
  have h := CryptoBulletproofsWitnessExtraction.quadratic_module_interpolation
    (x 0) (x 1) (x 2) 0 a b c (hx.ne (by decide)) (hx.ne (by decide)) (hx.ne (by decide))
  simpa only [he, smul_zero, add_zero, zero_smul, zero_pow (by decide : 2 ≠ 0)] using h.symm

theorem grid_coeff_annihilates (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (hc : ValidOpenings p Ac Sc V c) (hf : ValidFamily p Ac Sc V f)
    (hz : ∀ i j l, local_coeff c f i j l = 0) (i : Fin (2 ^ k)) (j : Fin 3) :
    relation_eval p (grid_coeff c f i j) = 0 := by
  let tau := CryptoBulletproofsWitnessExtraction.interpolate_quad (f.x i j) (f.taux i j)
  let C0 := (t0 c.a c.b (f.y i) (f.z j) - (f.z j) ^ 2 * c.v -
    delta_fn (f.y i) (f.z j) (2 ^ k)) • p.B + (tau 0 - (f.z j) ^ 2 * c.gamma) • p.Hblind
  let C1 := t1 c.a c.b c.s c.t (f.y i) (f.z j) • p.B + tau 1 • p.Hblind - f.T1 i j
  let C2 := t2 c.s c.t (f.y i) • p.B + tau 2 • p.Hblind - f.T2 i j
  have he (l : Fin 3) : C0 + f.x i j l • C1 + (f.x i j l) ^ 2 • C2 = 0 := by
    have ht := local_coeff_zero_tx p Ac Sc V c f hf i j l (hz i j l)
    have hτ := CryptoBulletproofsWitnessExtraction.interpolate_quad_evaluates
      (f.x i j) (f.taux i j) (hf.2.2.2.1 i j) l
    change tau 0 + tau 1 * f.x i j l + tau 2 * (f.x i j l) ^ 2 = f.taux i j l at hτ
    calc
      _ = value_commit p (f.tx i j l) (f.taux i j l) -
          ((f.z j) ^ 2 • V + delta_fn (f.y i) (f.z j) (2 ^ k) • p.B +
            f.x i j l • f.T1 i j + (f.x i j l) ^ 2 • f.T2 i j) := by
        rw [ht, poly_inner_product_eq, ← hτ, hc.2.2]
        dsimp only [C0, C1, C2, value_commit]
        match_scalars <;> ring
      _ = 0 := sub_eq_zero.mpr (hf.2.2.2.2.1 i j l)
  have hh := group_constant_zero (f.x i j) (hf.2.2.2.1 i j) C0 C1 C2 he
  simpa [relation_eval, grid_coeff, multiscalar_mul, C0, tau] using hh

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem grid_coeff_zero_equality (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (i : Fin (2 ^ k)) (j : Fin 3) (hz : grid_coeff c f i j = 0) :
    t0 c.a c.b (f.y i) (f.z j) = (f.z j) ^ 2 * c.v + delta_fn (f.y i) (f.z j) (2 ^ k) := by
  have h := congrArg RelationCoefficients.base hz
  change _ - _ - _ = 0 at h
  linear_combination h

/-- Finite scans are executable and choose the first nonzero coefficient tuple. -/
def first_relation (cs : List (RelationCoefficients q k)) : Option (RelationCoefficients q k) :=
  cs.find? (fun c => decide (c ≠ 0))

def local_candidates (c : OpeningCertificate q k) (f : TranscriptFamily q A k) :
    List (RelationCoefficients q k) :=
  (List.ofFn fun i => (List.ofFn fun j => List.ofFn fun l => local_coeff c f i j l).flatten).flatten

def grid_candidates (c : OpeningCertificate q k) (f : TranscriptFamily q A k) :
    List (RelationCoefficients q k) :=
  (List.ofFn fun i => List.ofFn fun j => grid_coeff c f i j).flatten

theorem first_relation_some {cs : List (RelationCoefficients q k)} {c : RelationCoefficients q k}
    (h : first_relation cs = some c) : c ∈ cs ∧ c ≠ 0 :=
  ⟨List.mem_of_find?_eq_some h,
    of_decide_eq_true (List.find?_some (p := fun c => decide (c ≠ 0)) h)⟩

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem local_candidates_none (c : OpeningCertificate q k) (f : TranscriptFamily q A k) :
    first_relation (local_candidates c f) = none ↔ ∀ i j l, local_coeff c f i j l = 0 := by
  simp only [first_relation, List.find?_eq_none, decide_eq_true_eq, not_not,
    local_candidates, List.forall_mem_flatten, List.forall_mem_ofFn_iff]

omit [AddCommGroup A] [Module (ZMod q) A] in
theorem grid_candidates_none (c : OpeningCertificate q k) (f : TranscriptFamily q A k) :
    first_relation (grid_candidates c f) = none ↔ ∀ i j, grid_coeff c f i j = 0 := by
  simp only [first_relation, List.find?_eq_none, decide_eq_true_eq, not_not,
    grid_candidates, List.forall_mem_flatten, List.forall_mem_ofFn_iff]

structure RangeWitness (q k : ℕ) where
  a : Vec k (ZMod q)
  b : Vec k (ZMod q)
  value : ℕ
  gamma : ZMod q
  deriving DecidableEq

def certificate_witness (c : OpeningCertificate q k) : RangeWitness q k :=
  ⟨c.a, c.b, c.v.val, c.gamma⟩

def WitnessValid (p : Generators q A k) (V : A) (w : RangeWitness q k) : Prop :=
  (∀ i, w.a i = 0 ∨ w.a i = 1) ∧ (∀ i, w.b i = w.a i - 1) ∧
  (∑ i, (2 : ZMod q) ^ i.val * w.a i) = (w.value : ZMod q) ∧
  w.value < 2 ^ (2 ^ k) ∧ V = value_commit p (w.value : ZMod q) w.gamma ∧
  CryptoBulletproofsRangeInterpolation.reconstructed_value w.a = w.value

abbrev ExtractionResult (q k : ℕ) := Sum (RangeWitness q k) (RelationCoefficients q k)

def ResultValid (p : Generators q A k) (V : A) : ExtractionResult q k → Prop
  | .inl w => WitnessValid p V w
  | .inr c => c ≠ 0 ∧ relation_eval p c = 0

def extract (c : OpeningCertificate q k) (f : TranscriptFamily q A k) : ExtractionResult q k :=
  match first_relation (local_candidates c f) with
  | some r => .inr r
  | none => match first_relation (grid_candidates c f) with
    | some r => .inr r
    | none => .inl (certificate_witness c)

theorem certificate_witness_valid (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (hc : ValidOpenings p Ac Sc V c) (hf : ValidFamily p Ac Sc V f)
    (hq : 2 ^ (2 ^ k) < q) (hz : ∀ i j, grid_coeff c f i j = 0) :
    WitnessValid p V (certificate_witness c) := by
  have hn : 1 ≤ 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide))
  have hg := fun i j => grid_coeff_zero_equality c f i j (hz i j)
  have hi := CryptoBulletproofsRangeInterpolation.grid_equalities_imply_formal_identity
    c.a c.b c.v hn f.y f.z hf.1 hf.2.2.1 hg
  obtain ⟨hb, hbit, hv⟩ := formal_coefficients_imply_range c.a c.b c.v hi
  have hgn : CryptoBulletproofsRangeInterpolation.GridEqualities c.a c.b
      (c.v.val : ZMod q) f.y f.z := by
    simpa [CryptoBulletproofsRangeInterpolation.GridEqualities] using hg
  refine ⟨hbit, hb, ?_, ?_, ?_, ?_⟩
  · simpa [certificate_witness] using hv
  · exact CryptoBulletproofsRangeInterpolation.grid_equalities_imply_natural_range
      c.a c.b c.v.val hn f.y f.z hf.1 hf.2.2.1 (ZMod.val_lt c.v) hq hgn
  · simpa [certificate_witness] using hc.2.2
  · exact CryptoBulletproofsRangeInterpolation.grid_reconstructed_value_eq
      c.a c.b c.v.val hn f.y f.z hf.1 hf.2.2.1 (ZMod.val_lt c.v) hq hgn

theorem extraction_soundness (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k)
    (hc : ValidOpenings p Ac Sc V c) (hf : ValidFamily p Ac Sc V f)
    (hq : 2 ^ (2 ^ k) < q) : ResultValid p V (extract c f) := by
  unfold extract
  cases hl : first_relation (local_candidates c f) with
  | some r =>
    obtain ⟨hm, hn⟩ := first_relation_some hl
    refine ⟨hn, ?_⟩
    have hall : ∀ r ∈ local_candidates c f, relation_eval p r = 0 := by
      simp only [local_candidates, List.forall_mem_flatten, List.forall_mem_ofFn_iff]
      exact local_coeff_annihilates p Ac Sc V c f hc hf
    exact hall r hm
  | none =>
    have hz := (local_candidates_none c f).mp hl
    cases hg : first_relation (grid_candidates c f) with
    | some r =>
      obtain ⟨hm, hn⟩ := first_relation_some hg
      refine ⟨hn, ?_⟩
      have hall : ∀ r ∈ grid_candidates c f, relation_eval p r = 0 := by
        simp only [grid_candidates, List.forall_mem_flatten, List.forall_mem_ofFn_iff]
        exact grid_coeff_annihilates p Ac Sc V c f hc hf hz
      exact hall r hm
    | none =>
      exact certificate_witness_valid p Ac Sc V c f hc hf hq ((grid_candidates_none c f).mp hg)

instance [DecidableEq A] (p : Generators q A k) (Ac Sc V : A) (c : OpeningCertificate q k) :
    Decidable (ValidOpenings p Ac Sc V c) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance [DecidableEq A] (p : Generators q A k) (Ac Sc V : A) (f : TranscriptFamily q A k) :
    Decidable (ValidFamily p Ac Sc V f) := by unfold ValidFamily; infer_instance

inductive ExtractionError where
  | invalidDepth | insufficientField | invalidOpenings | invalidFamily
  deriving DecidableEq, Repr

def checked_extract [DecidableEq A] (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k) :
    Except ExtractionError (ExtractionResult q k) :=
  if 1 ≤ k then
    if 2 ^ (2 ^ k) < q then
      if ValidOpenings p Ac Sc V c then
        if ValidFamily p Ac Sc V f then .ok (extract c f) else .error .invalidFamily
      else .error .invalidOpenings
    else .error .insufficientField
  else .error .invalidDepth

theorem checked_extract_success_iff [DecidableEq A] (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k) (r : ExtractionResult q k) :
    checked_extract p Ac Sc V c f = .ok r ↔
      1 ≤ k ∧ 2 ^ (2 ^ k) < q ∧ ValidOpenings p Ac Sc V c ∧ ValidFamily p Ac Sc V f ∧
        extract c f = r := by
  simp only [checked_extract]
  split_ifs <;> simp_all

theorem checked_extract_sound [DecidableEq A] (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k) (r : ExtractionResult q k)
    (h : checked_extract p Ac Sc V c f = .ok r) : ResultValid p V r := by
  obtain ⟨_, hq, hc, hf, hr⟩ := (checked_extract_success_iff p Ac Sc V c f r).mp h
  rw [← hr]
  exact extraction_soundness p Ac Sc V c f hc hf hq

/-- Scaling is injective on the IPA coefficient tuple for a nonzero Y challenge. -/
theorem lift_tree_relation_nontrivial (y : ZMod q) (hy : y ≠ 0)
    (cs : CryptoBulletproofsTreeExtraction.GeneratorCoefficients q k) (hc : cs ≠ 0) :
    lift_scaled y cs.1 cs.2.1 0 cs.2.2 ≠ 0 := by
  intro hz
  obtain ⟨hg, hh, _, hu⟩ := (lift_scaled_zero_iff y hy _ _ _ _).mp hz
  apply hc
  rcases cs with ⟨g, h, u⟩
  simp_all

structure CryptoBulletproofsRangeWitnessExtractionSuite : Prop where
  composition : ∀ {q} [Fact (Nat.Prime q)] {k} {A : Type} [AddCommGroup A]
    [Module (ZMod q) A] (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k),
    ValidOpenings p Ac Sc V c → ValidFamily p Ac Sc V f → 2 ^ (2 ^ k) < q →
      ResultValid p V (extract c f)
  checked : ∀ {q} [Fact (Nat.Prime q)] {k} {A : Type} [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] (p : Generators q A k) (Ac Sc V : A)
    (c : OpeningCertificate q k) (f : TranscriptFamily q A k) (r : ExtractionResult q k),
    checked_extract p Ac Sc V c f = .ok r → ResultValid p V r
  lift : ∀ {q} [Fact (Nat.Prime q)] {k} (y : ZMod q), y ≠ 0 →
    ∀ (cs : CryptoBulletproofsTreeExtraction.GeneratorCoefficients q k), cs ≠ 0 →
      lift_scaled y cs.1 cs.2.1 0 cs.2.2 ≠ 0

theorem verification_suite : CryptoBulletproofsRangeWitnessExtractionSuite where
  composition := extraction_soundness
  checked := checked_extract_sound
  lift := lift_tree_relation_nontrivial

end CryptoBulletproofsRangeWitnessExtraction
