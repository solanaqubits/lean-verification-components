/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoCommitmentVectorPedersenGroup
import Verification.CryptoSchnorrIdentification
import Mathlib.Tactic.Module

/-!
# Algebraic Bulletproofs inner product argument

An executable interactive algebraic core. Challenges are units and supplied by
an external verifier. Completeness is not knowledge soundness or zero knowledge.
No independence of group generators is assumed.
-/
namespace CryptoBulletproofsInnerProduct

open scoped BigOperators
variable {q : ℕ} [Fact (Nat.Prime q)]
variable {A : Type} [AddCommGroup A] [Module (ZMod q) A]

abbrev Vec (k : ℕ) (B : Type) := Fin (2 ^ k) → B

def dot_product {n : ℕ} (a b : Fin n → ZMod q) : ZMod q := ∑ i, a i * b i

def multiscalar_mul {n : ℕ} (a : Fin n → ZMod q) (G : Fin n → A) : A :=
  ∑ i, a i • G i

def ipa_target {n : ℕ} (U : A) (G H : Fin n → A) (a b : Fin n → ZMod q) : A :=
  multiscalar_mul a G + multiscalar_mul b H + dot_product a b • U

theorem vector_commitment_bridge {n : ℕ} (U : A) (G : Fin n → A)
    (a : Fin n → ZMod q) (r : ZMod q) :
    CryptoCommitmentVectorPedersenGroup.commit_vec G U a r = multiscalar_mul a G + r • U := rfl

private theorem width_succ (k : ℕ) : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
  simp [pow_succ, Nat.mul_two]

def loIndex {k : ℕ} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  Fin.cast (width_succ k) (Fin.castAdd (2 ^ k) i)

def hiIndex {k : ℕ} (i : Fin (2 ^ k)) : Fin (2 ^ (k + 1)) :=
  Fin.cast (width_succ k) (Fin.natAdd (2 ^ k) i)

def split_lo {k : ℕ} {B : Type} (v : Vec (k + 1) B) : Vec k B := fun i => v (loIndex i)
def split_hi {k : ℕ} {B : Type} (v : Vec (k + 1) B) : Vec k B := fun i => v (hiIndex i)

theorem sum_split {k : ℕ} {B : Type} [AddCommMonoid B] (v : Vec (k + 1) B) :
    ∑ i, v i = (∑ i, split_lo v i) + ∑ i, split_hi v i := by
  rw [← (finCongr (width_succ k)).sum_comp v, Fin.sum_univ_add]
  rfl

structure RoundMessages (A : Type) where
  L : A
  R : A
  deriving DecidableEq

structure IPATranscript (q : ℕ) (A : Type) (k : ℕ) where
  rounds : Fin k → RoundMessages A
  a_final : ZMod q
  b_final : ZMod q

def round_messages {k : ℕ} (U : A) (G H : Vec (k + 1) A)
    (a b : Vec (k + 1) (ZMod q)) : RoundMessages A :=
  ⟨multiscalar_mul (split_lo a) (split_hi G) +
      multiscalar_mul (split_hi b) (split_lo H) + dot_product (split_lo a) (split_hi b) • U,
   multiscalar_mul (split_hi a) (split_lo G) +
      multiscalar_mul (split_lo b) (split_hi H) + dot_product (split_hi a) (split_lo b) • U⟩

def fold_vector_a {k : ℕ} (x : (ZMod q)ˣ) (a : Vec (k + 1) (ZMod q)) : Vec k (ZMod q) :=
  fun i => (x : ZMod q) * split_lo a i + (↑x⁻¹ : ZMod q) * split_hi a i

def fold_vector_b {k : ℕ} (x : (ZMod q)ˣ) (b : Vec (k + 1) (ZMod q)) : Vec k (ZMod q) :=
  fun i => (↑x⁻¹ : ZMod q) * split_lo b i + (x : ZMod q) * split_hi b i

def fold_generators_G {k : ℕ} (x : (ZMod q)ˣ) (G : Vec (k + 1) A) : Vec k A :=
  fun i => (↑x⁻¹ : ZMod q) • split_lo G i + (x : ZMod q) • split_hi G i

def fold_generators_H {k : ℕ} (x : (ZMod q)ˣ) (H : Vec (k + 1) A) : Vec k A :=
  fun i => (x : ZMod q) • split_lo H i + (↑x⁻¹ : ZMod q) • split_hi H i

def update_target (x : (ZMod q)ˣ) (msg : RoundMessages A) (P : A) : A :=
  (x : ZMod q)^2 • msg.L + P + (↑x⁻¹ : ZMod q)^2 • msg.R

private theorem coordinate_fold (x : (ZMod q)ˣ) (al ar bl br : ZMod q)
    (gl gr hl hr U : A) :
    ((x : ZMod q) * al + (↑x⁻¹ : ZMod q) * ar) •
        ((↑x⁻¹ : ZMod q) • gl + (x : ZMod q) • gr) +
      ((↑x⁻¹ : ZMod q) * bl + (x : ZMod q) * br) •
        ((x : ZMod q) • hl + (↑x⁻¹ : ZMod q) • hr) +
      (((x : ZMod q) * al + (↑x⁻¹ : ZMod q) * ar) *
        ((↑x⁻¹ : ZMod q) * bl + (x : ZMod q) * br)) • U =
    (x : ZMod q)^2 • (al • gr + br • hl + (al * br) • U) +
      (al • gl + ar • gr + (bl • hl + br • hr) + (al * bl + ar * br) • U) +
      (↑x⁻¹ : ZMod q)^2 • (ar • gl + bl • hr + (ar * bl) • U) := by
  simp only [Units.val_inv_eq_inv_val]
  have hx := Units.ne_zero x
  match_scalars <;> field_simp <;> ring

theorem ipa_round_invariant {k : ℕ} (U : A) (G H : Vec (k + 1) A)
    (a b : Vec (k + 1) (ZMod q)) (x : (ZMod q)ˣ) :
    update_target x (round_messages U G H a b) (ipa_target U G H a b) =
      ipa_target U (fold_generators_G x G) (fold_generators_H x H)
        (fold_vector_a x a) (fold_vector_b x b) := by
  unfold update_target round_messages ipa_target
  simp only [multiscalar_mul, dot_product]
  rw [sum_split (fun i => a i • G i), sum_split (fun i => b i • H i),
    sum_split (fun i => a i * b i)]
  simp only [split_lo, split_hi, add_smul, Finset.sum_smul, smul_add, Finset.smul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [fold_vector_a, fold_vector_b, fold_generators_G, fold_generators_H,
    split_lo, split_hi, smul_add, add_smul] using
    (coordinate_fold x (split_lo a i) (split_hi a i) (split_lo b i)
    (split_hi b i) (split_lo G i) (split_hi G i)
      (split_lo H i) (split_hi H i) U).symm


/-- Executable prover for an externally supplied sequence of nonzero challenges. -/
def prover (U : A) : {k : ℕ} → (G H : Vec k A) → (a b : Vec k (ZMod q)) →
    (Fin k → (ZMod q)ˣ) → IPATranscript q A k
  | 0, _, _, a, b, _ => ⟨Fin.elim0, a 0, b 0⟩
  | _ + 1, G, H, a, b, xs =>
    let msg := round_messages U G H a b
    let t := prover U (fold_generators_G (xs 0) G) (fold_generators_H (xs 0) H)
      (fold_vector_a (xs 0) a) (fold_vector_b (xs 0) b) (Fin.tail xs)
    ⟨Fin.cons msg t.rounds, t.a_final, t.b_final⟩

def transcript_tail {k : ℕ} (t : IPATranscript q A (k + 1)) : IPATranscript q A k :=
  ⟨Fin.tail t.rounds, t.a_final, t.b_final⟩

/-- Only public generators, target, challenges and transcript enter the verifier. -/
def verifier [DecidableEq A] (U : A) : {k : ℕ} → (G H : Vec k A) → A →
    (Fin k → (ZMod q)ˣ) → IPATranscript q A k → Bool
  | 0, G, H, P, _, t => decide (P = t.a_final • G 0 + t.b_final • H 0 +
      (t.a_final * t.b_final) • U)
  | _ + 1, G, H, P, xs, t =>
    verifier U (fold_generators_G (xs 0) G) (fold_generators_H (xs 0) H)
      (update_target (xs 0) (t.rounds 0) P) (Fin.tail xs) (transcript_tail t)

theorem ipa_completeness [DecidableEq A] {k : ℕ} (U : A) (G H : Vec k A)
    (a b : Vec k (ZMod q)) (xs : Fin k → (ZMod q)ˣ) :
    verifier U G H (ipa_target U G H a b) xs (prover U G H a b xs) = true := by
  induction k with
  | zero => simp [verifier, prover, ipa_target, dot_product, multiscalar_mul]
  | succ k ih =>
    simp only [prover, verifier, Fin.cons_zero, transcript_tail, Fin.tail_cons]
    rw [ipa_round_invariant]
    exact ih _ _ _ _ _

/-- The first message is constructed before, and independently of, this round's challenge. -/
theorem prover_first_message {k : ℕ} (U : A) (G H : Vec (k + 1) A)
    (a b : Vec (k + 1) (ZMod q)) (xs : Fin (k + 1) → (ZMod q)ˣ) :
    (prover U G H a b xs).rounds 0 = round_messages U G H a b := rfl

theorem challenge_nonzero (x : (ZMod q)ˣ) : (x : ZMod q) ≠ 0 := Units.ne_zero x

/-- Flattening counts transmitted elements, not group operations or bytes. -/
def group_payload {k : ℕ} (t : IPATranscript q A k) : List A :=
  (List.ofFn t.rounds).flatMap (fun r => [r.L, r.R])

def scalar_payload {k : ℕ} (t : IPATranscript q A k) : List (ZMod q) :=
  [t.a_final, t.b_final]

omit [Fact (Nat.Prime q)] [AddCommGroup A] [Module (ZMod q) A] in
theorem ipa_proof_elements_count {k : ℕ} (t : IPATranscript q A k) :
    (List.ofFn t.rounds).length = k ∧ (group_payload t).length = 2 * k ∧
      (scalar_payload t).length = 2 := by
  simp [group_payload, scalar_payload, List.length_flatMap, List.sum_ofFn, mul_comm]

/-- Join the low and high halves in the original contiguous index order. -/
def join {k : ℕ} {B : Type} (l h : Vec k B) : Vec (k + 1) B :=
  fun i => Fin.append l h (Fin.cast (width_succ k).symm i)

@[simp] theorem split_lo_join {k : ℕ} {B : Type} (l h : Vec k B) :
    split_lo (join l h) = l := by
  funext i
  simp [split_lo, join, loIndex]

@[simp] theorem split_hi_join {k : ℕ} {B : Type} (l h : Vec k B) :
    split_hi (join l h) = h := by
  funext i
  change Fin.append l h (Fin.natAdd (2^k) i) = h i
  exact Fin.append_right l h i

/-- Products of challenge powers, expanded back to the original coordinates. -/
def weights_G : (k : ℕ) → (Fin k → (ZMod q)ˣ) → Vec k (ZMod q)
  | 0, _ => fun _ => 1
  | k + 1, xs =>
    let w := weights_G k (Fin.tail xs)
    join (fun i => w i * (↑(xs 0)⁻¹ : ZMod q)) (fun i => w i * (xs 0 : ZMod q))

def weights_H : (k : ℕ) → (Fin k → (ZMod q)ˣ) → Vec k (ZMod q)
  | 0, _ => fun _ => 1
  | k + 1, xs =>
    let w := weights_H k (Fin.tail xs)
    join (fun i => w i * (xs 0 : ZMod q)) (fun i => w i * (↑(xs 0)⁻¹ : ZMod q))

def final_G : {k : ℕ} → (Fin k → (ZMod q)ˣ) → Vec k A → A
  | 0, _, G => G 0
  | _ + 1, xs, G => final_G (Fin.tail xs) (fold_generators_G (xs 0) G)

def final_H : {k : ℕ} → (Fin k → (ZMod q)ˣ) → Vec k A → A
  | 0, _, H => H 0
  | _ + 1, xs, H => final_H (Fin.tail xs) (fold_generators_H (xs 0) H)

theorem multiscalar_join {k : ℕ} (l h : Vec k (ZMod q)) (G : Vec (k + 1) A) :
    multiscalar_mul (join l h) G =
      multiscalar_mul l (split_lo G) + multiscalar_mul h (split_hi G) := by
  unfold multiscalar_mul
  rw [sum_split]
  simp only [split_lo, split_hi]
  change (∑ i, split_lo (join l h) i • split_lo G i) +
    (∑ i, split_hi (join l h) i • split_hi G i) = _
  rw [split_lo_join, split_hi_join]
  rfl

theorem final_G_expansion {k : ℕ} (xs : Fin k → (ZMod q)ˣ) (G : Vec k A) :
    final_G xs G = multiscalar_mul (weights_G k xs) G := by
  induction k with
  | zero => simp [final_G, weights_G, multiscalar_mul]
  | succ k ih =>
    rw [final_G, ih, weights_G, multiscalar_join]
    simp only [multiscalar_mul, fold_generators_G, smul_add, smul_smul, Finset.sum_add_distrib]

theorem final_H_expansion {k : ℕ} (xs : Fin k → (ZMod q)ˣ) (H : Vec k A) :
    final_H xs H = multiscalar_mul (weights_H k xs) H := by
  induction k with
  | zero => simp [final_H, weights_H, multiscalar_mul]
  | succ k ih =>
    rw [final_H, ih, weights_H, multiscalar_join]
    simp only [multiscalar_mul, fold_generators_H, smul_add, smul_smul, Finset.sum_add_distrib]

/-- Accumulated round corrections, with no witness or recursive group folding. -/
def round_correction {k : ℕ} (xs : Fin k → (ZMod q)ˣ) (t : IPATranscript q A k) : A :=
  ∑ i, ((xs i : ZMod q)^2 • (t.rounds i).L +
    (↑(xs i)⁻¹ : ZMod q)^2 • (t.rounds i).R)

def batch_verifier [DecidableEq A] {k : ℕ} (U : A) (G H : Vec k A) (P : A)
    (xs : Fin k → (ZMod q)ˣ) (t : IPATranscript q A k) : Bool :=
  decide (P + round_correction xs t =
    multiscalar_mul (fun i => t.a_final * weights_G k xs i) G +
    multiscalar_mul (fun i => t.b_final * weights_H k xs i) H +
    (t.a_final * t.b_final) • U)

theorem verifier_expansion [DecidableEq A] {k : ℕ} (U : A) (G H : Vec k A) (P : A)
    (xs : Fin k → (ZMod q)ˣ) (t : IPATranscript q A k) :
    verifier U G H P xs t = decide (P + round_correction xs t =
      t.a_final • final_G xs G + t.b_final • final_H xs H +
        (t.a_final * t.b_final) • U) := by
  induction k generalizing P with
  | zero => simp only [verifier, final_G, final_H, round_correction, Fin.sum_univ_zero, add_zero]
  | succ k ih =>
    rw [verifier, ih]
    simp only [round_correction, Fin.sum_univ_succ, transcript_tail, Fin.tail,
      final_G, final_H, update_target]
    congr 2
    abel

theorem ipa_batch_verification_equivalence [DecidableEq A] {k : ℕ} (U : A)
    (G H : Vec k A) (P : A) (xs : Fin k → (ZMod q)ˣ) (t : IPATranscript q A k) :
    verifier U G H P xs t = batch_verifier U G H P xs t := by
  rw [verifier_expansion, final_G_expansion, final_H_expansion]
  simp [batch_verifier, multiscalar_mul, Finset.smul_sum, smul_smul]


theorem ipa_batch_completeness [DecidableEq A] {k : ℕ} (U : A) (G H : Vec k A)
    (a b : Vec k (ZMod q)) (xs : Fin k → (ZMod q)ˣ) :
    batch_verifier U G H (ipa_target U G H a b) xs (prover U G H a b xs) = true := by
  rw [← ipa_batch_verification_equivalence]
  exact ipa_completeness U G H a b xs

theorem ipa_zero_target {n : ℕ} (U : A) (G H : Fin n → A) :
    ipa_target U G H (0 : Fin n → ZMod q) 0 = 0 := by
  simp [ipa_target, dot_product, multiscalar_mul]

/-- Algebraic properties hold even for dependent generators and thus specialize
without extra assumptions to any cyclic group model supplied by the library. -/
structure VerifiedProperties (q : ℕ) (A : Type) [Fact q.Prime] [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A] : Prop where
  folding : ∀ k (U : A) (G H : Vec (k + 1) A) (a b : Vec (k + 1) (ZMod q))
    (x : (ZMod q)ˣ),
    update_target x (round_messages U G H a b) (ipa_target U G H a b) =
      ipa_target U (fold_generators_G x G) (fold_generators_H x H)
        (fold_vector_a x a) (fold_vector_b x b)
  completeness : ∀ k (U : A) (G H : Vec k A) (a b : Vec k (ZMod q))
    (xs : Fin k → (ZMod q)ˣ),
    verifier U G H (ipa_target U G H a b) xs (prover U G H a b xs) = true
  batch_equivalence : ∀ k (U : A) (G H : Vec k A) (P : A)
    (xs : Fin k → (ZMod q)ˣ) (t : IPATranscript q A k),
    verifier U G H P xs t = batch_verifier U G H P xs t
  message_count : ∀ k (t : IPATranscript q A k),
    (List.ofFn t.rounds).length = k ∧ (group_payload t).length = 2 * k ∧
      (scalar_payload t).length = 2
  challenge_safe : ∀ x : (ZMod q)ˣ, (x : ZMod q) ≠ 0
  first_independent : ∀ k (U : A) (G H : Vec (k + 1) A)
    (a b : Vec (k + 1) (ZMod q)) (xs : Fin (k + 1) → (ZMod q)ˣ),
    (prover U G H a b xs).rounds 0 = round_messages U G H a b

theorem verified_properties [DecidableEq A] : VerifiedProperties q A where
  folding := fun _ => ipa_round_invariant
  completeness := fun _ => ipa_completeness
  batch_equivalence := fun _ => ipa_batch_verification_equivalence
  message_count := fun _ => ipa_proof_elements_count
  challenge_safe := challenge_nonzero
  first_independent := fun _ => prover_first_message

structure CryptoBulletproofsInnerProductSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [AddCommGroup A]
    [Module (ZMod q) A] [DecidableEq A], VerifiedProperties q A
  cyclic_model : ∀ (q : ℕ) [Fact q.Prime],
    Nonempty (CryptoPedersenHomomorphicSum.Setup q (ZMod q))

theorem verification_suite : CryptoBulletproofsInnerProductSuite where
  all_models := fun _ _ _ _ _ _ => verified_properties
  cyclic_model := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoBulletproofsInnerProduct
