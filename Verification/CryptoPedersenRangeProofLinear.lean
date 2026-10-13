/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.CryptoCommitmentVectorPedersenGroup
import Verification.CryptoSchnorrIdentification
import Mathlib.Data.Fin.VecNotation

/-!
# Linear interactive Pedersen range proofs

Binary OR proofs use a common verifier challenge. Extraction produces a range
opening, not unconditional equality with a previously supplied opening. The
probabilistic contract is special honest-verifier zero knowledge, not Fiat-Shamir
security or security against malicious verifiers.
-/
namespace CryptoPedersenRangeProofLinear

open scoped BigOperators

/-- Little-endian natural value; arithmetic here is not modular. -/
def bitValue {m : ℕ} (b : Fin m → ℕ) : ℕ := ∑ i, 2 ^ i.val * b i

theorem bitValue_cons {m : ℕ} (a : ℕ) (b : Fin m → ℕ) :
    bitValue (Fin.cons a b) = a + 2 * bitValue b := by
  simp only [bitValue, Fin.sum_univ_succ, Fin.cons_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.cons_succ, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem bitValue_lt {m : ℕ} (b : Fin m → ℕ) (hb : ∀ i, b i ≤ 1) :
    bitValue b < 2 ^ m := by
  induction m with
  | zero => simp [bitValue]
  | succ m ih =>
    have h := ih (fun i => b i.succ) (fun i => hb i.succ)
    have hh := hb 0
    have he : b = Fin.cons (b 0) (fun i => b i.succ) := by
      funext i; exact (Fin.cases rfl (fun _ => rfl) i)
    rw [he, bitValue_cons, pow_succ]
    omega

theorem nat_bit_decomp_iff (m v : ℕ) :
    v < 2 ^ m ↔ ∃ b : Fin m → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = v := by
  constructor
  · intro hv
    induction m generalizing v with
    | zero =>
      have : v = 0 := by simpa using hv
      subst v
      exact ⟨Fin.elim0, fun i => Fin.elim0 i, by simp [bitValue]⟩
    | succ m ih =>
      have hd : v / 2 < 2 ^ m := by
        apply (Nat.div_lt_iff_lt_mul (by omega : 0 < 2)).mpr
        simpa [pow_succ] using hv
      obtain ⟨b, hb, he⟩ := ih (v / 2) hd
      refine ⟨Fin.cons (v % 2) b, ?_, ?_⟩
      · intro i; refine Fin.cases ?_ (fun j => hb j) i
        simp only [Fin.cons_zero]; omega
      · rw [bitValue_cons, he]; omega
  · rintro ⟨b, hb, rfl⟩; exact bitValue_lt b hb

variable {q : ℕ} [Fact q.Prime]
variable {A : Type} [Fintype A] [AddCommGroup A] [Module (ZMod q) A]
abbrev Setup := CryptoPedersenHomomorphicSum.Setup
abbrev commit (S : Setup q A) (v r : ZMod q) : A :=
  CryptoPedersenHomomorphicSum.commit S v r

def weight (i : ℕ) : ZMod q := (2 : ZMod q) ^ i

theorem bitValue_cast {m : ℕ} (b : Fin m → ℕ) :
    (bitValue b : ZMod q) = ∑ i, weight i.val * (b i : ZMod q) := by
  simp [bitValue, weight, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]

def aggregate {m : ℕ} (C : Fin m → A) : A := ∑ i, (weight i.val : ZMod q) • C i

def blindSum {m : ℕ} (r : Fin m → ZMod q) : ZMod q := ∑ i, weight i.val * r i

theorem aggregate_commit {m : ℕ} (S : Setup q A) (b : Fin m → ℕ)
    (r : Fin m → ZMod q) :
    aggregate (q := q) (fun i => commit S (b i) (r i)) = commit S (bitValue b) (blindSum r) := by
  rw [bitValue_cast]
  simp [aggregate, blindSum, commit, CryptoPedersenHomomorphicSum.commit,
    smul_add, mul_smul, Finset.sum_add_distrib, Finset.sum_smul]

/-- Each branch carries its own challenge and response. -/
structure ORTranscript (q : ℕ) (A : Type) where
  a0 : A
  a1 : A
  e0 : ZMod q
  e1 : ZMod q
  z0 : ZMod q
  z1 : ZMod q
  deriving DecidableEq

def ORVerify (S : Setup q A) (C : A) (e : ZMod q) (t : ORTranscript q A) : Prop :=
  t.e0 + t.e1 = e ∧ t.z0 • S.h = t.a0 + t.e0 • C ∧
    t.z1 • S.h = t.a1 + t.e1 • (C - S.g)

abbrev Coins (q : ℕ) := ZMod q × ZMod q × ZMod q

/-- Public simulator coins are (first branch challenge, first response, second response). -/
def orSim (S : Setup q A) (C : A) (e : ZMod q) (u : Coins q) : ORTranscript q A :=
  ⟨u.2.1 • S.h - u.1 • C, u.2.2 • S.h - (e - u.1) • (C - S.g),
    u.1, e - u.1, u.2.1, u.2.2⟩

theorem orSim_valid (S : Setup q A) (C : A) (e : ZMod q) (u : Coins q) :
    ORVerify S C e (orSim S C e u) := by simp [ORVerify, orSim]

/-- Real coins: false-branch challenge, true-branch nonce, false-branch response. -/
def responseEquiv (b : Bool) (r e : ZMod q) : Coins q ≃ Coins q :=
  if b then
    { toFun := fun u => (u.1, u.2.2, u.2.1 + (e - u.1) * r)
      invFun := fun u => (u.1, u.2.2 - (e - u.1) * r, u.2.1)
      left_inv := by intro u; simp
      right_inv := by intro u; simp }
  else
    { toFun := fun u => (e - u.1, u.2.1 + (e - u.1) * r, u.2.2)
      invFun := fun u => (e - u.1, u.2.1 - u.1 * r, u.2.2)
      left_inv := by intro u; simp
      right_inv := by intro u; simp }

def orHonest (S : Setup q A) (b : Bool) (r e : ZMod q) (u : Coins q) : ORTranscript q A :=
  orSim S (commit S b.toNat r) e (responseEquiv b r e u)

theorem or_completeness (S : Setup q A) (b : Bool) (r e : ZMod q) (u : Coins q) :
    ORVerify S (commit S b.toNat r) e (orHonest S b r e u) := orSim_valid _ _ _ _

/-- First messages are generated before the verifier's challenge. -/
theorem or_first_message_independent (S : Setup q A) (b : Bool) (r e e' : ZMod q)
    (u : Coins q) :
    (orHonest S b r e u).a0 = (orHonest S b r e' u).a0 ∧
    (orHonest S b r e u).a1 = (orHonest S b r e' u).a1 := by
  cases b <;> simp [orHonest, orSim, responseEquiv, commit,
    CryptoPedersenHomomorphicSum.commit, add_smul, mul_smul]

/-- Reuse Schnorr extraction with the Pedersen blinding generator. -/
def blindSetup (S : Setup q A) : Setup q A :=
  ⟨S.card_eq, S.h, S.g, S.h_ne_zero, S.g_ne_zero⟩

def extractBit (t t' : ORTranscript q A) : Bool × ZMod q :=
  if t.e0 = t'.e0 then
    (true, CryptoSchnorrIdentification.extractWitness t.e1 t'.e1 t.z1 t'.z1)
  else
    (false, CryptoSchnorrIdentification.extractWitness t.e0 t'.e0 t.z0 t'.z0)

theorem or_special_soundness (S : Setup q A) (C : A) (e e' : ZMod q)
    (t t' : ORTranscript q A) (h0 : t.a0 = t'.a0) (h1 : t.a1 = t'.a1)
    (he : e ≠ e') (ht : ORVerify S C e t) (ht' : ORVerify S C e' t') :
    C = commit S (extractBit t t').1.toNat (extractBit t t').2 := by
  rcases ht with ⟨hs, hz0, hz1⟩
  rcases ht' with ⟨hs', hz0', hz1'⟩
  by_cases h : t.e0 = t'.e0
  · have hne : t.e1 ≠ t'.e1 := by intro hh; apply he; rw [← hs, ← hs', h, hh]
    have hx := (CryptoSchnorrIdentification.schnorr_special_soundness (blindSetup S)
      (C - S.g) t.a1 t.e1 t'.e1 t.z1 t'.z1 hne hz1
        (by simpa [CryptoSchnorrIdentification.Verify, blindSetup, ← h1] using hz1')).2
    simpa [extractBit, h, commit, CryptoPedersenHomomorphicSum.commit,
      blindSetup, sub_eq_iff_eq_add, add_comm] using hx
  · have hx := (CryptoSchnorrIdentification.schnorr_special_soundness (blindSetup S)
      C t.a0 t.e0 t'.e0 t.z0 t'.z0 h hz0
        (by simpa [CryptoSchnorrIdentification.Verify, blindSetup, ← h0] using hz0')).2
    simpa [extractBit, h, commit, CryptoPedersenHomomorphicSum.commit, blindSetup] using hx

noncomputable def orRealLaw (S : Setup q A) (b : Bool) (r e : ZMod q) : PMF (ORTranscript q A) :=
  (PMF.uniformOfFintype (Coins q)).map (orHonest S b r e)

noncomputable def orSimLaw (S : Setup q A) (C : A) (e : ZMod q) : PMF (ORTranscript q A) :=
  (PMF.uniformOfFintype (Coins q)).map (orSim S C e)

theorem or_hvzk (S : Setup q A) (b : Bool) (r e : ZMod q) :
    orRealLaw S b r e = orSimLaw S (commit S b.toNat r) e := by
  have h := CryptoPedersenHomomorphicSum.map_uniform_equiv (responseEquiv b r e)
  unfold orSimLaw
  rw [← h, PMF.map_comp]
  rfl


structure RangeProofTranscript (q m : ℕ) (A : Type) where
  commitments : Fin m → A
  challenge : ZMod q
  proofs : Fin m → ORTranscript q A

def verify_range_proof {m : ℕ} (S : Setup q A) (C : A)
    (t : RangeProofTranscript q m A) : Prop :=
  aggregate (q := q) t.commitments = C ∧
    ∀ i, ORVerify S (t.commitments i) t.challenge (t.proofs i)

/-- Includes all prover messages sent before the common challenge. -/
def SameFirst {m : ℕ} (t t' : RangeProofTranscript q m A) : Prop :=
  t.commitments = t'.commitments ∧ ∀ i,
    (t.proofs i).a0 = (t'.proofs i).a0 ∧ (t.proofs i).a1 = (t'.proofs i).a1

def rangeHonest {m : ℕ} (S : Setup q A) (b : Fin m → Bool)
    (r : Fin m → ZMod q) (e : ZMod q) (u : Fin m → Coins q) : RangeProofTranscript q m A :=
  ⟨fun i => commit S (b i).toNat (r i), e, fun i => orHonest S (b i) (r i) e (u i)⟩

theorem range_proof_completeness {m : ℕ} (S : Setup q A) (b : Fin m → Bool)
    (r : Fin m → ZMod q) (e : ZMod q) (u : Fin m → Coins q) :
    verify_range_proof S (commit S (bitValue (fun i => (b i).toNat)) (blindSum r))
      (rangeHonest S b r e u) :=
  ⟨aggregate_commit S _ _, fun _i => or_completeness S _ _ _ _⟩

theorem range_first_message_independent {m : ℕ} (S : Setup q A) (b : Fin m → Bool)
    (r : Fin m → ZMod q) (e e' : ZMod q) (u : Fin m → Coins q) :
    SameFirst (rangeHonest S b r e u) (rangeHonest S b r e' u) :=
  ⟨rfl, fun _i => or_first_message_independent S _ _ _ _ _⟩

def extractedBits {m : ℕ} (t t' : RangeProofTranscript q m A) : Fin m → ℕ :=
  fun i => (extractBit (t.proofs i) (t'.proofs i)).1.toNat

def extractedBlinds {m : ℕ} (t t' : RangeProofTranscript q m A) : Fin m → ZMod q :=
  fun i => (extractBit (t.proofs i) (t'.proofs i)).2

def extract_range_witness {m : ℕ} (t t' : RangeProofTranscript q m A) : ℕ × ZMod q :=
  (bitValue (extractedBits t t'), blindSum (extractedBlinds t t'))

theorem range_proof_extract_witness {m : ℕ} (S : Setup q A) (C : A)
    (t t' : RangeProofTranscript q m A) (hfirst : SameFirst t t')
    (he : t.challenge ≠ t'.challenge)
    (ht : verify_range_proof S C t) (ht' : verify_range_proof S C t') :
    (extract_range_witness t t').1 < 2 ^ m ∧
    C = commit S (extract_range_witness t t').1 (extract_range_witness t t').2 := by
  have hb : ∀ i, extractedBits t t' i ≤ 1 := by
    intro i; exact Bool.toNat_le _
  refine ⟨bitValue_lt _ hb, ?_⟩
  have hc : t.commitments = fun i => commit S (extractedBits t t' i) (extractedBlinds t t' i) := by
    funext i
    exact or_special_soundness S _ _ _ _ _ (hfirst.2 i).1 (hfirst.2 i).2 he
      (ht.2 i) (by simpa [← hfirst.1] using ht'.2 i)
  rw [← ht.1, hc, aggregate_commit]
  rfl

theorem pedersen_binding_violation_extracts_dlog (S : Setup q A)
    (v r v' r' : ZMod q) (hc : commit S v r = commit S v' r') (hv : v ≠ v') :
    S.g = ((r' - r) * (v - v')⁻¹) • S.h := by
  have he : (v - v') • S.g = (r' - r) • S.h := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
    simpa [commit, CryptoPedersenHomomorphicSum.commit, add_comm] using hc
  have hi := congrArg (fun x : A => (v - v')⁻¹ • x) he
  simpa [smul_smul, sub_ne_zero.mpr hv, mul_comm] using hi

/-- Natural range values embed injectively; this does not imply binding of commitments. -/
theorem range_cast_injective {m v w : ℕ} (hq : 2 ^ m < q)
    (hv : v < 2 ^ m) (hw : w < 2 ^ m) (he : (v : ZMod q) = (w : ZMod q)) : v = w := by
  have h := congrArg ZMod.val he
  simpa [ZMod.val_natCast, Nat.mod_eq_of_lt (lt_trans hv hq),
    Nat.mod_eq_of_lt (lt_trans hw hq)] using h


/-- Fixed weighted blinding, including the dependency between bit commitments. -/
abbrev OpeningFiber (q m : ℕ) [Fact q.Prime] (r : ZMod q) :=
  { rs : Fin m → ZMod q // blindSum rs = r }

abbrev CommitmentFiber (q m : ℕ) [Fact q.Prime] (A : Type)
    [AddCommGroup A] [Module (ZMod q) A] (C : A) :=
  { cs : Fin m → A // aggregate (q := q) cs = C }

noncomputable instance {m : ℕ} (r : ZMod q) : Fintype (OpeningFiber q m r) :=
  Fintype.ofFinite _
noncomputable instance {m : ℕ} (C : A) : Fintype (CommitmentFiber q m A C) :=
  Fintype.ofFinite _

instance {n : ℕ} (r : ZMod q) : Nonempty (OpeningFiber q (n + 1) r) :=
  ⟨⟨Fin.cons r (fun _ => 0), by simp [blindSum, Fin.sum_univ_succ, weight]⟩⟩
instance {n : ℕ} (C : A) : Nonempty (CommitmentFiber q (n + 1) A C) :=
  ⟨⟨Fin.cons C (fun _ => 0), by simp [aggregate, Fin.sum_univ_succ, weight]⟩⟩

/-- Only used in the distribution proof; the simulator does not use this inverse. -/
noncomputable def fiberEquiv {m : ℕ} (S : Setup q A) (b : Fin m → Bool) (r : ZMod q) :
    OpeningFiber q m r ≃
      CommitmentFiber q m A (commit S (bitValue (fun i => (b i).toNat)) r) where
  toFun rs := ⟨fun i => commit S (b i).toNat (rs.val i), by
    rw [aggregate_commit, rs.property]⟩
  invFun cs := ⟨fun i =>
    (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).symm (cs.val i), by
    apply (CryptoPedersenHomomorphicSum.commit_bijective S
      (bitValue (fun i => (b i).toNat))).1
    change commit S (bitValue (fun i => (b i).toNat))
      (blindSum (fun i =>
        (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).symm (cs.val i))) =
      commit S (bitValue (fun i => (b i).toNat)) r
    rw [← aggregate_commit S (fun i => (b i).toNat)
      (fun i => (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).symm (cs.val i))]
    convert cs.property using 1
    congr 1
    funext i
    exact (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).apply_symm_apply _⟩
  left_inv rs := by
    apply Subtype.ext
    funext i
    exact (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).symm_apply_apply _
  right_inv cs := by
    apply Subtype.ext
    funext i
    exact (CryptoPedersenHomomorphicSum.commitEquiv S (b i).toNat).apply_symm_apply _

noncomputable def vectorResponseEquiv {m : ℕ} (b : Fin m → Bool)
    (r : Fin m → ZMod q) (e : ZMod q) :
    (Fin m → Coins q) ≃ (Fin m → Coins q) :=
  Equiv.piCongrRight (fun i => responseEquiv (b i) (r i) e)

def rangeSim {m : ℕ} (S : Setup q A) (cs : Fin m → A) (e : ZMod q)
    (u : Fin m → Coins q) : RangeProofTranscript q m A :=
  ⟨cs, e, fun i => orSim S (cs i) e (u i)⟩

theorem rangeSim_valid {m : ℕ} (S : Setup q A) (C : A)
    (cs : CommitmentFiber q m A C) (e : ZMod q) (u : Fin m → Coins q) :
    verify_range_proof S C (rangeSim S cs.val e u) :=
  ⟨cs.property, fun i => orSim_valid S (cs.val i) e (u i)⟩

noncomputable def conditionalRealLaw {m : ℕ} (S : Setup q A) (b : Fin m → Bool)
    (rs : Fin m → ZMod q) (e : ZMod q) : PMF (RangeProofTranscript q m A) :=
  (PMF.uniformOfFintype (Fin m → Coins q)).map (rangeHonest S b rs e)

noncomputable def conditionalSimLaw {m : ℕ} (S : Setup q A) (cs : Fin m → A)
    (e : ZMod q) : PMF (RangeProofTranscript q m A) :=
  (PMF.uniformOfFintype (Fin m → Coins q)).map (rangeSim S cs e)

theorem conditional_hvzk {m : ℕ} (S : Setup q A) (b : Fin m → Bool)
    (rs : Fin m → ZMod q) (e : ZMod q) :
    conditionalRealLaw S b rs e =
      conditionalSimLaw S (fun i => commit S (b i).toNat (rs i)) e := by
  have h := CryptoPedersenHomomorphicSum.map_uniform_equiv (vectorResponseEquiv b rs e)
  unfold conditionalSimLaw
  rw [← h, PMF.map_comp]
  rfl

/-- Distribution for a fixed opening of C; bit blindings are sampled jointly. -/
noncomputable def rangeRealLaw {n : ℕ} (S : Setup q A) (b : Fin (n + 1) → Bool)
    (r e : ZMod q) : PMF (RangeProofTranscript q (n + 1) A) :=
  (PMF.uniformOfFintype (OpeningFiber q (n + 1) r)).bind
    (fun rs => conditionalRealLaw S b rs.val e)

/-- Public-input-only simulator: uniformly sample the affine commitment fiber,
then all OR responses. No bit, opening or discrete logarithm is an input. -/
noncomputable def rangeSimLaw {n : ℕ} (S : Setup q A) (C : A)
    (e : ZMod q) : PMF (RangeProofTranscript q (n + 1) A) :=
  (PMF.uniformOfFintype (CommitmentFiber q (n + 1) A C)).bind
    (fun cs => conditionalSimLaw S cs.val e)

/-- Equality of full joint transcript PMFs, including correlated bit commitments. -/
theorem range_proof_hvzk_sim_eq_dist {n : ℕ} (S : Setup q A)
    (b : Fin (n + 1) → Bool) (r e : ZMod q) :
    rangeRealLaw S b r e =
      rangeSimLaw S (commit S (bitValue (fun i => (b i).toNat)) r) e := by
  have h := CryptoPedersenHomomorphicSum.map_uniform_equiv (fiberEquiv S b r)
  unfold rangeSimLaw
  rw [← h, PMF.bind_map]
  unfold rangeRealLaw
  congr 1
  funext rs
  exact conditional_hvzk S b rs.val e


/-- Sampling n free commitments and solving the coefficient-one coordinate
implements the public affine-fiber distribution without computing a logarithm. -/
def commitmentTailEquiv {n : ℕ} (C : A) :
    (Fin n → A) ≃ CommitmentFiber q (n + 1) A C where
  toFun xs := ⟨Fin.cons (C - ∑ i, (weight i.succ.val : ZMod q) • xs i) xs, by
    simp [aggregate, Fin.sum_univ_succ, weight]⟩
  invFun cs := fun i => cs.val i.succ
  left_inv _ := rfl
  right_inv cs := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h := cs.property
    simp only [aggregate, Fin.sum_univ_succ, weight, Fin.val_zero, pow_zero, one_smul] at h
    simpa only [Fin.cons_zero, weight] using (eq_sub_iff_add_eq.mpr h).symm

def openingTailEquiv {n : ℕ} (r : ZMod q) :
    (Fin n → ZMod q) ≃ OpeningFiber q (n + 1) r where
  toFun xs := ⟨Fin.cons (r - ∑ i, weight i.succ.val * xs i) xs, by
    simp [blindSum, Fin.sum_univ_succ, weight]⟩
  invFun rs := fun i => rs.val i.succ
  left_inv _ := rfl
  right_inv rs := by
    apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun _ => rfl) i
    have h := rs.property
    simp only [blindSum, Fin.sum_univ_succ, weight, Fin.val_zero, pow_zero, one_mul] at h
    simpa only [Fin.cons_zero, weight] using (eq_sub_iff_add_eq.mpr h).symm

theorem opening_tail_sampling {n : ℕ} (r : ZMod q) :
    (PMF.uniformOfFintype (Fin n → ZMod q)).map (openingTailEquiv r) =
      PMF.uniformOfFintype (OpeningFiber q (n + 1) r) :=
  CryptoPedersenHomomorphicSum.map_uniform_equiv _

theorem commitment_tail_sampling {n : ℕ} (C : A) :
    (PMF.uniformOfFintype (Fin n → A)).map (commitmentTailEquiv (q := q) C) =
      PMF.uniformOfFintype (CommitmentFiber q (n + 1) A C) :=
  CryptoPedersenHomomorphicSum.map_uniform_equiv _

/-- Simulator with n independent group samples rather than an abstract constrained sampler. -/
noncomputable def rangePublicSimulator {n : ℕ} (S : Setup q A) (C : A) (e : ZMod q) :
    PMF (RangeProofTranscript q (n + 1) A) :=
  (PMF.uniformOfFintype (Fin n → A)).bind
    (fun xs => conditionalSimLaw S (commitmentTailEquiv (q := q) C xs).val e)

theorem public_simulator_eq {n : ℕ} (S : Setup q A) (C : A) (e : ZMod q) :
    rangePublicSimulator (n := n) S C e = rangeSimLaw S C e := by
  unfold rangeSimLaw
  rw [← commitment_tail_sampling C, PMF.bind_map]
  rfl

/-- Real interaction samples openings and nonces before an independent challenge. -/
noncomputable def rangeInteractionLaw {n : ℕ} (S : Setup q A) (b : Fin (n + 1) → Bool)
    (r : ZMod q) (ν : PMF (ZMod q)) : PMF (RangeProofTranscript q (n + 1) A) :=
  (PMF.uniformOfFintype (OpeningFiber q (n + 1) r)).bind fun rs =>
    (PMF.uniformOfFintype (Fin (n + 1) → Coins q)).bind fun u =>
      ν.map (fun e => rangeHonest S b rs.val e u)

theorem range_hvzk_independent_challenge {n : ℕ} (S : Setup q A)
    (b : Fin (n + 1) → Bool) (r : ZMod q) (ν : PMF (ZMod q)) :
    rangeInteractionLaw S b r ν =
      ν.bind (rangePublicSimulator S (commit S (bitValue (fun i => (b i).toNat)) r)) := by
  have horder : rangeInteractionLaw S b r ν = ν.bind (rangeRealLaw S b r) := by
    unfold rangeInteractionLaw rangeRealLaw conditionalRealLaw
    simp only [PMF.map]
    simp_rw [PMF.bind_comm (PMF.uniformOfFintype (Fin (n + 1) → Coins q)) ν]
    exact PMF.bind_comm _ _ _
  rw [horder]
  congr 1
  funext e
  rw [public_simulator_eq]
  exact range_proof_hvzk_sim_eq_dist S b r e

theorem nat_bool_decomp_iff (m v : ℕ) :
    v < 2 ^ m ↔ ∃ b : Fin m → Bool, bitValue (fun i => (b i).toNat) = v := by
  rw [nat_bit_decomp_iff]
  constructor
  · rintro ⟨b, hb, he⟩
    refine ⟨fun i => decide (b i = 1), ?_⟩
    have hv : (fun i => (decide (b i = 1)).toNat) = b := by
      funext i
      have h := hb i
      by_cases hi : b i = 1
      · simp [hi]
      · have hz : b i = 0 := by omega
        simp [hz]
    simpa [hv] using he
  · rintro ⟨b, he⟩
    exact ⟨fun i => (b i).toNat, fun i => Bool.toNat_le _, he⟩

/-- Completeness for every natural range value and every blinding of the original commitment. -/
theorem range_completeness_for_opening {n : ℕ} (S : Setup q A) (v : ℕ)
    (hv : v < 2 ^ (n + 1)) (r e : ZMod q) (u : Fin (n + 1) → Coins q) :
    ∃ t : RangeProofTranscript q (n + 1) A,
      t.challenge = e ∧ verify_range_proof S (commit S v r) t := by
  obtain ⟨b, hb⟩ := (nat_bool_decomp_iff _ _).mp hv
  let rs := openingTailEquiv (n := n) r (fun _ => 0)
  refine ⟨rangeHonest S b rs.val e u, rfl, ?_⟩
  have h := range_proof_completeness S b rs.val e u
  simpa [hb, rs.property] using h

theorem upper_endpoint_no_decomposition (m : ℕ) :
    ¬ ∃ b : Fin m → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = 2 ^ m := by
  rw [← nat_bit_decomp_iff]; exact lt_irrefl _

theorem broken_aggregate_rejected {m : ℕ} (S : Setup q A) (C : A)
    (t : RangeProofTranscript q m A) (h : aggregate (q := q) t.commitments ≠ C) :
    ¬ verify_range_proof S C t := fun hv => h hv.1

/-- Identical zero-challenge transcripts have extractor output zero, which need
not be a witness. This refutes the extraction formula without distinct challenges,
not the existence of some opening in a perfectly hiding commitment scheme. -/
theorem same_challenge_extractor_failure (S : Setup q A) :
    let t := orSim S 0 0 (0, 0, 0)
    ORVerify S 0 0 t ∧
      (0 : A) ≠ commit S (extractBit t t).1.toNat (extractBit t t).2 := by
  dsimp
  refine ⟨orSim_valid _ _ _ _, ?_⟩
  simpa [extractBit, orSim, CryptoSchnorrIdentification.extractWitness,
    commit, CryptoPedersenHomomorphicSum.commit] using S.g_ne_zero.symm

/-- Known relation gives alternate openings, without any independence axiom. -/
theorem known_relation_alternate_opening (S : Setup q A) (x v r v' : ZMod q)
    (hx : S.g = x • S.h) :
    commit S v r = commit S v' (r + (v - v') * x) := by
  simp only [commit, CryptoPedersenHomomorphicSum.commit, hx, smul_smul, ← add_smul]
  congr 1
  ring


instance [DecidableEq A] (S : Setup q A) (C : A) (e : ZMod q) (t : ORTranscript q A) :
    Decidable (ORVerify S C e t) := by unfold ORVerify; infer_instance
instance [DecidableEq A] {m : ℕ} (S : Setup q A) (C : A) (t : RangeProofTranscript q m A) :
    Decidable (verify_range_proof S C t) := by unfold verify_range_proof; infer_instance

/-- The scalar commitment is the one-coordinate vector commitment already in the library. -/
theorem bridge_to_vector_pedersen (S : Setup q A) (v r : ZMod q) :
    commit S v r = CryptoCommitmentVectorPedersenGroup.commit_vec
      (fun _ : Fin 1 => S.g) S.h (fun _ => v) r := by
  simp [commit, CryptoPedersenHomomorphicSum.commit,
    CryptoCommitmentVectorPedersenGroup.commit_vec]

structure VerifiedProperties (S : Setup q A) : Prop where
  completeness : ∀ (n v : ℕ), v < 2 ^ (n + 1) → ∀ (r e : ZMod q) (_u : Fin (n + 1) → Coins q),
    ∃ t : RangeProofTranscript q (n + 1) A,
      t.challenge = e ∧ verify_range_proof S (commit S v r) t
  extraction : ∀ (m : ℕ) (C : A) (t t' : RangeProofTranscript q m A), SameFirst t t' →
    t.challenge ≠ t'.challenge → verify_range_proof S C t → verify_range_proof S C t' →
    (extract_range_witness t t').1 < 2 ^ m ∧
      C = commit S (extract_range_witness t t').1 (extract_range_witness t t').2
  hvzk : ∀ (n : ℕ) (b : Fin (n + 1) → Bool) (r e : ZMod q),
    rangeRealLaw S b r e = rangeSimLaw S (commit S (bitValue (fun i => (b i).toNat)) r) e
  interaction_hvzk : ∀ (n : ℕ) (b : Fin (n + 1) → Bool) (r : ZMod q) (ν : PMF (ZMod q)),
    rangeInteractionLaw S b r ν =
      ν.bind (rangePublicSimulator S (commit S (bitValue (fun i => (b i).toNat)) r))
  first_independent : ∀ (m : ℕ) (b : Fin m → Bool) (rs : Fin m → ZMod q)
    (e e' : ZMod q) (u : Fin m → Coins q),
    SameFirst (rangeHonest S b rs e u) (rangeHonest S b rs e' u)
  collision : ∀ (v r v' r' : ZMod q), commit S v r = commit S v' r' → v ≠ v' →
    S.g = ((r' - r) * (v - v')⁻¹) • S.h
  simulator_accepts : ∀ (m : ℕ) (C : A) (cs : CommitmentFiber q m A C)
    (e : ZMod q) (u : Fin m → Coins q), verify_range_proof S C (rangeSim S cs.val e u)

theorem verified_properties (S : Setup q A) : VerifiedProperties S where
  completeness := fun _ v hv r e u => range_completeness_for_opening S v hv r e u
  extraction := fun _ _ _ _ => range_proof_extract_witness S _ _ _
  hvzk := fun _ _ _ _ => range_proof_hvzk_sim_eq_dist S _ _ _
  interaction_hvzk := fun _ _ _ _ => range_hvzk_independent_challenge S _ _ _
  first_independent := fun _ _ _ _ _ _ => range_first_message_independent S _ _ _ _ _
  collision := pedersen_binding_violation_extracts_dlog S
  simulator_accepts := fun _ _ _ _ _ => rangeSim_valid S _ _ _ _

structure CryptoPedersenRangeProofLinearSuite : Prop where
  bit_range : ∀ m v, v < 2 ^ m ↔
    ∃ b : Fin m → ℕ, (∀ i, b i ≤ 1) ∧ bitValue b = v
  all_models : ∀ (q : ℕ) [Fact q.Prime] (A : Type) [Fintype A] [AddCommGroup A]
    [Module (ZMod q) A] (S : Setup q A), VerifiedProperties S
  cast_range : ∀ (q : ℕ) [Fact q.Prime] (m v w : ℕ), 2 ^ m < q →
    v < 2 ^ m → w < 2 ^ m → (v : ZMod q) = (w : ZMod q) → v = w
  satisfiable : ∀ (q : ℕ) [Fact q.Prime], Nonempty (Setup q (ZMod q))

theorem verification_suite : CryptoPedersenRangeProofLinearSuite where
  bit_range := nat_bit_decomp_iff
  all_models := fun _ _ _ _ _ _ S => verified_properties S
  cast_range := fun _ _ _ _ _ => range_cast_injective
  satisfiable := CryptoPedersenHomomorphicSum.setup_satisfiable

end CryptoPedersenRangeProofLinear
