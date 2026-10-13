import Verification.CryptoThresholdSchnorrFrostGroup

open CryptoThresholdSchnorrFrostGroup Polynomial
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private noncomputable def S : CryptoShamirSecretSharingGroup.Setup 7 2 3 (ZMod 7) :=
  ConsistencyModel 7 2 3 (by decide) (by decide) (by decide)
private noncomputable def f : Polynomial (ZMod 7) := C 3 + X
private theorem degree_f : f.natDegree < 2 := by unfold f; compute_degree!

-- Deliberately transparent functions: correctness must not assume a secure hash.
private def H : HashContext 7 (ZMod 7) (ZMod 7) where
  binding := fun Y m L i => Y + m + i + (L.map (fun p => p.1 + p.2.1 + p.2.2)).sum
  challenge := fun R Y m => R + Y + m

private noncomputable def pairSession : Session S (ZMod 7) :=
  ⟨{0, 2}, by decide, 4, fun i => (i.val : ZMod 7) + 1, fun _ => 2⟩
private noncomputable def allSession : Session S (ZMod 7) :=
  ⟨Finset.univ, by decide, 4, fun _ => 3, fun i => (i.val : ZMod 7) + 2⟩

-- A real degree-one polynomial, two-of-three, and strictly more than threshold.
example : f.eval 0 = 3 := by simp [f]
example : pairSession.signers.card = 2 ∧ allSession.signers.card = 3 := by decide
example : 2 < allSession.signers.card := by decide
example : z_agg S H f pairSession • S.generator =
    R_agg S H f pairSession + challenge S H f pairSession • publicKey S f :=
  session_aggregate_verification S H f degree_f pairSession
example : z_agg S H f allSession • S.generator =
    R_agg S H f allSession + challenge S H f allSession • publicKey S f :=
  session_aggregate_verification S H f degree_f allSession
example (a b : Session S (ZMod 7)) :
    (z_agg S H f a • S.generator = R_agg S H f a + challenge S H f a • publicKey S f) ∧
    (z_agg S H f b • S.generator = R_agg S H f b + challenge S H f b • publicKey S f) :=
  frost_alternate_coalition_correctness S H f degree_f a b

-- Reversed enumeration leaves the entire transcript and signature unchanged.
example (d e : Fin 3 → ZMod 7) :
    commitmentList S ([0, 2] : List (Fin 3)).toFinset d e =
      commitmentList S ([2, 0] : List (Fin 3)).toFinset d e :=
  (frost_canonical_order_invariance S [0, 2] [2, 0] (List.Perm.swap _ _ []) d e).2
example (xs ys : List (Fin 3)) (hp : xs.Perm ys) (hx : validEnumeration xs)
    (hy : validEnumeration ys) (hxs : 2 ≤ xs.toFinset.card) (hys : 2 ≤ ys.toFinset.card)
    (m : ZMod 7) (d e : Fin 3 → ZMod 7) :
    let a := sessionFromList S xs hx hxs m d e
    let b := sessionFromList S ys hy hys m d e
    bindingFactor S H f a = bindingFactor S H f b ∧ challenge S H f a = challenge S H f b ∧
    R_agg S H f a = R_agg S H f b ∧ z_agg S H f a = z_agg S H f b :=
  canonical_session_invariance S H f xs ys hp hx hy hxs hys m d e
example : ¬validEnumeration ([0, 0, 2] : List (Fin 3)) := duplicate_enumeration_rejected _ _
example : (canonicalOrder S pairSession.signers).Nodup := canonicalOrder_nodup S _
example : (canonicalOrder S pairSession.signers).Pairwise
    (fun i j => (S.coordinates i).val ≤ (S.coordinates j).val) := canonicalOrder_sorted S _

-- One changed scalar fails both equations; two opposite changes preserve the aggregate.
example : (z_agg S H f pairSession + 1) • S.generator ≠
    R_agg S H f pairSession + challenge S H f pairSession • publicKey S f :=
  (frost_single_share_tamper_rejected S H f degree_f pairSession 0 1 (by decide)).2
example :
    (∑ k ∈ pairSession.signers, cancelErrors (z_share S H f pairSession) 0 2 1 k) • S.generator =
      R_agg S H f pairSession + challenge S H f pairSession • publicKey S f ∧
    cancelErrors (z_share S H f pairSession) 0 2 1 0 • S.generator ≠ R_share S H f pairSession 0 +
      (challenge S H f pairSession * CryptoShamirSecretSharingGroup.lagrange_coeff S.coordinates
        pairSession.signers 0) • sharePublic S f 0 ∧
    cancelErrors (z_share S H f pairSession) 0 2 1 2 • S.generator ≠ R_share S H f pairSession 2 +
      (challenge S H f pairSession * CryptoShamirSecretSharingGroup.lagrange_coeff S.coordinates
        pairSession.signers 2) • sharePublic S f 2 :=
  session_error_cancellation S H f degree_f pairSession (by decide) (by decide) (by decide) 1 (by decide)

-- t=1 genuinely reduces the scalar response to Schnorr with a combined nonce.
example (s d e ρ c : ZMod 7) :
    response d e ρ c (CryptoShamirSecretSharingGroup.lagrange_coeff
      (fun _ : Fin 1 => (1 : ZMod 7)) {0} 0) ((C s).eval 1) = d + ρ * e + c * (C s).eval 0 :=
  frost_reduction_to_schnorr_t1 (fun _ : Fin 1 => (1 : ZMod 7)) (C s)
    (by simp) 0 d e ρ c
example (d e ρ : Fin 3 → ZMod 7) (c : ZMod 7) :
    (∑ i, response (d i) (e i) (ρ i) c (CryptoShamirSecretSharingGroup.lagrange_coeff
      S.coordinates Finset.univ i) (f.eval (S.coordinates i))) • S.generator =
      (∑ i, nonceShare S.generator (d i) (e i) (ρ i)) + c • (f.eval 0 • S.generator) :=
  frost_threshold_all S.generator S.coordinates S.coordinates_injective f
    (lt_trans degree_f (by decide)) d e ρ c

example : CryptoThresholdSchnorrFrostGroupSuite := crypto_threshold_schnorr_frost_group_master_suite
#print axioms crypto_threshold_schnorr_frost_group_master_suite
#print axioms canonical_session_invariance
#print axioms session_error_cancellation
