import Verification.CryptoShamirSecretSharingGroup

open CryptoShamirSecretSharingGroup Polynomial
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (0 < 3) := ⟨by decide⟩
instance : Fact (0 < 1) := ⟨by decide⟩

private noncomputable def S : Setup 7 3 4 (ZMod 7) := ConsistencyModel 7 3 4 (by decide) (by decide) (by decide)
private noncomputable def ξ : Fin 4 → ZMod 7 := S.coordinates
private noncomputable def p : ShamirPoly (ZMod 7) 3 3 :=
  ⟨C 3 + C 2 * X + C 4 * X ^ 2, by compute_degree!, by simp⟩

-- A genuine 3-of-4 instance uses several different interpolation subsets.
example : Nonempty (Setup 7 3 4 (ZMod 7)) := ⟨S⟩
example : GroupProperties S := group_properties S
example : p.val.eval (ξ 0) = 2 ∧ p.val.eval (ξ 1) = 2 ∧ p.val.eval (ξ 2) = 3 := by
  norm_num [p, ξ, S, ConsistencyModel]
  decide
example (I : Finset (Fin 4)) (hI : I.card = 3) :
    ∑ i ∈ I, lagrange_coeff ξ I i * p.val.eval (ξ i) = 3 :=
  shamir_threshold_reconstruction ξ S.coordinates_injective I hI p
example : ∑ i ∈ ({0, 2, 3} : Finset (Fin 4)), lagrange_coeff ξ {0, 2, 3} i * p.val.eval (ξ i) = 3 :=
  shamir_threshold_reconstruction ξ S.coordinates_injective _ (by decide) p
example (I : Finset (Fin 4)) (hI : I.card = 3) :
    ∑ i ∈ I, lagrange_coeff ξ I i • (p.val.eval (ξ i) • (1 : ZMod 7)) = 3 • (1 : ZMod 7) :=
  shamir_group_reconstruction 1 ξ S.coordinates_injective I hI p

-- The distribution is joint across a two-member coalition, for all secret values.
example (s s' : ZMod 7) : observationLaw (t := 3) ξ {0, 2} s = observationLaw (t := 3) ξ {0, 2} s' :=
  shamir_pmf_perfect_secrecy ξ S.coordinates_nonzero _ (by decide) s s'
example (s s' : ZMod 7) : observationLaw (t := 1) ξ ∅ s = observationLaw (t := 1) ξ ∅ s' :=
  shamir_pmf_perfect_secrecy ξ S.coordinates_nonzero _ (by decide) s s'
example : (coalitionPoly ξ {0, 2}).natDegree = 2 ∧ (coalitionPoly ξ {0, 2}).eval 0 = 1 ∧
    (coalitionPoly ξ {0, 2}).eval (ξ 0) = 0 :=
  ⟨by rw [coalitionPoly_degree ξ S.coordinates_nonzero]; decide,
    coalitionPoly_eval_zero ξ S.coordinates_nonzero _, coalitionPoly_eval_member ξ _ (by simp)⟩
example (f : ShamirPoly (ZMod 7) 3 3) :
    observe ξ {0, 2} (shamir_poly_shift_equiv 3 5 (coalitionPoly ξ {0, 2})
      (by rw [coalitionPoly_degree ξ S.coordinates_nonzero]; decide)
      (coalitionPoly_eval_zero ξ S.coordinates_nonzero _) f) = observe ξ {0, 2} f :=
  shift_preserves_observations 3 5 ξ S.coordinates_nonzero _ (by decide) f

-- Threshold boundary cases and the independent two-share field identity.
example (s : ZMod 7) (f : ShamirPoly (ZMod 7) 1 s) (z : ZMod 7) : f.val.eval z = s := threshold_one f z
example (s a : ZMod 7) :
    2 / (2 - 1) * (s + a * 1) + (-1) / (2 - 1) * (s + a * 2) = s :=
  two_share_field s a 1 2 (by decide)
example (s : ZMod 7) (f : ShamirPoly (ZMod 7) 4 s) :
    ∑ i, lagrange_coeff ξ Finset.univ i * f.val.eval (ξ i) = s :=
  threshold_all ξ S.coordinates_injective f
example (I : Finset (Fin 4)) (hI : I.card = 3) :
    (∑ i ∈ I.map (Equiv.swap 0 1).toEmbedding,
      lagrange_coeff (ξ ∘ (Equiv.swap 0 1).symm) (I.map (Equiv.swap 0 1).toEmbedding) i *
        p.val.eval (ξ ((Equiv.swap 0 1).symm i))) =
      ∑ i ∈ I, lagrange_coeff ξ I i * p.val.eval (ξ i) :=
  reconstruction_permutation ξ S.coordinates_injective (Equiv.swap 0 1) I hI p

-- Weighted closure includes empty sums, negative weights and zero weights.
example (w s : Fin 2 → ZMod 7) (f : ∀ j, ShamirPoly (ZMod 7) 3 (s j)) :
    (∑ j, w j • (f j).val).natDegree < 3 ∧
    (∑ j, w j • (f j).val).eval 0 = ∑ j, w j * s j :=
  shamir_homomorphism_weighted_sum (by decide) Finset.univ w s f
example : ((-1 : ZMod 7) • p.val).eval 0 = -3 := by simp [p.property.2]
example : ((0 : ZMod 7) • p.val).eval 0 = 0 := by simp
example : (∑ j ∈ (∅ : Finset (Fin 4)), (j.val : ZMod 7) • p.val).eval 0 = 0 := by simp
example (w : Fin 2 → ZMod 7) (f : Fin 2 → (ZMod 7)[X]) (z : ZMod 7) :
    ∑ j, w j • ((f j).eval z • (1 : ZMod 7)) = (∑ j, w j • f j).eval z • (1 : ZMod 7) :=
  weighted_group_shares 1 Finset.univ w f z

-- Removing the nonzero-coordinate restriction exposes the secret, even with threshold 3.
example (s : ZMod 7) (f : ShamirPoly (ZMod 7) 3 s) : f.val.eval ((fun _ : Fin 1 => 0) 0) = s :=
  shamir_zero_coord_leakage f (fun _ : Fin 1 => 0) 0 rfl
example (f : ShamirPoly (ZMod 7) 3 0) (g : ShamirPoly (ZMod 7) 3 1) : f.val.eval 0 ≠ g.val.eval 0 := by
  rw [f.property.2, g.property.2]
  decide
example (f : CryptoShamirSecretSharing.Shamir2Polynomial) (x y : ℝ) (h : x ≠ y) :
    CryptoShamirSecretSharing.reconstructSecret x (CryptoShamirSecretSharing.share f x)
      y (CryptoShamirSecretSharing.share f y) = f.secret := bridge_to_scalar_shamir f x y h
example : CryptoShamirSecretSharingGroupSuite := crypto_shamir_group_master_suite
#print axioms crypto_shamir_group_master_suite
