import Verification.CryptoCommitmentVectorPedersenGroup

open CryptoCommitmentVectorPedersenGroup
open scoped BigOperators

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private abbrev H : ZMod 7 := 1
private def bases : Fin 2 → ZMod 7 := ![2, 3]
private theorem hH : Function.Bijective (fun r : ZMod 7 => r • H) := by simp [H, smul_eq_mul]

example : Nonempty (Setup 7 2 (ZMod 7)) := ⟨ConsistencyModel 7 2⟩
example (m : MsgVector 7 2) : Function.Bijective (commit_vec (q := 7) bases H m) :=
  commit_vec_hiding_equiv bases H hH m
example (m : MsgVector 7 2) : commitmentLaw bases H m = PMF.uniformOfFintype (ZMod 7) :=
  commit_vec_perfect_hiding bases H hH m
example (m m' : MsgVector 7 2) : commitmentLaw bases H m = commitmentLaw bases H m' :=
  message_independent_law bases H hH m m'

example (m : MsgVector 7 0) (r : ZMod 7) :
    commit_vec (q := 7) (fun i : Fin 0 => Fin.elim0 i) H m r = r • H := empty_vector H m r
example (S : CryptoPedersenHomomorphicSum.Setup 7 (ZMod 7)) (m r : ZMod 7) :
    commit_vec (q := 7) (fun _ : Fin 1 => S.g) S.h (fun _ => m) r =
      CryptoPedersenHomomorphicSum.commit S m r := bridge_to_scalar_pedersen S m r

example (m m' : MsgVector 7 2) (r r' : ZMod 7) :
    commit_vec (q := 7) bases H (m + m') (r + r') = commit_vec (q := 7) bases H m r + commit_vec (q := 7) bases H m' r' :=
  commit_vec_add_homomorphism bases H m m' r r'
example (m : MsgVector 7 2) (r a : ZMod 7) :
    commit_vec (q := 7) bases H ((-a) • m) ((-a) * r) = (-a) • commit_vec (q := 7) bases H m r :=
  commit_vec_smul_homomorphism bases H (-a) m r
example (m : MsgVector 7 2) (r : ZMod 7) :
    commit_vec (q := 7) bases H ((0 : ZMod 7) • m) (0 * r) = 0 := by
  simp
example (w r : Fin 2 → ZMod 7) (m : Fin 2 → MsgVector 7 2) :
    (∑ j, w j • commit_vec (q := 7) bases H (m j) (r j)) =
      commit_vec (q := 7) bases H (∑ j, w j • m j) (∑ j, w j * r j) :=
  commit_vec_weighted_sum_homomorphism Finset.univ bases H w r m
example (w r : ℕ → ZMod 7) (m : ℕ → MsgVector 7 2) :
    (∑ j ∈ (∅ : Finset ℕ), w j • commit_vec (q := 7) bases H (m j) (r j)) = 0 := by simp

example (m m' : MsgVector 7 2) (r r' : ZMod 7)
    (hc : commit_vec (q := 7) bases H m r = commit_vec (q := 7) bases H m' r') (hm : m ≠ m') :
    (∑ i, (m i - m' i) • bases i) + (r - r') • H = 0 ∧ ∃ i, m i - m' i ≠ 0 :=
  ⟨commit_vec_collision_linear_relation bases H m m' r r' hc,
   commit_vec_collision_nontrivial_coeff m m' hm⟩

example : commit_vec (q := 7) bases H ![3, 0] 1 = commit_vec (q := 7) bases H ![0, 0] 0 := by decide
example : bases 0 = (-(((3 : ZMod 7) - 0)⁻¹ * (0 + (1 - 0)))) • H := by
  have h := commit_vec_dlog_extraction_conditional bases H ![3, 0] ![0, 0] 1 0 0
    (fun _ => (3 : ZMod 7)) (by intro i hi; fin_cases i <;> simp_all [bases, H])
    (by decide) (by decide)
  simpa [Fin.sum_univ_two] using h

-- Equal bases give distinct message vectors with the same blinding and commitment.
example : (![1, 0] : MsgVector 7 2) ≠ ![0, 1] ∧
    commit_vec (q := 7) (fun _ : Fin 2 => (1 : ZMod 7)) H ![1, 0] 4 =
      commit_vec (q := 7) (fun _ : Fin 2 => (1 : ZMod 7)) H ![0, 1] 4 := by decide
example (G : Fin 2 → ZMod 7) (m : MsgVector 7 2) (r : ZMod 7) (hg : G 0 = G 1) :
    commit_vec (q := 7) G H (m ∘ Equiv.swap 0 1) r = commit_vec (q := 7) G H m r :=
  commit_vec_identical_generators_collision G H m r 0 1 hg

example (m : MsgVector 7 2) (r : ZMod 7) :
    (m + ![1, 0], r + (-2 : ZMod 7)) ≠ (m, r) ∧
      commit_vec (q := 7) bases H (m + ![1, 0]) (r + (-2 : ZMod 7)) = commit_vec (q := 7) bases H m r :=
  commit_vec_known_relation_alternate_open bases H m ![1, 0] r (-2)
    (by decide) (Or.inr (by decide))

example : CryptoCommitmentVectorPedersenGroupSuite := crypto_vector_pedersen_master_suite
#print axioms crypto_vector_pedersen_master_suite
