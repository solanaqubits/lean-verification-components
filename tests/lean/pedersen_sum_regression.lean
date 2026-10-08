import Verification.CryptoPedersenHomomorphicSum
import Verification.CryptoPedersenCommitment
import Mathlib.Tactic.NormNum

open CryptoPedersenHomomorphicSum

universe u
section Generic
variable {q : ℕ} [Fact q.Prime] {G : Type u}
variable [Fintype G] [AddCommGroup G] [Module (ZMod q) G] (S : Setup q G)

-- The group remains abstract; cardinality and nonzero generators are explicit.
example : VerifiedProperties S :=
  crypto_pedersen_homomorphic_sum_master_suite.all_models q G S

example (m m' : ZMod q) (y : G) :
    commitmentLaw S m = commitmentLaw S m' ∧ commitmentLaw S m y = (q : ENNReal)⁻¹ :=
  ⟨message_independent_law S m m', commitment_point_probability S m y⟩

example {n : ℕ} (I : Finset (Fin n)) (c m : Fin n → ZMod q)
    (k : Fin n) (hk : k ∈ I) (hc : c k ≠ 0) (μ : PMF (Fin n → ZMod q)) :
    (independentBlindings k μ).map (aggregate S I c m) = PMF.uniformOfFintype G :=
  commit_aggregate_hiding S I c m hk hc μ

example {n : ℕ} (k : Fin n) (μ : PMF (Fin n → ZMod q)) :
    (independentBlindings k μ).map (fun r => (r k, Function.update r k 0)) =
      (μ.map (fun r => Function.update r k 0)).bind
        (fun rest => (PMF.uniformOfFintype (ZMod q)).map (fun t => (t, rest))) :=
  independent_blindings_joint_law k μ

-- Correlated uniform marginals can give a nonuniform aggregate, even for q=2.
example : (correlatedBlindings q).map (fun r => r 0) = PMF.uniformOfFintype (ZMod q) ∧
    (correlatedBlindings q).map (fun r => r 1) = PMF.uniformOfFintype (ZMod q) ∧
    (correlatedBlindings q).map (aggregate S Finset.univ (fun _ => 1) (fun _ => 0)) ≠
      PMF.uniformOfFintype G := by
  refine ⟨correlated_first_uniform, correlated_second_uniform, ?_⟩
  rw [correlated_aggregate_constant]
  exact zero_law_not_uniform S

example (m r m' r' : ZMod q) (hc : commit S m r = commit S m' r') (hm : m ≠ m') :
    r ≠ r' ∧ S.h = ((m - m') * (r' - r)⁻¹) • S.g :=
  dlog_extraction_from_collision S hc hm

example (c m r m' r' : Fin 3 → ZMod q)
    (hc : aggregate S Finset.univ c m r = aggregate S Finset.univ c m' r')
    (hm : (∑ i, c i * m i) ≠ ∑ i, c i * m' i) :
    (∑ i, c i * r i) ≠ (∑ i, c i * r' i) :=
  (aggregate_binding_scalar_only S Finset.univ c m r m' r' hc hm).1

example (m : Fin 0 → ZMod q) (μ : PMF (Fin 0 → ZMod q)) :
    μ.map (aggregate S Finset.univ (fun _ => 0) m) = PMF.pure 0 :=
  aggregate_zero_law S _ _ _ (by simp) μ

example (m r : ZMod q) :
    aggregate S Finset.univ (fun _ : Fin 2 => 1) (fun _ => m) (fun _ => r) =
      commit S (2 * m) (2 * r) := by
  simp [commit_linear_combination, two_mul]

example (m r : ZMod q) :
    aggregate S Finset.univ (fun _ : Fin 1 => -1) (fun _ => m) (fun _ => r) =
      commit S (-m) (-r) := by simp [commit_linear_combination]

example : (leftMessage : Fin 2 → ZMod q) ≠ rightMessage ∧
    aggregate S Finset.univ (fun _ => 1) leftMessage (fun _ => 0) =
      aggregate S Finset.univ (fun _ => 1) rightMessage (fun _ => 0) :=
  ⟨(vector_not_determined S).1, (vector_not_determined S).2.2⟩

example {x : ZMod q} (hx : S.h = x • S.g) (m r m' : ZMod q) :
    commit S m r = commit S m' (r + (m - m') / x) :=
  known_relation_opening S hx m r m'
end Generic

instance : Fact (Nat.Prime 7) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
def setup7 : Setup 7 (ZMod 7) := scalarSetup 3 (by decide)
def setup2 : Setup 2 (ZMod 2) := scalarSetup 1 one_ne_zero

example : commit setup7 1 0 = commit setup7 0 5 := by decide
example : (5 : ZMod 7) ≠ 0 ∧ ((1 : ZMod 7) / 5) = 3 := by
  refine ⟨by decide, (div_eq_iff (by decide)).mpr ?_⟩
  decide
example : commit setup2 1 0 = commit setup2 0 1 := by decide
example : Nonempty (Setup 2 (ZMod 2)) := setup_satisfiable 2
example : (correlatedBlindings 2).map
    (aggregate setup2 Finset.univ (fun _ => 1) (fun _ => 0)) = PMF.pure 0 :=
  correlated_aggregate_constant setup2

-- The zero-generator shortcuts are excluded, rather than silently assumed sound.
example (S : Setup 7 (ZMod 7)) : S.g ≠ 0 ∧ S.h ≠ 0 := ⟨S.g_ne_zero, S.h_ne_zero⟩
