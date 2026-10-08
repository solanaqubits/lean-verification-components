/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Finite prime-order Pedersen commitments. Distributional hiding is unconditional;
collision extraction is an algebraic reduction, not a computational hardness theorem.
The existing real-scalar commitment API is not modified. -/
namespace CryptoPedersenHomomorphicSum

universe u v
variable {q : ℕ} [Fact q.Prime]
variable {G : Type u} [Fintype G] [AddCommGroup G] [Module (ZMod q) G]

/-- Nonzero generators in a group of exactly q elements. No known discrete-log
relation or hardness axiom is part of the setup. -/
structure Setup (q : ℕ) (G : Type u) [Fact q.Prime] [Fintype G] [AddCommGroup G]
    [Module (ZMod q) G] where
  card_eq : Fintype.card G = q
  g : G
  h : G
  g_ne_zero : g ≠ 0
  h_ne_zero : h ≠ 0

def commit (S : Setup q G) (m r : ZMod q) : G := m • S.g + r • S.h

def aggregate {ι : Type v} (S : Setup q G) (I : Finset ι)
    (c m r : ι → ZMod q) : G := ∑ i ∈ I, c i • commit S (m i) (r i)

theorem commit_linear_combination {ι : Type v} (S : Setup q G) (I : Finset ι)
    (c m r : ι → ZMod q) :
    aggregate S I c m r = commit S (∑ i ∈ I, c i * m i) (∑ i ∈ I, c i * r i) := by
  simp [aggregate, commit, smul_add, mul_smul, Finset.sum_add_distrib, Finset.sum_smul]

@[simp] theorem commit_zero (S : Setup q G) : commit S 0 0 = 0 := by simp [commit]

theorem commit_empty_combination {ι : Type v} (S : Setup q G) (c m r : ι → ZMod q) :
    aggregate S ∅ c m r = commit S 0 0 ∧ commit S 0 0 = 0 := by simp [aggregate]

theorem commit_aggregate_all_zero {ι : Type v} (S : Setup q G) (I : Finset ι)
    (c m r : ι → ZMod q) (hc : ∀ i ∈ I, c i = 0) : aggregate S I c m r = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  simp [hc i hi]

theorem nonzero_generator_bijective (S : Setup q G) {h : G} (hh : h ≠ 0) :
    Function.Bijective (fun r : ZMod q => r • h) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  exact ⟨smul_left_injective (ZMod q) hh, (ZMod.card q).trans S.card_eq.symm⟩

theorem commit_bijective (S : Setup q G) (m : ZMod q) :
    Function.Bijective (commit S m) := by
  obtain ⟨hi, hs⟩ := nonzero_generator_bijective S S.h_ne_zero
  constructor
  · intro a b hab
    exact hi (add_left_cancel hab)
  · intro y
    obtain ⟨r, hr⟩ := hs (y - m • S.g)
    exact ⟨r, by simp [commit, hr]⟩

noncomputable def commitEquiv (S : Setup q G) (m : ZMod q) : ZMod q ≃ G :=
  Equiv.ofBijective (commit S m) (commit_bijective S m)

theorem map_uniform_equiv {α : Type*} {β : Type*} [Fintype α] [Nonempty α]
    [Fintype β] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
  classical
  ext b
  simp only [PMF.map_apply, PMF.uniformOfFintype_apply]
  simp_rw [← e.symm_apply_eq]
  simp [Fintype.card_congr e]

noncomputable def commitmentLaw (S : Setup q G) (m : ZMod q) : PMF G :=
  (PMF.uniformOfFintype (ZMod q)).map (commit S m)

theorem commit_perfect_hiding (S : Setup q G) (m : ZMod q) :
    commitmentLaw S m = PMF.uniformOfFintype G := map_uniform_equiv (commitEquiv S m)

theorem message_independent_law (S : Setup q G) (m m' : ZMod q) :
    commitmentLaw S m = commitmentLaw S m' := by rw [commit_perfect_hiding, commit_perfect_hiding]

theorem dlog_extraction_from_collision (S : Setup q G) {m r m' r' : ZMod q}
    (hc : commit S m r = commit S m' r') (hm : m ≠ m') :
    r ≠ r' ∧ S.h = ((m - m') * (r' - r)⁻¹) • S.g := by
  have hr : r ≠ r' := by
    intro he
    subst r'
    exact hm (smul_left_injective (ZMod q) S.g_ne_zero (add_right_cancel hc))
  have he : (m - m') • S.g = (r' - r) • S.h := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_add_eq_add]
    simpa [commit, add_comm] using hc
  refine ⟨hr, ?_⟩
  have hi := congrArg (fun x : G => (r' - r)⁻¹ • x) he
  simpa [smul_smul, sub_ne_zero.mpr hr.symm, mul_comm] using hi.symm

theorem affine_bijective {c : ZMod q} (hc : c ≠ 0) (a : ZMod q) :
    Function.Bijective (fun t : ZMod q => c * t + a) := by
  constructor
  · intro x y h
    exact mul_left_cancel₀ hc (add_right_cancel h)
  · intro y
    refine ⟨(y - a) / c, ?_⟩
    field_simp
    ring

theorem aggregate_update_blinding {ι : Type v} [DecidableEq ι] (S : Setup q G)
    (I : Finset ι) (c m r : ι → ZMod q) {k : ι} (hk : k ∈ I) (t : ZMod q) :
    aggregate S I c m (Function.update r k t) =
      commit S (∑ i ∈ I, c i * m i) (c k * t + ∑ i ∈ I.erase k, c i * r i) := by
  rw [commit_linear_combination]
  congr 1
  rw [← Finset.add_sum_erase I _ hk]
  simp only [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Draw the other coordinates from any joint law, then independently refresh k
with a uniform field element. Correlation among the other coordinates is allowed. -/
noncomputable def independentBlindings {ι : Type v} [DecidableEq ι]
    (k : ι) (μ : PMF (ι → ZMod q)) : PMF (ι → ZMod q) :=
  μ.bind fun r => (PMF.uniformOfFintype (ZMod q)).map (Function.update r k)

theorem aggregate_conditional_uniform {ι : Type v} [DecidableEq ι] (S : Setup q G)
    (I : Finset ι) (c m r : ι → ZMod q) {k : ι} (hk : k ∈ I) (hc : c k ≠ 0) :
    (PMF.uniformOfFintype (ZMod q)).map
      (fun t => aggregate S I c m (Function.update r k t)) = PMF.uniformOfFintype G := by
  have hb : Function.Bijective (fun t => aggregate S I c m (Function.update r k t)) := by
    simp_rw [aggregate_update_blinding S I c m r hk]
    exact (commit_bijective S _).comp (affine_bijective hc _)
  exact map_uniform_equiv (Equiv.ofBijective _ hb)

theorem commit_aggregate_hiding {ι : Type v} [DecidableEq ι] (S : Setup q G)
    (I : Finset ι) (c m : ι → ZMod q) {k : ι} (hk : k ∈ I) (hc : c k ≠ 0)
    (μ : PMF (ι → ZMod q)) :
    (independentBlindings k μ).map (aggregate S I c m) = PMF.uniformOfFintype G := by
  rw [independentBlindings, PMF.map_bind]
  simp_rw [PMF.map_comp]
  change (μ.bind fun r => (PMF.uniformOfFintype (ZMod q)).map
    (fun t => aggregate S I c m (Function.update r k t))) = _
  simp_rw [aggregate_conditional_uniform S I c m _ hk hc]
  exact PMF.bind_const _ _

theorem aggregate_zero_law {ι : Type v} (S : Setup q G) (I : Finset ι)
    (c m : ι → ZMod q) (hc : ∀ i ∈ I, c i = 0) (μ : PMF (ι → ZMod q)) :
    μ.map (aggregate S I c m) = PMF.pure 0 := by
  have h : aggregate S I c m = Function.const _ 0 := by
    funext r; exact commit_aggregate_all_zero S I c m r hc
  rw [h, PMF.map_const]

theorem aggregate_binding_scalar_only {ι : Type v} (S : Setup q G) (I : Finset ι)
    (c m r m' r' : ι → ZMod q)
    (he : aggregate S I c m r = aggregate S I c m' r')
    (hm : (∑ i ∈ I, c i * m i) ≠ ∑ i ∈ I, c i * m' i) :
    (∑ i ∈ I, c i * r i) ≠ (∑ i ∈ I, c i * r' i) ∧
    S.h = (((∑ i ∈ I, c i * m i) - ∑ i ∈ I, c i * m' i) *
      ((∑ i ∈ I, c i * r' i) - ∑ i ∈ I, c i * r i)⁻¹) • S.g := by
  rw [commit_linear_combination, commit_linear_combination] at he
  exact dlog_extraction_from_collision S he hm

def leftMessage : Fin 2 → ZMod q := ![1, 0]
def rightMessage : Fin 2 → ZMod q := ![0, 1]

theorem vector_not_determined (S : Setup q G) :
    (leftMessage : Fin 2 → ZMod q) ≠ rightMessage ∧
    (∑ i : Fin 2, leftMessage (q := q) i) = (∑ i : Fin 2, rightMessage (q := q) i) ∧
    aggregate S Finset.univ (fun _ => 1) leftMessage (fun _ => 0) =
      aggregate S Finset.univ (fun _ => 1) rightMessage (fun _ => 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have h0 := congrFun h 0
    simp [leftMessage, rightMessage] at h0
  · simp [Fin.sum_univ_two, leftMessage, rightMessage]
  · simp [aggregate, Fin.sum_univ_two, leftMessage, rightMessage, commit]

theorem independent_coordinate_uniform {ι : Type v} [DecidableEq ι]
    (k : ι) (μ : PMF (ι → ZMod q)) :
    (independentBlindings k μ).map (fun r => r k) = PMF.uniformOfFintype (ZMod q) := by
  suffices h : (PMF.uniformOfFintype (ZMod q)).map (fun t => t) =
      PMF.uniformOfFintype (ZMod q) by
    simpa [independentBlindings, PMF.map_bind, PMF.map_comp,
      Function.comp_def, PMF.bind_const] using h
  exact PMF.map_id _

/-- Exact joint-law factorization: the refreshed coordinate and the remaining
vector (encoded with zero at k) are drawn independently. -/
theorem independent_blindings_joint_law {ι : Type v} [DecidableEq ι]
    (k : ι) (μ : PMF (ι → ZMod q)) :
    (independentBlindings k μ).map (fun r => (r k, Function.update r k 0)) =
      (μ.map (fun r => Function.update r k 0)).bind
        (fun rest => (PMF.uniformOfFintype (ZMod q)).map (fun t => (t, rest))) := by
  simp [independentBlindings, PMF.map_bind, PMF.map_comp, Function.comp_def]

theorem commitment_point_probability (S : Setup q G) (m : ZMod q) (y : G) :
    commitmentLaw S m y = (q : ENNReal)⁻¹ := by
  rw [commit_perfect_hiding, PMF.uniformOfFintype_apply, S.card_eq]

theorem zero_law_not_uniform (S : Setup q G) :
    (PMF.pure (0 : G)) ≠ PMF.uniformOfFintype G := by
  intro h
  have he := congrArg (fun p : PMF G => p S.g) h
  simp [PMF.pure_apply, S.g_ne_zero, eq_comm] at he

/-- Uniform marginals need not suffice: r₁=t and r₂=-t cancel exactly. -/
noncomputable def correlatedBlindings (q : ℕ) [Fact q.Prime] : PMF (Fin 2 → ZMod q) :=
  (PMF.uniformOfFintype (ZMod q)).map (fun t => ![t, -t])

theorem correlated_first_uniform :
    (correlatedBlindings q).map (fun r => r 0) = PMF.uniformOfFintype (ZMod q) := by
  suffices h : (PMF.uniformOfFintype (ZMod q)).map (fun t => t) =
      PMF.uniformOfFintype (ZMod q) by
    simpa [correlatedBlindings, PMF.map_comp, Function.comp_def] using h
  exact PMF.map_id _

theorem correlated_second_uniform :
    (correlatedBlindings q).map (fun r => r 1) = PMF.uniformOfFintype (ZMod q) := by
  rw [correlatedBlindings, PMF.map_comp]
  exact map_uniform_equiv (Equiv.neg (ZMod q))

theorem correlated_aggregate_constant (S : Setup q G) :
    (correlatedBlindings q).map
      (aggregate S Finset.univ (fun _ => 1) (fun _ => 0)) = PMF.pure 0 := by
  rw [correlatedBlindings, PMF.map_comp]
  have he : (aggregate S Finset.univ (fun _ => 1) (fun _ => 0)) ∘
      (fun t : ZMod q => ![t, -t]) = Function.const _ 0 := by
    funext t
    simp [aggregate, Fin.sum_univ_two, commit]
  rw [he, PMF.map_const]

/-- A concrete satisfiability witness, not an example of DLOG hardness. -/
def scalarSetup (h : ZMod q) (hh : h ≠ 0) : Setup q (ZMod q) where
  card_eq := ZMod.card q
  g := 1
  h := h
  g_ne_zero := one_ne_zero
  h_ne_zero := hh

theorem setup_satisfiable (q : ℕ) [Fact q.Prime] : Nonempty (Setup q (ZMod q)) :=
  ⟨scalarSetup 1 one_ne_zero⟩

theorem known_relation_opening (S : Setup q G) {x : ZMod q} (hx : S.h = x • S.g)
    (m r m' : ZMod q) : commit S m r = commit S m' (r + (m - m') / x) := by
  have hx0 : x ≠ 0 := by
    intro he
    apply S.h_ne_zero
    simpa [he] using hx
  simp only [commit, hx, smul_smul, ← add_smul]
  congr 1
  field_simp
  ring

/-- Each field of the contract states a result, not an assumption on a setup. -/
structure VerifiedProperties (S : Setup q G) : Prop where
  linear : ∀ n (I : Finset (Fin n)) (c m r : Fin n → ZMod q),
    aggregate S I c m r = commit S (∑ i ∈ I, c i * m i) (∑ i ∈ I, c i * r i)
  zero : commit S 0 0 = 0
  bijective : ∀ m, Function.Bijective (commit S m)
  perfect_hiding : ∀ m, commitmentLaw S m = PMF.uniformOfFintype G
  aggregate_hiding : ∀ n (I : Finset (Fin n)) (c m : Fin n → ZMod q) k,
    k ∈ I → c k ≠ 0 → ∀ μ : PMF (Fin n → ZMod q),
      (independentBlindings k μ).map (aggregate S I c m) = PMF.uniformOfFintype G
  zero_weights : ∀ n (I : Finset (Fin n)) (c m : Fin n → ZMod q),
    (∀ i ∈ I, c i = 0) → ∀ μ : PMF (Fin n → ZMod q),
      μ.map (aggregate S I c m) = PMF.pure 0
  collision : ∀ m r m' r', commit S m r = commit S m' r' → m ≠ m' →
    r ≠ r' ∧ S.h = ((m - m') * (r' - r)⁻¹) • S.g
  vector_boundary : (leftMessage : Fin 2 → ZMod q) ≠ rightMessage ∧
    (∑ i : Fin 2, leftMessage (q := q) i) = (∑ i : Fin 2, rightMessage (q := q) i) ∧
    aggregate S Finset.univ (fun _ => 1) leftMessage (fun _ => 0) =
      aggregate S Finset.univ (fun _ => 1) rightMessage (fun _ => 0)
  correlated_boundary : (correlatedBlindings q).map
    (aggregate S Finset.univ (fun _ => 1) (fun _ => 0)) = PMF.pure 0
  degenerate_not_uniform : (PMF.pure (0 : G)) ≠ PMF.uniformOfFintype G

theorem verified_properties (S : Setup q G) : VerifiedProperties S where
  linear := fun _ => commit_linear_combination S
  zero := commit_zero S
  bijective := commit_bijective S
  perfect_hiding := commit_perfect_hiding S
  aggregate_hiding := fun _ I c m _ hk hc => commit_aggregate_hiding S I c m hk hc
  zero_weights := fun _ => aggregate_zero_law S
  collision := fun _ _ _ _ => dlog_extraction_from_collision S
  vector_boundary := vector_not_determined S
  correlated_boundary := correlated_aggregate_constant S
  degenerate_not_uniform := zero_law_not_uniform S

structure CryptoPedersenHomomorphicSumSuite : Prop where
  all_models : ∀ (q : ℕ) [Fact q.Prime] (G : Type u) [Fintype G] [AddCommGroup G]
    [Module (ZMod q) G] (S : Setup q G), VerifiedProperties S
  satisfiable : ∀ (q : ℕ) [Fact q.Prime], Nonempty (Setup q (ZMod q))

theorem crypto_pedersen_homomorphic_sum_master_suite : CryptoPedersenHomomorphicSumSuite.{u} where
  all_models := fun _ _ _ _ _ _ S => verified_properties S
  satisfiable := setup_satisfiable

end CryptoPedersenHomomorphicSum
