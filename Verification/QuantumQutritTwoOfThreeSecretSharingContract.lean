/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.QuantumErasureCorrectabilityContract

/-! The Cleve–Gottesman–Lo three-qutrit code. Factors are ordered A,B,C.
Cyclic regroupings put the retained pair first and the erased share last.
This is a fixed exact (2,3) scheme, not a general threshold construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators ComplexOrder Kronecker
open QuantumPOVMNaimarkDilation QuantumCPTPChannelContract
open QuantumKnillLaflammeEnvironmentCriterion QuantumComplementaryChannelContract
open QuantumReferencePreservingRecoveryContract QuantumErasureCorrectabilityContract
open QuantumHelstromStateDiscrimination
namespace QuantumQutritTwoOfThreeSecretSharingContract

/-- Normalized amplitude, with its complex conjugation explicit. -/
def amplitude : ℂ := ((Real.sqrt 3)⁻¹ : ℝ)
@[simp] theorem amplitude_star : star amplitude = amplitude := by simp [amplitude]
@[simp] theorem amplitude_conj : (starRingEnd ℂ) amplitude = amplitude := amplitude_star
@[simp] theorem amplitude_sq : amplitude ^ 2 = (1 / 3 : ℂ) := by
  have h : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hr : ((Real.sqrt 3)⁻¹) ^ 2 = (1 / 3 : ℝ) := by rw [inv_pow, h]; norm_num
  unfold amplitude
  rw [← Complex.ofReal_pow, hr]
  norm_num

/-- Flat ordering ((A,B),C). -/
def triple (a b c : Fin 3) : Fin (9 * 3) := pair (pair a b) c

/-- The coefficient of |a,b,c> in J|s>; all additions are in Fin 3. -/
def code : Matrix (Fin (9 * 3)) (Fin 3) ℂ := fun x s =>
  let ab := (finProdFinEquiv.symm x).1
  let c := (finProdFinEquiv.symm x).2
  let a := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm ab).1
  let b := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm ab).2
  if b = a + s ∧ c = a + 2 * s then amplitude else 0

theorem code_entry (a b c s : Fin 3) :
    code (triple a b c) s = if b = a + s ∧ c = a + 2*s then amplitude else 0 := by
  simp [code, triple, pair]

set_option maxHeartbeats 800000 in
-- Finite matrix expansion; the larger budget does not change the kernel checks.
/-- The literal sum-of-basis-vectors specification in the contract. -/
theorem code_column (x : Fin 27) (s : Fin 3) :
    code x s = amplitude * ∑ r : Fin 3,
      (if x = triple r (r+s) (r+2*s) then (1 : ℂ) else 0) := by
  simp only [Fin.sum_univ_succ]
  fin_cases s <;> fin_cases x <;>
    norm_num [code, triple, pair, finProdFinEquiv, Fin.divNat, Fin.modNat,
      Fin.add_def, Fin.mul_def, Fin.ext_iff, Fin.sum_univ_succ]

/-- q=0 erases A and retains (B,C); q=1 erases B and retains (C,A);
q=2 erases C and retains (A,B). Maps grouped coordinates to physical ABC. -/
def physicalIndex (q : Fin 3) (x : Fin (9 * 3)) : Fin (9 * 3) :=
  let uv := (finProdFinEquiv.symm x).1
  let w := (finProdFinEquiv.symm x).2
  let u := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv).1
  let v := ((finProdFinEquiv : Fin 3 × Fin 3 ≃ Fin 9).symm uv).2
  if q = 0 then triple w u v else if q = 1 then triple v w u else triple u v w

def groupedCode (q : Fin 3) : Matrix (Fin (9 * 3)) (Fin 3) ℂ :=
  fun x s => code (physicalIndex q x) s

set_option maxHeartbeats 800000 in
-- Finite matrix expansion; the larger budget does not change the kernel checks.
theorem cyclic_code (q : Fin 3) : groupedCode q = code := by
  ext x s
  fin_cases q <;> fin_cases s <;> fin_cases x <;>
    norm_num [groupedCode, physicalIndex, code, triple, pair, finProdFinEquiv,
      Fin.divNat, Fin.modNat, Fin.add_def, Fin.mul_def, Fin.ext_iff]

set_option maxHeartbeats 800000 in
-- Finite matrix expansion; the larger budget does not change the kernel checks.
theorem code_isometry : code.conjTranspose * code = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [code, Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.add_def, Fin.mul_def,
      Fin.ext_iff] <;> ring_nf <;> norm_num

def mixedShare : Q 3 := (1/3 : ℂ) • (1 : Q 3)

set_option maxHeartbeats 800000 in
-- Finite matrix expansion; the larger budget does not change the kernel checks.
theorem single_share (q : Fin 3) (X : Q 3) :
    traceA (encode (groupedCode q) X) = X.trace • mixedShare := by
  rw [cyclic_code]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [traceA, partialTrace_system, toProduct, encode, code, mixedShare,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.add_def, Fin.mul_def,
      Fin.ext_iff, Matrix.trace, Matrix.diag, Matrix.smul_apply] <;>
    ring_nf <;> simp <;> ring

/-- The regrouping is a genuine permutation of the physical basis. -/
theorem physicalIndex_bijective (q : Fin 3) : Function.Bijective (physicalIndex q) := by
  fin_cases q <;> decide

def regroup (q : Fin 3) (Y : Q 27) : Q (9 * 3) :=
  fun x y => Y (physicalIndex q x) (physicalIndex q y)

theorem regroup_encode (q : Fin 3) (X : Q 3) :
    regroup q (encode code X) = encode (groupedCode q) X := by
  rfl

/-- Physical reduced state of share q, tracing out its complementary pair. -/
def share (q : Fin 3) (Y : Q 27) : Q 3 := traceA (regroup q Y)
/-- Physical reduced state of the cyclically ordered surviving pair. -/
def retainedPair (q : Fin 3) (Y : Q 27) : Q 9 := traceB (regroup q Y)

theorem share_privacy (q : Fin 3) (X : Q 3) :
    share q (encode code X) = X.trace • mixedShare := by
  exact single_share q X

theorem grouped_isometry (q : Fin 3) : (groupedCode q).conjTranspose * groupedCode q = 1 := by
  rw [cyclic_code, code_isometry]

theorem mixedShare_density : Density mixedShare := by
  apply environment_density (by decide) (erasureChannel 9 3) (groupedCode 2)
    (grouped_isometry 2) mixedShare
  apply (knill_laflamme_equiv_environment _ _ _).mpr
  intro X
  rw [erasure_complement, single_share]

/-- Recovery is obtained from the already proved erasure criterion, not assumed. -/
theorem pair_recoverable (q : Fin 3) : ErasureRecoverable (groupedCode q) :=
  (erasure_correctability_equivalence (by decide) _ (grouped_isometry q)).mpr
    ⟨mixedShare,mixedShare_density,single_share q⟩

/-- A finite Kraus family selected once for each erased position. -/
def recoverySize (q : Fin 3) : ℕ := (pair_recoverable q).choose

def pairRecovery (q : Fin 3) : KrausChannel 9 3 (recoverySize q) :=
  (pair_recoverable q).choose_spec.choose

theorem pair_recovery (q : Fin 3) (X : Q 3) :
    apply_channel (pairRecovery q) (retainedPair q (encode code X)) = X :=
  (pair_recoverable q).choose_spec.choose_spec X

theorem reference_recovery (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) m X = X :=
  erasure_reference_recovery _ _ (pair_recovery q) m X

theorem reference_share_independence (q : Fin 3) (m : ℕ) (X : Joint m 3) :
    amplify (environmentMap (erasureChannel 9 3) (groupedCode q)) m X =
      traceLogical X ⊗ₖ mixedShare := by
  apply independence_env_reference
  intro Y
  rw [erasure_complement, single_share]

theorem maximally_entangled_recovery (q : Fin 3) :
    liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) 3
      (maximallyEntangled 3) = maximallyEntangled 3 := reference_recovery q 3 _

/-- A single share kills every off-diagonal matrix unit, including complex ones. -/
theorem share_coherence (q i j : Fin 3) (h : i ≠ j) (z : ℂ) :
    share q (encode code (Matrix.single i j z)) = 0 := by
  rw [share_privacy, Matrix.trace_single_eq_of_ne _ _ _ h, zero_smul]

/-- No CPTP recovery from one share exists, for any finite Kraus count. -/
theorem single_share_not_recoverable (q : Fin 3) :
    ¬ ∃ s, ∃ R : KrausChannel 3 3 s,
      ∀ X : Q 3, apply_channel R (share q (encode code X)) = X := by
  rintro ⟨s,R,h⟩
  have hx := h (Matrix.single 0 1 (1 : ℂ))
  rw [share_coherence q 0 1 (by decide), map_zero] at hx
  have he := congrArg (fun M : Q 3 => M 0 1) hx
  norm_num at he

structure QuantumQutritTwoOfThreeSecretSharingContractSuite : Prop where
  column : ∀ (x : Fin 27) (s : Fin 3), code x s = amplitude *
    ∑ r : Fin 3, (if x = triple r (r+s) (r+2*s) then (1 : ℂ) else 0)
  isometry : code.conjTranspose * code = 1
  permutations : ∀ q, Function.Bijective (physicalIndex q)
  regrouping : ∀ q (X : Q 3), regroup q (encode code X) = encode (groupedCode q) X
  privacy : ∀ q (X : Q 3), share q (encode code X) = X.trace • mixedShare
  density : Density mixedShare
  recovery : ∀ q (X : Q 3), apply_channel (pairRecovery q) (retainedPair q (encode code X)) = X
  reference : ∀ q m (X : Joint m 3),
    liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) m X = X
  decoupling : ∀ q m (X : Joint m 3),
    amplify (environmentMap (erasureChannel 9 3) (groupedCode q)) m X = traceLogical X ⊗ₖ mixedShare
  entangled : ∀ q, liftedRecovery (erasureChannel 9 3) (groupedCode q) (pairRecovery q) 3
    (maximallyEntangled 3) = maximallyEntangled 3
  obstruction : ∀ q, ¬ ∃ s, ∃ R : KrausChannel 3 3 s,
    ∀ X : Q 3, apply_channel R (share q (encode code X)) = X

theorem verification_suite : QuantumQutritTwoOfThreeSecretSharingContractSuite where
  column := code_column
  isometry := code_isometry
  permutations := physicalIndex_bijective
  regrouping := regroup_encode
  privacy := share_privacy
  density := mixedShare_density
  recovery := pair_recovery
  reference := reference_recovery
  decoupling := reference_share_independence
  entangled := maximally_entangled_recovery
  obstruction := single_share_not_recoverable

end QuantumQutritTwoOfThreeSecretSharingContract
