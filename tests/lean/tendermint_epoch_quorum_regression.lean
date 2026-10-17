import Verification.DistributedTendermintQuorumIntersectionEpochTransitionContract
import Mathlib.Data.Fin.VecNotation

open Finset DistributedTendermintEpochIdentityContract
open DistributedTendermintQuorumIntersectionEpochTransitionContract
open DistributedTendermintCoreSafety (Config)
namespace TendermintEpochQuorumRegression
set_option maxRecDepth 4096

def p : Fin 3 → ℚ := ![1/2, 1/3, 1/6]
def z : Fin 3 → ℚ := ![1/3, 1/2, 1/6]
def uniform : Fin 3 → ℚ := fun _ => 1/3
def raw : Fin 3 → ℚ := ![3, 2, 1]
def faults : Finset (Fin 3) := {2}
def strong : Fin 3 → ℚ := ![4/5, 1/5, 0]
def forcedOld : Fin 3 → ℚ := ![3/5, 2/5, 0]
def forcedNew : Fin 3 → ℚ := ![3/5, 0, 2/5]
def c : Config 3 := ⟨![3, 2, 1], {2}, 17⟩
def old : EpochConfig (Fin 3) :=
  ⟨2, ⟨![0, 1], by decide +kernel⟩, ![3, 2], ∅, 10, 19, by decide⟩
def next : EpochConfig (Fin 3) :=
  ⟨3, Function.Embedding.refl _, ![3, 2, 1], ∅, 20, 29, by decide⟩
def shuffled := reindex old (Equiv.swap (0 : Fin 2) (1 : Fin 2))

theorem p_normalized : Normalized p := by decide +kernel
theorem z_normalized : Normalized z := by decide +kernel

example : mass p univ = 1 := by decide +kernel
example : mass z univ = 1 := by decide +kernel
example : mass (common p z) univ = 5/6 := by decide +kernel
example : variation p z = 1/6 := by decide +kernel
example : variation z p = 1/6 := by decide +kernel
example : honestCommon p z ∅ = 5/6 := by decide +kernel
example : honestCommon p z faults = 2/3 := by decide +kernel
example : mass (common p z) faults = 1/6 := by decide +kernel
example : honestLoss p z faults = 1/6 := by decide +kernel
example : mass p faults + honestLoss p z faults = 1/3 := by decide +kernel
example : isQuorum p (4/5) {0, 1} ∧ isQuorum z (4/5) {0, 1} := by decide +kernel
example : mass (common p z) (honestIntersection faults {0, 1} {0, 1}) = 2/3 := by decide +kernel
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ faults ∧ 0 < p v ∧ 0 < z v :=
  honest_node_in_intersection p z p_normalized z_normalized faults {0, 1} {0, 1} (4/5) (4/5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : (4:ℚ)/5 + 4/5 - 1 - variation p z - mass (common p z) faults ≤
    mass (common p z) (honestIntersection faults {0, 1} {0, 1}) :=
  variation_weight_bound p z p_normalized z_normalized faults {0, 1} {0, 1} (4/5) (4/5)
    (by decide +kernel) (by decide +kernel)
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ faults ∧ 0 < p v ∧ 0 < z v :=
  directed_loss_sufficient p z p_normalized z_normalized faults {0, 1} {0, 1} (4/5) (4/5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ faults ∧ 0 < p v ∧ 0 < z v :=
  strict_tendermint_intersection p z p_normalized z_normalized faults {0, 1} {0, 1}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : variation p p = 0 := (static_epoch_equivalence p p_normalized faults).2
example : honestCommon p p faults = 5/6 := by decide +kernel
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ faults ∧ 0 < p v :=
  static_epoch_specialization p p_normalized faults {0, 1} {0, 1}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : mass raw univ = 6 := by decide +kernel
example : normalize raw = p := by apply funext; decide +kernel
example : normalize (fun v => 7 * raw v) = normalize raw :=
  normalization_scale_invariant raw 7 (by norm_num)
example : Normalized (normalize raw) := normalize_normalized raw (by decide +kernel) (by decide +kernel)
example : ¬ Normalized (fun _ : Fin 3 => (0 : ℚ)) := by decide +kernel
example : ¬ Normalized (normalize (fun _ : Fin 3 => (0 : ℚ))) := by decide +kernel
example : ¬ Normalized (![2, -1, 0] : Fin 3 → ℚ) := by decide +kernel
example : normalize (legacyWeights c) = p := by apply funext; decide +kernel
example : (2:ℚ)/3 < mass (normalize (legacyWeights c)) {0, 1} ↔ c.quorum {0, 1} :=
  legacy_quorum_equivalence c {0, 1} (by decide +kernel)
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ c.byzantine ∧ 0 < c.weight v :=
  static_legacy_specialization c {0, 1} {0, 1}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : Normalized boundaryOld ∧ Normalized boundaryNew :=
  ⟨insufficient_overlap_counterexample.1, insufficient_overlap_counterexample.2.1⟩
example : variation boundaryOld boundaryNew = 1/3 := by decide +kernel
example : honestCommon boundaryOld boundaryNew ∅ = 2/3 := by decide +kernel
example : isQuorum boundaryOld (2/3) {0, 1} ∧ isQuorum boundaryNew (2/3) {2, 3} := by decide +kernel
example : honestIntersection (∅ : Finset (Fin 4)) {0, 1} {2, 3} = ∅ := by decide +kernel
example : ¬ ∃ v ∈ ({0, 1} : Finset (Fin 4)) ∩ {2, 3}, v ∉ (∅ : Finset (Fin 4)) := by decide +kernel
example : (2:ℚ)/3 = mass boundaryOld {0, 1} := by decide +kernel
example : variation splitOld splitNew = 2/5 := by decide +kernel
example : (2:ℚ)/3 < mass splitOld {0, 1} ∧ (2:ℚ)/3 < mass splitNew {2, 3} := by decide +kernel
example : mass (common splitOld splitNew) (honestIntersection ∅ {0, 1} {2, 3}) = 0 := by decide +kernel
-- Equality cannot replace strict slack for non-strict quorums, even in one epoch.
example : Normalized uniform ∧ mass uniform {1} = 1/3 := by decide +kernel
example : isQuorum uniform (2/3) {0, 1} ∧ isQuorum uniform (2/3) {1, 2} := by decide +kernel
example : honestCommon uniform uniform {1} = 2/3 := by decide +kernel
example : honestIntersection ({1} : Finset (Fin 3)) {0, 1} {1, 2} = ∅ := by decide +kernel
-- An overly conservative two-fault-mass criterion loses an otherwise valid static case.
example : Normalized strong ∧ mass strong {1} < 1/3 := by decide +kernel
example : ¬ (mass strong {1} + mass strong {1} + variation strong strong < 1/3) := by decide +kernel
example : ∃ v ∈ ({0} : Finset (Fin 3)) ∩ {0}, v ∉ ({1} : Finset (Fin 3)) ∧ 0 < strong v :=
  static_epoch_specialization strong (by decide +kernel) {1} {0} {0}
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
-- Sufficient common-mass bounds are not necessary for every particular distribution.
example : honestCommon forcedOld forcedNew ∅ = 3/5 := by decide +kernel
example : ∀ Q : Finset (Fin 3), (2:ℚ)/3 < mass forcedOld Q → 0 ∈ Q := by decide +kernel
example : ∀ Q : Finset (Fin 3), (2:ℚ)/3 < mass forcedNew Q → 0 ∈ Q := by decide +kernel
example : old.n = 2 ∧ next.n = 3 := by decide
example : epochWeights old = forcedOld := by apply funext; decide +kernel
example : epochWeights next = p := by apply funext; decide +kernel
example : epochWeights shuffled = epochWeights old := epoch_reindex_invariance _ _
example : Normalized (epochWeights old) := epochWeights_normalized _ (by decide +kernel)
example : isQuorum (epochWeights old) (4/5) {0, 1} ∧
    isQuorum (epochWeights next) (4/5) {0, 1} := by decide +kernel
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1},
    v ∉ (∅ : Finset (Fin 3)) ∧ v ∈ old.activeIds ∧ v ∈ next.activeIds :=
  epoch_shared_subject old next (by decide +kernel) (by decide +kernel) ∅ {0, 1} {0, 1} (4/5) (4/5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1},
    v ∉ (∅ : Finset (Fin 3)) ∧ 0 < p v ∧ 0 < z v :=
  two_fault_masses_sufficient p z p_normalized z_normalized ∅ {0, 1} {0, 1} (2/3) (2/3)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
example : ∃ v ∈ ({0, 1} : Finset (Fin 3)) ∩ {0, 1}, v ∉ faults ∧ 0 < p v ∧ 0 < z v :=
  variation_sufficient p z p_normalized z_normalized faults {0, 1} {0, 1} (4/5) (4/5)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

#eval [("normalized", decide (Normalized p ∧ Normalized z)),
  ("common mass", decide (honestCommon p z ∅ = 5/6)),
  ("variation", decide (variation p z = 1/6)),
  ("directed loss", decide (honestLoss p z faults = 1/6)),
  ("good quorums", decide (isQuorum p (4/5) {0, 1} ∧ isQuorum z (4/5) {0, 1})),
  ("honest subject", decide ((0 : Fin 3) ∈ honestIntersection faults {0, 1} {0, 1})),
  ("static", decide (variation p p = 0)),
  ("legacy", decide (c.quorum {0, 1})),
  ("boundary split", decide (variation boundaryOld boundaryNew = 1/3 ∧
    honestIntersection (∅ : Finset (Fin 4)) {0, 1} {2, 3} = ∅)),
  ("strict split", decide ((2:ℚ)/3 < mass splitOld {0, 1} ∧ (2:ℚ)/3 < mass splitNew {2, 3})),
  ("fault boundary", decide (honestIntersection ({1} : Finset (Fin 3)) {0, 1} {1, 2} = ∅)),
  ("strict equality", decide (honestCommon p z faults = 2/3 ∧ (2:ℚ)/3 < mass p {0, 1})),
  ("scale", decide (mass (normalize (fun v => 7 * raw v)) {0, 1} = 5/6)),
  ("zero total", decide (¬ Normalized (normalize (fun _ : Fin 3 => (0 : ℚ))))),
  ("negative weight", decide (¬ Normalized (![2, -1, 0] : Fin 3 → ℚ))),
  ("epoch bridge", decide (epochWeights old 0 = 3/5)),
  ("permutation", decide (epochWeights shuffled 0 = epochWeights old 0)),
  ("different size", decide (old.n ≠ next.n)),
  ("not necessary", decide (honestCommon forcedOld forcedNew ∅ < 2/3 ∧
    ∀ Q : Finset (Fin 3), (2:ℚ)/3 < mass forcedOld Q → 0 ∈ Q)),
  ("two faults conservative", decide (mass strong {1} < 1/3 ∧
    ¬ (mass strong {1} + mass strong {1} + variation strong strong < 1/3)))]
end TendermintEpochQuorumRegression
