/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Translation and rectangular placement bounds

Universal identities and an exact rational bounds checker. No particular JSON
manifest is imported here. A stored SHA-256 string is metadata, not a proof that
the certified rational data was obtained from the bytes bearing that digest.
Boundary contact is allowed. Physical rectangle interpretation requires
nonnegative dimensions, which the bounds-only checker does not enforce.
-/

namespace SolarisLayout

structure Point2D where
  x : ℝ
  y : ℝ

noncomputable def translate (p t : Point2D) : Point2D :=
  ⟨p.x + t.x, p.y + t.y⟩

noncomputable def distSq (p1 p2 : Point2D) : ℝ :=
  (p1.x - p2.x) ^ 2 + (p1.y - p2.y) ^ 2

/-- The Euclidean distance, not the maximum metric on a Cartesian product. -/
noncomputable def euclideanDist (p1 p2 : Point2D) : ℝ :=
  Real.sqrt (distSq p1 p2)

theorem translation_preserves_distSq (p1 p2 t : Point2D) :
    distSq (translate p1 t) (translate p2 t) = distSq p1 p2 := by
  dsimp [distSq, translate]
  ring

theorem translation_preserves_distance (p1 p2 t : Point2D) :
    euclideanDist (translate p1 t) (translate p2 t) = euclideanDist p1 p2 := by
  unfold euclideanDist
  rw [translation_preserves_distSq]

structure RectNode where
  x : ℝ
  y : ℝ
  w : ℝ
  h : ℝ

structure DieBounds where
  W : ℝ
  H : ℝ

/-- Four edge inequalities for the closed die [0,W] × [0,H]. -/
def is_contained (node : RectNode) (die : DieBounds) : Prop :=
  0 ≤ node.x - node.w / 2 ∧ node.x + node.w / 2 ≤ die.W ∧
  0 ≤ node.y - node.h / 2 ∧ node.y + node.h / 2 ≤ die.H

theorem center_bounds_iff_contained (node : RectNode) (die : DieBounds) :
    is_contained node die ↔
      (node.w / 2 ≤ node.x ∧ node.x ≤ die.W - node.w / 2 ∧
       node.h / 2 ≤ node.y ∧ node.y ≤ die.H - node.h / 2) := by
  dsimp [is_contained]
  constructor <;> rintro ⟨hx0, hxW, hy0, hyH⟩ <;>
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

structure ManifestNodeRat where
  id : ℕ
  x : ℚ
  y : ℚ
  w : ℚ
  h : ℚ
  deriving DecidableEq, Repr

structure DieBoundsRat where
  W : ℚ
  H : ℚ
  deriving DecidableEq, Repr

/-- Exact center inequalities. This predicate does not check dimension signs. -/
def nodeFitsRat (n : ManifestNodeRat) (d : DieBoundsRat) : Bool :=
  decide (n.w / 2 ≤ n.x ∧ n.x ≤ d.W - n.w / 2 ∧
    n.h / 2 ≤ n.y ∧ n.y ≤ d.H - n.h / 2)

def validateLayoutManifest (nodes : List ManifestNodeRat) (d : DieBoundsRat) : Bool :=
  nodes.all (fun n => nodeFitsRat n d)

theorem validateLayoutManifest_iff (nodes : List ManifestNodeRat) (d : DieBoundsRat) :
    validateLayoutManifest nodes d = true ↔
      ∀ n ∈ nodes, (n.w / 2 ≤ n.x ∧ n.x ≤ d.W - n.w / 2 ∧
        n.h / 2 ≤ n.y ∧ n.y ≤ d.H - n.h / 2) := by
  simp [validateLayoutManifest, nodeFitsRat, List.all_eq_true]

theorem validateLayoutManifest_sound (nodes : List ManifestNodeRat) (d : DieBoundsRat)
    (h_val : validateLayoutManifest nodes d = true) :
    ∀ n ∈ nodes, (n.w / 2 ≤ n.x ∧ n.x ≤ d.W - n.w / 2 ∧
      n.h / 2 ≤ n.y ∧ n.y ≤ d.H - n.h / 2) :=
  (validateLayoutManifest_iff nodes d).mp h_val

noncomputable def ManifestNodeRat.toReal (n : ManifestNodeRat) : RectNode :=
  ⟨n.x, n.y, n.w, n.h⟩

noncomputable def DieBoundsRat.toReal (d : DieBoundsRat) : DieBounds :=
  ⟨d.W, d.H⟩

/-- Exact rational embedding, without rounding or numerical tolerance. -/
theorem nodeFitsRat_iff_real (n : ManifestNodeRat) (d : DieBoundsRat) :
    nodeFitsRat n d = true ↔ is_contained n.toReal d.toReal := by
  rw [center_bounds_iff_contained]
  simp only [nodeFitsRat, decide_eq_true_eq, ManifestNodeRat.toReal, DieBoundsRat.toReal]
  norm_cast

theorem validateLayoutManifest_sound_real (nodes : List ManifestNodeRat) (d : DieBoundsRat)
    (h_val : validateLayoutManifest nodes d = true) :
    ∀ n ∈ nodes, is_contained n.toReal d.toReal := by
  intro n hn
  apply (nodeFitsRat_iff_real n d).mp
  exact (List.all_eq_true.mp h_val) n hn

/-- Bounds-certified data; sha256 is an unchecked provenance label, not a hash binding. -/
structure CertifiedPlacementManifest where
  sha256 : String
  nodes : List ManifestNodeRat
  die : DieBoundsRat
  h_all_fit : validateLayoutManifest nodes die = true

theorem CertifiedPlacementManifest.all_contained (m : CertifiedPlacementManifest) :
    ∀ n ∈ m.nodes, is_contained n.toReal m.die.toReal :=
  validateLayoutManifest_sound_real m.nodes m.die m.h_all_fit

/-- Small regression examples; these are not the simulation's 256-node manifest. -/
example : validateLayoutManifest [⟨0, 1, 1, 2, 2⟩] ⟨2, 2⟩ = true := by decide +kernel

example : validateLayoutManifest [⟨0, 2, 1, 2, 2⟩] ⟨2, 2⟩ = false := by decide +kernel

example : validateLayoutManifest ([] : List ManifestNodeRat) ⟨2, 2⟩ = true := by decide

structure ChipLayoutGeometryFormalSuite : Prop where
  h_translation_sq : ∀ p1 p2 t, distSq (translate p1 t) (translate p2 t) = distSq p1 p2
  h_translation_dist : ∀ p1 p2 t,
    euclideanDist (translate p1 t) (translate p2 t) = euclideanDist p1 p2
  h_center_bounds : ∀ node die, is_contained node die ↔
    (node.w / 2 ≤ node.x ∧ node.x ≤ die.W - node.w / 2 ∧
      node.h / 2 ≤ node.y ∧ node.y ≤ die.H - node.h / 2)
  h_validator : ∀ nodes die, validateLayoutManifest nodes die = true ↔
    ∀ n ∈ nodes, (n.w / 2 ≤ n.x ∧ n.x ≤ die.W - n.w / 2 ∧
      n.h / 2 ≤ n.y ∧ n.y ≤ die.H - n.h / 2)
  h_real_bounds : ∀ nodes die, validateLayoutManifest nodes die = true →
    ∀ n ∈ nodes, is_contained n.toReal die.toReal

theorem chip_layout_geometry_master_suite : ChipLayoutGeometryFormalSuite := {
  h_translation_sq := translation_preserves_distSq
  h_translation_dist := translation_preserves_distance
  h_center_bounds := center_bounds_iff_contained
  h_validator := validateLayoutManifest_iff
  h_real_bounds := validateLayoutManifest_sound_real
}

end SolarisLayout
