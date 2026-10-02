/-
Copyright (c) 2026 aicyberg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aicyberg
-/
import Verification.ChipLayoutGeometry
import Lean.Elab.Tactic.Omega

/-!
# Exact certification of the corrected 256-node placement

Bounds, positive dimensions, unique array-index IDs and disjoint closed
rectangles are separate properties. The imported data are explicit rationals;
the generator checks source bytes externally. Lean does not verify JSON parsing
or SHA-256. No routing, optical loss, delay or fabrication rule is certified.
-/

namespace SolarisLayout

-- BEGIN GENERATED MANIFEST DATA
/-- SHA-256 of corrected.json; external provenance, not a verified hash function. -/
def correctedManifestSHA256 : String :=
  "139d8b6d574d18937f0e08cf8c7b1dc4e9c5d6306f5dd7e2070ab769de89975a"

def manifest_die_256 : DieBoundsRat := ⟨4000, 4000⟩

/-- Explicit imported records in array order, in micrometres. -/
def manifest_nodes_256 : List ManifestNodeRat := [
  ⟨0, 125, 125, 15, (5 / 2)⟩,
  ⟨1, 125, 375, 15, (5 / 2)⟩,
  ⟨2, 125, 625, 15, (5 / 2)⟩,
  ⟨3, 125, 875, 15, (5 / 2)⟩,
  ⟨4, 125, 1125, 15, (5 / 2)⟩,
  ⟨5, 125, 1375, 15, (5 / 2)⟩,
  ⟨6, 125, 1625, 15, (5 / 2)⟩,
  ⟨7, 125, 1875, 15, (5 / 2)⟩,
  ⟨8, 125, 2125, 15, (5 / 2)⟩,
  ⟨9, 125, 2375, 15, (5 / 2)⟩,
  ⟨10, 125, 2625, 15, (5 / 2)⟩,
  ⟨11, 125, 2875, 15, (5 / 2)⟩,
  ⟨12, 125, 3125, 15, (5 / 2)⟩,
  ⟨13, 125, 3375, 15, (5 / 2)⟩,
  ⟨14, 125, 3625, 15, (5 / 2)⟩,
  ⟨15, 125, 3875, 15, (5 / 2)⟩,
  ⟨16, 375, 125, 15, (5 / 2)⟩,
  ⟨17, 375, 375, 15, (5 / 2)⟩,
  ⟨18, 375, 625, 15, (5 / 2)⟩,
  ⟨19, 375, 875, 15, (5 / 2)⟩,
  ⟨20, 375, 1125, 15, (5 / 2)⟩,
  ⟨21, 375, 1375, 15, (5 / 2)⟩,
  ⟨22, 375, 1625, 15, (5 / 2)⟩,
  ⟨23, 375, 1875, 15, (5 / 2)⟩,
  ⟨24, 375, 2125, 15, (5 / 2)⟩,
  ⟨25, 375, 2375, 15, (5 / 2)⟩,
  ⟨26, 375, 2625, 15, (5 / 2)⟩,
  ⟨27, 375, 2875, 15, (5 / 2)⟩,
  ⟨28, 375, 3125, 15, (5 / 2)⟩,
  ⟨29, 375, 3375, 15, (5 / 2)⟩,
  ⟨30, 375, 3625, 15, (5 / 2)⟩,
  ⟨31, 375, 3875, 15, (5 / 2)⟩,
  ⟨32, 625, 125, 15, (5 / 2)⟩,
  ⟨33, 625, 375, 15, (5 / 2)⟩,
  ⟨34, 625, 625, 15, (5 / 2)⟩,
  ⟨35, 625, 875, 15, (5 / 2)⟩,
  ⟨36, 625, 1125, 15, (5 / 2)⟩,
  ⟨37, 625, 1375, 15, (5 / 2)⟩,
  ⟨38, 625, 1625, 15, (5 / 2)⟩,
  ⟨39, 625, 1875, 15, (5 / 2)⟩,
  ⟨40, 625, 2125, 15, (5 / 2)⟩,
  ⟨41, 625, 2375, 15, (5 / 2)⟩,
  ⟨42, 625, 2625, 15, (5 / 2)⟩,
  ⟨43, 625, 2875, 15, (5 / 2)⟩,
  ⟨44, 625, 3125, 15, (5 / 2)⟩,
  ⟨45, 625, 3375, 15, (5 / 2)⟩,
  ⟨46, 625, 3625, 15, (5 / 2)⟩,
  ⟨47, 625, 3875, 15, (5 / 2)⟩,
  ⟨48, 875, 125, 15, (5 / 2)⟩,
  ⟨49, 875, 375, 15, (5 / 2)⟩,
  ⟨50, 875, 625, 15, (5 / 2)⟩,
  ⟨51, 875, 875, 15, (5 / 2)⟩,
  ⟨52, 875, 1125, 15, (5 / 2)⟩,
  ⟨53, 875, 1375, 15, (5 / 2)⟩,
  ⟨54, 875, 1625, 15, (5 / 2)⟩,
  ⟨55, 875, 1875, 15, (5 / 2)⟩,
  ⟨56, 875, 2125, 15, (5 / 2)⟩,
  ⟨57, 875, 2375, 15, (5 / 2)⟩,
  ⟨58, 875, 2625, 15, (5 / 2)⟩,
  ⟨59, 875, 2875, 15, (5 / 2)⟩,
  ⟨60, 875, 3125, 15, (5 / 2)⟩,
  ⟨61, 875, 3375, 15, (5 / 2)⟩,
  ⟨62, 875, 3625, 15, (5 / 2)⟩,
  ⟨63, 875, 3875, 15, (5 / 2)⟩,
  ⟨64, 1125, 125, 15, (5 / 2)⟩,
  ⟨65, 1125, 375, 15, (5 / 2)⟩,
  ⟨66, 1125, 625, 15, (5 / 2)⟩,
  ⟨67, 1125, 875, 15, (5 / 2)⟩,
  ⟨68, 1125, 1125, 15, (5 / 2)⟩,
  ⟨69, 1125, 1375, 15, (5 / 2)⟩,
  ⟨70, 1125, 1625, 15, (5 / 2)⟩,
  ⟨71, 1125, 1875, 15, (5 / 2)⟩,
  ⟨72, 1125, 2125, 15, (5 / 2)⟩,
  ⟨73, 1125, 2375, 15, (5 / 2)⟩,
  ⟨74, 1125, 2625, 15, (5 / 2)⟩,
  ⟨75, 1125, 2875, 15, (5 / 2)⟩,
  ⟨76, 1125, 3125, 15, (5 / 2)⟩,
  ⟨77, 1125, 3375, 15, (5 / 2)⟩,
  ⟨78, 1125, 3625, 15, (5 / 2)⟩,
  ⟨79, 1125, 3875, 15, (5 / 2)⟩,
  ⟨80, 1375, 125, 15, (5 / 2)⟩,
  ⟨81, 1375, 375, 15, (5 / 2)⟩,
  ⟨82, 1375, 625, 15, (5 / 2)⟩,
  ⟨83, 1375, 875, 15, (5 / 2)⟩,
  ⟨84, 1375, 1125, 15, (5 / 2)⟩,
  ⟨85, 1375, 1375, 15, (5 / 2)⟩,
  ⟨86, 1375, 1625, 15, (5 / 2)⟩,
  ⟨87, 1375, 1875, 15, (5 / 2)⟩,
  ⟨88, 1375, 2125, 15, (5 / 2)⟩,
  ⟨89, 1375, 2375, 15, (5 / 2)⟩,
  ⟨90, 1375, 2625, 15, (5 / 2)⟩,
  ⟨91, 1375, 2875, 15, (5 / 2)⟩,
  ⟨92, 1375, 3125, 15, (5 / 2)⟩,
  ⟨93, 1375, 3375, 15, (5 / 2)⟩,
  ⟨94, 1375, 3625, 15, (5 / 2)⟩,
  ⟨95, 1375, 3875, 15, (5 / 2)⟩,
  ⟨96, 1625, 125, 15, (5 / 2)⟩,
  ⟨97, 1625, 375, 15, (5 / 2)⟩,
  ⟨98, 1625, 625, 15, (5 / 2)⟩,
  ⟨99, 1625, 875, 15, (5 / 2)⟩,
  ⟨100, 1625, 1125, 15, (5 / 2)⟩,
  ⟨101, 1625, 1375, 15, (5 / 2)⟩,
  ⟨102, 1625, 1625, 15, (5 / 2)⟩,
  ⟨103, 1625, 1875, 15, (5 / 2)⟩,
  ⟨104, 1625, 2125, 15, (5 / 2)⟩,
  ⟨105, 1625, 2375, 15, (5 / 2)⟩,
  ⟨106, 1625, 2625, 15, (5 / 2)⟩,
  ⟨107, 1625, 2875, 15, (5 / 2)⟩,
  ⟨108, 1625, 3125, 15, (5 / 2)⟩,
  ⟨109, 1625, 3375, 15, (5 / 2)⟩,
  ⟨110, 1625, 3625, 15, (5 / 2)⟩,
  ⟨111, 1625, 3875, 15, (5 / 2)⟩,
  ⟨112, 1875, 125, 15, (5 / 2)⟩,
  ⟨113, 1875, 375, 15, (5 / 2)⟩,
  ⟨114, 1875, 625, 15, (5 / 2)⟩,
  ⟨115, 1875, 875, 15, (5 / 2)⟩,
  ⟨116, 1875, 1125, 15, (5 / 2)⟩,
  ⟨117, 1875, 1375, 15, (5 / 2)⟩,
  ⟨118, 1875, 1625, 15, (5 / 2)⟩,
  ⟨119, 1875, 1875, 15, (5 / 2)⟩,
  ⟨120, 1875, 2125, 15, (5 / 2)⟩,
  ⟨121, 1875, 2375, 15, (5 / 2)⟩,
  ⟨122, 1875, 2625, 15, (5 / 2)⟩,
  ⟨123, 1875, 2875, 15, (5 / 2)⟩,
  ⟨124, 1875, 3125, 15, (5 / 2)⟩,
  ⟨125, 1875, 3375, 15, (5 / 2)⟩,
  ⟨126, 1875, 3625, 15, (5 / 2)⟩,
  ⟨127, 1875, 3875, 15, (5 / 2)⟩,
  ⟨128, 2125, 125, 15, (5 / 2)⟩,
  ⟨129, 2125, 375, 15, (5 / 2)⟩,
  ⟨130, 2125, 625, 15, (5 / 2)⟩,
  ⟨131, 2125, 875, 15, (5 / 2)⟩,
  ⟨132, 2125, 1125, 15, (5 / 2)⟩,
  ⟨133, 2125, 1375, 15, (5 / 2)⟩,
  ⟨134, 2125, 1625, 15, (5 / 2)⟩,
  ⟨135, 2125, 1875, 15, (5 / 2)⟩,
  ⟨136, 2125, 2125, 15, (5 / 2)⟩,
  ⟨137, 2125, 2375, 15, (5 / 2)⟩,
  ⟨138, 2125, 2625, 15, (5 / 2)⟩,
  ⟨139, 2125, 2875, 15, (5 / 2)⟩,
  ⟨140, 2125, 3125, 15, (5 / 2)⟩,
  ⟨141, 2125, 3375, 15, (5 / 2)⟩,
  ⟨142, 2125, 3625, 15, (5 / 2)⟩,
  ⟨143, 2125, 3875, 15, (5 / 2)⟩,
  ⟨144, 2375, 125, 15, (5 / 2)⟩,
  ⟨145, 2375, 375, 15, (5 / 2)⟩,
  ⟨146, 2375, 625, 15, (5 / 2)⟩,
  ⟨147, 2375, 875, 15, (5 / 2)⟩,
  ⟨148, 2375, 1125, 15, (5 / 2)⟩,
  ⟨149, 2375, 1375, 15, (5 / 2)⟩,
  ⟨150, 2375, 1625, 15, (5 / 2)⟩,
  ⟨151, 2375, 1875, 15, (5 / 2)⟩,
  ⟨152, 2375, 2125, 15, (5 / 2)⟩,
  ⟨153, 2375, 2375, 15, (5 / 2)⟩,
  ⟨154, 2375, 2625, 15, (5 / 2)⟩,
  ⟨155, 2375, 2875, 15, (5 / 2)⟩,
  ⟨156, 2375, 3125, 15, (5 / 2)⟩,
  ⟨157, 2375, 3375, 15, (5 / 2)⟩,
  ⟨158, 2375, 3625, 15, (5 / 2)⟩,
  ⟨159, 2375, 3875, 15, (5 / 2)⟩,
  ⟨160, 2625, 125, 15, (5 / 2)⟩,
  ⟨161, 2625, 375, 15, (5 / 2)⟩,
  ⟨162, 2625, 625, 15, (5 / 2)⟩,
  ⟨163, 2625, 875, 15, (5 / 2)⟩,
  ⟨164, 2625, 1125, 15, (5 / 2)⟩,
  ⟨165, 2625, 1375, 15, (5 / 2)⟩,
  ⟨166, 2625, 1625, 15, (5 / 2)⟩,
  ⟨167, 2625, 1875, 15, (5 / 2)⟩,
  ⟨168, 2625, 2125, 15, (5 / 2)⟩,
  ⟨169, 2625, 2375, 15, (5 / 2)⟩,
  ⟨170, 2625, 2625, 15, (5 / 2)⟩,
  ⟨171, 2625, 2875, 15, (5 / 2)⟩,
  ⟨172, 2625, 3125, 15, (5 / 2)⟩,
  ⟨173, 2625, 3375, 15, (5 / 2)⟩,
  ⟨174, 2625, 3625, 15, (5 / 2)⟩,
  ⟨175, 2625, 3875, 15, (5 / 2)⟩,
  ⟨176, 2875, 125, 15, (5 / 2)⟩,
  ⟨177, 2875, 375, 15, (5 / 2)⟩,
  ⟨178, 2875, 625, 15, (5 / 2)⟩,
  ⟨179, 2875, 875, 15, (5 / 2)⟩,
  ⟨180, 2875, 1125, 15, (5 / 2)⟩,
  ⟨181, 2875, 1375, 15, (5 / 2)⟩,
  ⟨182, 2875, 1625, 15, (5 / 2)⟩,
  ⟨183, 2875, 1875, 15, (5 / 2)⟩,
  ⟨184, 2875, 2125, 15, (5 / 2)⟩,
  ⟨185, 2875, 2375, 15, (5 / 2)⟩,
  ⟨186, 2875, 2625, 15, (5 / 2)⟩,
  ⟨187, 2875, 2875, 15, (5 / 2)⟩,
  ⟨188, 2875, 3125, 15, (5 / 2)⟩,
  ⟨189, 2875, 3375, 15, (5 / 2)⟩,
  ⟨190, 2875, 3625, 15, (5 / 2)⟩,
  ⟨191, 2875, 3875, 15, (5 / 2)⟩,
  ⟨192, 3125, 125, 15, (5 / 2)⟩,
  ⟨193, 3125, 375, 15, (5 / 2)⟩,
  ⟨194, 3125, 625, 15, (5 / 2)⟩,
  ⟨195, 3125, 875, 15, (5 / 2)⟩,
  ⟨196, 3125, 1125, 15, (5 / 2)⟩,
  ⟨197, 3125, 1375, 15, (5 / 2)⟩,
  ⟨198, 3125, 1625, 15, (5 / 2)⟩,
  ⟨199, 3125, 1875, 15, (5 / 2)⟩,
  ⟨200, 3125, 2125, 15, (5 / 2)⟩,
  ⟨201, 3125, 2375, 15, (5 / 2)⟩,
  ⟨202, 3125, 2625, 15, (5 / 2)⟩,
  ⟨203, 3125, 2875, 15, (5 / 2)⟩,
  ⟨204, 3125, 3125, 15, (5 / 2)⟩,
  ⟨205, 3125, 3375, 15, (5 / 2)⟩,
  ⟨206, 3125, 3625, 15, (5 / 2)⟩,
  ⟨207, 3125, 3875, 15, (5 / 2)⟩,
  ⟨208, 3375, 125, 15, (5 / 2)⟩,
  ⟨209, 3375, 375, 15, (5 / 2)⟩,
  ⟨210, 3375, 625, 15, (5 / 2)⟩,
  ⟨211, 3375, 875, 15, (5 / 2)⟩,
  ⟨212, 3375, 1125, 15, (5 / 2)⟩,
  ⟨213, 3375, 1375, 15, (5 / 2)⟩,
  ⟨214, 3375, 1625, 15, (5 / 2)⟩,
  ⟨215, 3375, 1875, 15, (5 / 2)⟩,
  ⟨216, 3375, 2125, 15, (5 / 2)⟩,
  ⟨217, 3375, 2375, 15, (5 / 2)⟩,
  ⟨218, 3375, 2625, 15, (5 / 2)⟩,
  ⟨219, 3375, 2875, 15, (5 / 2)⟩,
  ⟨220, 3375, 3125, 15, (5 / 2)⟩,
  ⟨221, 3375, 3375, 15, (5 / 2)⟩,
  ⟨222, 3375, 3625, 15, (5 / 2)⟩,
  ⟨223, 3375, 3875, 15, (5 / 2)⟩,
  ⟨224, 3625, 125, 15, (5 / 2)⟩,
  ⟨225, 3625, 375, 15, (5 / 2)⟩,
  ⟨226, 3625, 625, 15, (5 / 2)⟩,
  ⟨227, 3625, 875, 15, (5 / 2)⟩,
  ⟨228, 3625, 1125, 15, (5 / 2)⟩,
  ⟨229, 3625, 1375, 15, (5 / 2)⟩,
  ⟨230, 3625, 1625, 15, (5 / 2)⟩,
  ⟨231, 3625, 1875, 15, (5 / 2)⟩,
  ⟨232, 3625, 2125, 15, (5 / 2)⟩,
  ⟨233, 3625, 2375, 15, (5 / 2)⟩,
  ⟨234, 3625, 2625, 15, (5 / 2)⟩,
  ⟨235, 3625, 2875, 15, (5 / 2)⟩,
  ⟨236, 3625, 3125, 15, (5 / 2)⟩,
  ⟨237, 3625, 3375, 15, (5 / 2)⟩,
  ⟨238, 3625, 3625, 15, (5 / 2)⟩,
  ⟨239, 3625, 3875, 15, (5 / 2)⟩,
  ⟨240, 3875, 125, 15, (5 / 2)⟩,
  ⟨241, 3875, 375, 15, (5 / 2)⟩,
  ⟨242, 3875, 625, 15, (5 / 2)⟩,
  ⟨243, 3875, 875, 15, (5 / 2)⟩,
  ⟨244, 3875, 1125, 15, (5 / 2)⟩,
  ⟨245, 3875, 1375, 15, (5 / 2)⟩,
  ⟨246, 3875, 1625, 15, (5 / 2)⟩,
  ⟨247, 3875, 1875, 15, (5 / 2)⟩,
  ⟨248, 3875, 2125, 15, (5 / 2)⟩,
  ⟨249, 3875, 2375, 15, (5 / 2)⟩,
  ⟨250, 3875, 2625, 15, (5 / 2)⟩,
  ⟨251, 3875, 2875, 15, (5 / 2)⟩,
  ⟨252, 3875, 3125, 15, (5 / 2)⟩,
  ⟨253, 3875, 3375, 15, (5 / 2)⟩,
  ⟨254, 3875, 3625, 15, (5 / 2)⟩,
  ⟨255, 3875, 3875, 15, (5 / 2)⟩
]
-- END GENERATED MANIFEST DATA

/-- Nonempty, positive-size, unique-ID bounds check. Does not test separation. -/
def validPlacement (nodes : List ManifestNodeRat) (die : DieBoundsRat) : Bool :=
  decide (nodes ≠ [] ∧ 0 < die.W ∧ 0 < die.H ∧
    (nodes.map ManifestNodeRat.id).Nodup) &&
  nodes.all (fun n => decide (0 < n.w ∧ 0 < n.h)) && validateLayoutManifest nodes die

/-- Strict edge separation excludes even boundary contact between closed rectangles. -/
def ClosedSeparatedRat (a b : ManifestNodeRat) : Prop :=
  a.x + a.w / 2 < b.x - b.w / 2 ∨ b.x + b.w / 2 < a.x - a.w / 2 ∨
  a.y + a.h / 2 < b.y - b.h / 2 ∨ b.y + b.h / 2 < a.y - a.h / 2

instance (a b : ManifestNodeRat) : Decidable (ClosedSeparatedRat a b) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

/-- Membership of a real point in the closed rectangle, including its boundary. -/
def inClosedRectangle (p : Point2D) (n : RectNode) : Prop :=
  n.x - n.w / 2 ≤ p.x ∧ p.x ≤ n.x + n.w / 2 ∧
  n.y - n.h / 2 ≤ p.y ∧ p.y ≤ n.y + n.h / 2

/-- Rational strict separation implies actual disjointness over the real plane. -/
theorem closedSeparatedRat_sound (a b : ManifestNodeRat) (h : ClosedSeparatedRat a b) :
    ∀ p : Point2D, ¬ (inClosedRectangle p a.toReal ∧ inClosedRectangle p b.toReal) := by
  intro p ⟨ha, hb⟩
  dsimp [inClosedRectangle, ManifestNodeRat.toReal] at ha hb
  have hreal : (a.x : ℝ) + a.w / 2 < (b.x : ℝ) - b.w / 2 ∨
      (b.x : ℝ) + b.w / 2 < (a.x : ℝ) - a.w / 2 ∨
      (a.y : ℝ) + a.h / 2 < (b.y : ℝ) - b.h / 2 ∨
      (b.y : ℝ) + b.h / 2 < (a.y : ℝ) - a.h / 2 := by
    exact_mod_cast h
  rcases ha with ⟨ha1, ha2, ha3, ha4⟩
  rcases hb with ⟨hb1, hb2, hb3, hb4⟩
  rcases hreal with h | h | h | h <;> linarith

/-- Checked shape witness for every explicit record, not a replacement data generator. -/
def onPlacementGrid (n : ManifestNodeRat) : Prop :=
  n.x = 125 + 250 * ((n.id / 16 : ℕ) : ℚ) ∧
  n.y = 125 + 250 * ((n.id % 16 : ℕ) : ℚ) ∧ n.w = 15 ∧ n.h = 5 / 2

instance (n : ManifestNodeRat) : Decidable (onPlacementGrid n) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Algebraic proof covers every pair, using the checked exact shape of each record. -/
theorem grid_nodes_separated (a b : ManifestNodeRat)
    (ha : onPlacementGrid a) (hb : onPlacementGrid b) (hne : a.id ≠ b.id) :
    ClosedSeparatedRat a b := by
  rcases ha with ⟨hax, hay, haw, hah⟩
  rcases hb with ⟨hbx, hby, hbw, hbh⟩
  have cases : a.id / 16 < b.id / 16 ∨ b.id / 16 < a.id / 16 ∨
      a.id % 16 < b.id % 16 ∨ b.id % 16 < a.id % 16 := by omega
  dsimp [ClosedSeparatedRat]
  rw [hax, hay, haw, hah, hbx, hby, hbw, hbh]
  rcases cases with h | h | h | h
  · have hq : ((a.id / 16 : ℕ) : ℚ) + 1 ≤ ((b.id / 16 : ℕ) : ℚ) := by
      exact_mod_cast h
    left; linarith
  · have hq : ((b.id / 16 : ℕ) : ℚ) + 1 ≤ ((a.id / 16 : ℕ) : ℚ) := by
      exact_mod_cast h
    right; left; linarith
  · have hq : ((a.id % 16 : ℕ) : ℚ) + 1 ≤ ((b.id % 16 : ℕ) : ℚ) := by
      exact_mod_cast h
    right; right; left; linarith
  · have hq : ((b.id % 16 : ℕ) : ℚ) + 1 ≤ ((a.id % 16 : ℕ) : ℚ) := by
      exact_mod_cast h
    right; right; right; linarith

/-- Literal list length, checked by the kernel. -/
theorem manifest_count : manifest_nodes_256.length = 256 := by decide +kernel

theorem manifest_ids_unique : (manifest_nodes_256.map ManifestNodeRat.id).Nodup := by
  decide +kernel

theorem manifest_die_positive : 0 < manifest_die_256.W ∧ 0 < manifest_die_256.H := by
  decide +kernel

theorem manifest_dimensions_positive :
    ∀ n ∈ manifest_nodes_256, 0 < n.w ∧ 0 < n.h := by
  have h : manifest_nodes_256.all (fun n => decide (0 < n.w ∧ 0 < n.h)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem manifest_bounds_checked :
    validateLayoutManifest manifest_nodes_256 manifest_die_256 = true := by
  decide +kernel

theorem manifest_valid : validPlacement manifest_nodes_256 manifest_die_256 = true := by
  decide +kernel

/-- The grid identity is checked against all 256 explicit imported records. -/
theorem manifest_on_grid : ∀ n ∈ manifest_nodes_256, onPlacementGrid n := by
  have h : manifest_nodes_256.all (fun n => decide (onPlacementGrid n)) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem manifest_all_contained : ∀ n ∈ manifest_nodes_256,
    is_contained n.toReal manifest_die_256.toReal :=
  validateLayoutManifest_sound_real _ _ manifest_bounds_checked

theorem manifest_pairwise_separated (a b : ManifestNodeRat)
    (ha : a ∈ manifest_nodes_256) (hb : b ∈ manifest_nodes_256) (hne : a ≠ b) :
    ClosedSeparatedRat a b := by
  have hag := manifest_on_grid a ha
  have hbg := manifest_on_grid b hb
  apply grid_nodes_separated a b hag hbg
  intro hi
  apply hne
  rcases a with ⟨ai, ax, ay, aw, ah⟩
  rcases b with ⟨bi, bx, by_, bw, bh⟩
  dsimp [onPlacementGrid] at hag hbg
  obtain rfl := hi
  rcases hag with ⟨rfl, rfl, rfl, rfl⟩
  rcases hbg with ⟨rfl, rfl, rfl, rfl⟩
  rfl

theorem manifest_closed_rectangles_disjoint (a b : ManifestNodeRat)
    (ha : a ∈ manifest_nodes_256) (hb : b ∈ manifest_nodes_256) (hne : a ≠ b) :
    ∀ p : Point2D, ¬ (inClosedRectangle p a.toReal ∧ inClosedRectangle p b.toReal) :=
  closedSeparatedRat_sound a b (manifest_pairwise_separated a b ha hb hne)

/-- Bounds-only certificate; stronger properties are stated separately above. -/
def certifiedPlacement256 : CertifiedPlacementManifest :=
  ⟨correctedManifestSHA256, manifest_nodes_256, manifest_die_256, manifest_bounds_checked⟩

-- Regression cases distinguish bounds contact from rectangle-to-rectangle contact.
example : validPlacement [⟨0, 1, 1, 2, 2⟩] ⟨2, 2⟩ = true := by decide +kernel
example : validPlacement [⟨0, 1001 / 1000, 1, 2, 2⟩] ⟨2, 2⟩ = false := by decide +kernel
example : validPlacement [⟨0, 1, 1, -2, 2⟩] ⟨2, 2⟩ = false := by decide +kernel
example : validPlacement [] ⟨2, 2⟩ = false := by decide +kernel
example : validPlacement [⟨0, 1, 1, 2, 2⟩, ⟨0, 1, 1, 2, 2⟩] ⟨2, 2⟩ = false := by
  decide +kernel
example : ¬ ClosedSeparatedRat ⟨0, 1, 1, 2, 2⟩ ⟨1, 3, 1, 2, 2⟩ := by decide +kernel
example : ¬ ClosedSeparatedRat ⟨0, 1, 1, 2, 2⟩ ⟨1, 2, 1, 2, 2⟩ := by decide +kernel

structure ChipPlacementCertificateSuite : Prop where
  h_count : manifest_nodes_256.length = 256
  h_ids : (manifest_nodes_256.map ManifestNodeRat.id).Nodup
  h_die : 0 < manifest_die_256.W ∧ 0 < manifest_die_256.H
  h_dimensions : ∀ n ∈ manifest_nodes_256, 0 < n.w ∧ 0 < n.h
  h_bounds : validateLayoutManifest manifest_nodes_256 manifest_die_256 = true
  h_real_bounds : ∀ n ∈ manifest_nodes_256, is_contained n.toReal manifest_die_256.toReal
  h_disjoint : ∀ a ∈ manifest_nodes_256, ∀ b ∈ manifest_nodes_256, a ≠ b →
    ∀ p : Point2D, ¬ (inClosedRectangle p a.toReal ∧ inClosedRectangle p b.toReal)

theorem chip_placement_certificate_master_suite : ChipPlacementCertificateSuite := {
  h_count := manifest_count
  h_ids := manifest_ids_unique
  h_die := manifest_die_positive
  h_dimensions := manifest_dimensions_positive
  h_bounds := manifest_bounds_checked
  h_real_bounds := manifest_all_contained
  h_disjoint := fun a ha b hb hne => manifest_closed_rectangles_disjoint a b ha hb hne
}

end SolarisLayout
