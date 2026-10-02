---
id: ChipLayoutGeometry
language: en
section: quantum-physics
source: Verification/ChipLayoutGeometry.lean
source_sha256: e89d4dd29d86901037b766f572773ef786be264763de13dbc95af96d813d87ae
novelty: not-assessed
status: reviewed
---

# ChipLayoutGeometry

[Section](../quantum-physics/README.md) · [Lean](../../Verification/ChipLayoutGeometry.lean)

## Universal geometry

`translation_preserves_distSq` proves preservation of squared Euclidean distance
under a common translation of two real-coordinate points. `euclideanDist` is the
square root of this squared distance, and `translation_preserves_distance`
proves preservation of that distance as well. This is not the maximum metric on
an unqualified Cartesian product.

`center_bounds_iff_contained` equates the four edge inequalities with the four
center bounds: `w/2 ≤ x ≤ W-w/2` and `h/2 ≤ y ≤ H-h/2`. Coordinates use a closed
die `[0,W] × [0,H]`; boundary contact is allowed. The inequalities make algebraic
sense for arbitrary reals. Their interpretation as bounds of an axis-aligned
rectangle requires nonnegative width and height, and a physical die needs
valid dimensions. These sign conditions are not checked by this bounds-only validator.

## Rational checker and its real interpretation

`nodeFitsRat` uses `decide` on the exact rational center inequalities.
`validateLayoutManifest` applies it to every node in a finite list.
`validateLayoutManifest_iff` proves both soundness and completeness for precisely
these inequalities; `validateLayoutManifest_sound` exposes the forward direction.
`nodeFitsRat_iff_real` and `validateLayoutManifest_sound_real` prove that the same
bounds hold after exact rational-to-real embedding. No approximation or numerical
tolerance appears in these statements.

Small kernel-checked examples cover a rectangle touching all die boundaries,
an out-of-bounds rectangle, and the empty list. The nonempty examples use
`decide +kernel`, with no native evaluation shortcut. They are regression
examples, not the 256-node simulation artifact. Empty input passes by design;
node count, ID uniqueness, dimension signs, pairwise nonintersection, and design
rule spacing are not validated.

## Certificate and provenance boundary

`CertifiedPlacementManifest` stores rational data and a proof that the checker
returns true. `all_contained` derives the real edge inequalities for each node.
Its `sha256 : String` is an **unchecked provenance label**: Lean does not prove
that the string is a valid SHA-256 digest, that it hashes an external file, or
that the stored data was parsed from that file.

This module imports no simulation JSON and certifies no particular 256-node
placement or 4 mm die. The separate [ChipPlacementCertificate](ChipPlacementCertificate.md)
module supplies concrete exact records and proofs of bounds, positive dimensions,
unique IDs, and pairwise nonintersection. Its published inputs and deterministic
converter provide an external provenance check. Parsing and hashing remain
outside Lean's proof boundary. If approximate coordinates are used in another
application, an error-margin argument is needed to transfer bounds to its original data.

The general translation theorem alone does not prove that a translated placement
fits a die. Ports, routing, physical path lengths, optical losses, delays, thermal
behavior, and fabrication rules are absent. Novelty is not assessed.

## Integration and verification

The suite is `SolarisLayout.ChipLayoutGeometryFormalSuite`, with theorem
`chip_layout_geometry_master_suite`, integrated as `PhotonicsInterposerFullSuite.chip_layout`.
The module passed `verifier_skill.py verify` and `audit`. Allowed dependencies are
`propext`, `Classical.choice`, and `Quot.sound`; this is not a claim that every
analytical theorem is axiom-free. See the [validation record](../VERIFICATION.en.md).
