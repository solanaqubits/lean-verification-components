---
id: ChipPlacementCertificate
language: en
section: quantum-physics
source: Verification/ChipPlacementCertificate.lean
source_sha256: 0f2630c29d8273c5c0d1010edad4096b1d0b3866393d84fe33e265e649caab3b
novelty: not-assessed
status: reviewed
---

# ChipPlacementCertificate

[Section](../quantum-physics/README.md) · [Lean](../../Verification/ChipPlacementCertificate.lean)

## Concrete data and statements

The module embeds an explicit list of 256 axis-aligned rectangles with exact
rational centre coordinates and dimensions, in micrometres, relative to the die
origin. The die is the closed rectangle `[0,4000] × [0,4000]`. IDs are positions
in the input array, not authenticated persistent hardware identifiers.

The certificate separates these properties:

- `manifest_count`: the list has exactly 256 records.
- `manifest_die_positive` and `manifest_dimensions_positive`: the die and every
  rectangle have strictly positive dimensions.
- `manifest_ids_unique`: all node IDs are unique.
- `manifest_bounds_checked`: every rectangle is contained in the die, using the exact rational checker
  from [ChipLayoutGeometry](ChipLayoutGeometry.md). The containment result also
  holds after exact embedding into real coordinates (`manifest_all_contained`).
- `manifest_closed_rectangles_disjoint`: distinct records describe disjoint closed
  rectangles. The separation
  predicate uses a strict gap along at least one coordinate axis. This excludes
  even boundary contact between nodes; it is stronger than disjoint interiors.

Containment alone does not imply nonintersection. The separate pairwise result
supplies that guarantee for these records. Neither a minimum fabrication gap nor
an arbitrary foundry rule set follows from these statements.

`manifest_nodes_256` is the explicit imported list; it is not replaced by a
formula-generated grid. Kernel computation (`decide +kernel`) checks its finite
properties, including `manifest_on_grid`. The algebraic theorem
`grid_nodes_separated` then proves separation of every distinct pair using that
checked shape; this does not enumerate 32,640 pairwise numerical distances.
`closedSeparatedRat_sound` transfers strict rational edge separation to actual
nonintersection over the real plane.

`validPlacement` checks nonempty input, positive die and node dimensions, unique
IDs, and bounds. It does not check pairwise separation or require exactly 256 nodes.
The concrete count and separation are additional theorems. Likewise,
`certifiedPlacement256` is a bounds-only certificate object; its stronger
properties are exposed by the suite.

The suite is `SolarisLayout.ChipPlacementCertificateSuite`, instantiated by
`chip_placement_certificate_master_suite`.

## Input provenance and reproduction

The published [corrected manifest](../../data/chip_manifest/corrected.json) has SHA-256:

`139d8b6d574d18937f0e08cf8c7b1dc4e9c5d6306f5dd7e2070ab769de89975a`

The [original manifest](../../data/chip_manifest/original.json) and
[exact rational export](../../data/chip_manifest/rational_data.json) are retained
as provenance evidence. The [deterministic converter](../../scripts/generate_chip_manifest.py)
pins the three input digests, parses decimal JSON numbers exactly, checks units,
coordinate conventions, die dimensions, array order and origin normalization,
and compares every rational coordinate and size with its source. It also checks
the common `(-125,-125)` micrometre correction and preservation of sizes and IDs.

From the repository root, reproduce the conversion check without writing files:

```bash
python3 scripts/generate_chip_manifest.py --check
```

This command checks external bytes and the embedded Lean data block. It is not a
Lean theorem about parsing or SHA-256. The formal certificate applies to the
explicit Lean records; trusting their correspondence to external JSON requires
the published converter, Python runtime, and digest check. The string stored in
Lean is provenance metadata, not a verified hash function.

## Boundaries and verification

Exact rational values need no floating-point tolerance. The proofs do not certify
ports, waveguide routes, physical path lengths, optical loss, delay, thermal
behaviour, material parameters, manufacturing yield, or hardware performance.
The original out-of-bounds placement is retained as input evidence, not certified
as contained. No numerical simulator run constitutes a Lean proof.

Strict module verification, audit, integration and the full project checks passed; see the
[validation record](../VERIFICATION.en.md). Scientific novelty is not assessed.
