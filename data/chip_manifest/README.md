# Exact placement inputs

These three byte-preserved JSON files are the publication inputs for
`Verification/ChipPlacementCertificate.lean`. They come from the frozen simulation
handoff dated 2026-10-02. Only placement fields are certified; other source JSON
fields (including descriptions of optical components) are not validated physics.

Run from the repository root:

```bash
python3 scripts/generate_chip_manifest.py --check
python3 -m unittest discover -s tests -p test_chip_manifest.py -v
```

Without `--check`, the generator replaces only the marked literal data block in
the Lean source. It verifies pinned SHA-256 digests, parses decimal values with
`Decimal` and `Fraction`, and compares every ID, centre, width and height against
the original JSON in array order. IDs are assigned array indices, not physical
identities. Both die dimensions and the die-local origin are checked. The
corrected coordinates differ from the original by exactly (-125,-125) micrometres;
node sizes and array order are unchanged.

| File | SHA-256 |
| --- | --- |
| corrected.json | `139d8b6d574d18937f0e08cf8c7b1dc4e9c5d6306f5dd7e2070ab769de89975a` |
| original.json | `3d7a2561f166d8a10f641c97aefa7b4d5ce5941b8aade41ca407491693eb0491` |
| rational_data.json | `9eecd42d3f2efcb31ab1b6576c2b203833076d5ba061293098a0ea2e2651e1f5` |

The upstream package manifest had SHA-256
`4ddb89808c141d5bb904f3d64379a6ec1d6867fe5b30bfd8d9b96c1d90b3972c`.
Its private run metadata and paths are deliberately not copied here.

Lean checks the actual 256 explicit rational records. It proves bounds in a
4000 by 4000 micrometre die, positive sizes, unique IDs and disjoint **closed**
rectangles, so rectangle-to-rectangle contact is excluded. Die boundary contact
is allowed by the bounds predicate. A kernel-checked grid-shape identity connects
every explicit record to the arithmetic pairwise-separation proof; the records
are not silently replaced by an assumed grid.

The byte hashes, parser and generator are an externally checked provenance chain,
not a Lean formalization of SHA-256 or JSON parsing. The stored Lean SHA-256 string
is a label. No minimum pairwise gap theorem, routing, ports, optical loss, delay,
process design rules or hardware properties are certified by this dataset.
