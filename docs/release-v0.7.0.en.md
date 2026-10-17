# v0.7.0 — full beta checkpoint with qutrit circuit refinement

This checkpoint synchronizes module 191 and its integration, tests and English
documentation. There are 191 direct MasterSuite imports and 235 root-inclusive
Lean sources (231 top-level files, three nested support sources, and the root).
The proof sources are byte-identical between the private and public trees.

## Hierarchical identity

- Alpha generation: 0 (unchanged).
- Beta checkpoint: 7, published as `v0.7.0`.
- Gamma direction: `quantum-physics`.
- Delta batch: `qutrit-secret-sharing` (modules 189, 190, 191).
- Epsilon module: `QuantumQutritDecoderCircuitRefinement` (stable number 191).
- Zeta: no new internal correction in this publication.

Direction and batch names are stable identifiers, not decimal version positions.
A broader validation scope does not promote an epsilon change into a system change.
The previous v0.6.0 tags remain immutable. Package versions in both trees are 0.7.0.

## Verified result and limits

The finite interpreter executes two controlled subtractions modulo three and a
coordinate exchange. Its permutation matrix equals the explicit decoder of module
190; its three Kraus operators define the same channel on every complex physical
input matrix. Recovery covers every erased share and arbitrary reference dimension.
Agreement with the chosen module-189 recovery is restricted to encoded inputs.

Regression coverage includes nine basis outputs, complex coherences, entangled
inputs, registry projections and four incorrect gate configurations. The three
new unittest methods compile 48 Lean examples and run the basis interpreter.
Wrong-circuit rejection does not imply tolerance of physical gate noise.
Numerical complex simulators, circuit compilers, hardware implementation and
minimal gate counts are outside scope. Python, JSON/SHA-256 and SimLab obligations
remain open. Independent normative conformance is registered for Simon and the
qutrit decoder, not every mathematical module or human intention.

## Release acceptance and evidence

Publication requires one complete beta run on each final tree. A private report
does not certify the differently packaged public tree. Changing the package
version changes the bound build configuration, so the earlier private evidence
remains a historical baseline rather than evidence for these new exact bytes.
No separate module/MasterSuite verify or targeted test run is added to the full
runner. Valid Lake cache is retained. Release tags record measured results and
the accepted evidence digest after every check passes.

```sh
python3 tools/release_evidence.py run-beta --output /absolute/external/evidence --auditor /absolute/path/to/pinned/axiom-audit
python3 tools/release_evidence.py check --evidence /absolute/external/evidence --expected-digest ACCEPTED_DIGEST
```

The runner performs strict root build, complete verify-all, registry audit, the
separate pinned axiom auditor, all live unittest, catalog, scope and diff checks.
Only `propext`, `Classical.choice`, `Quot.sound` are permitted. The second auditor
is a distinct implementation, not a second proof kernel. Counts of Lake tasks,
fresh compilations, tests, Lean assertions and declarations are reported separately;
intersecting audit scopes are never summed. Exact committed bytes are compared
with accepted inputs before sequential publication to main and the annotated tag.

Prior checkpoints:
- Private v0.6.0: `1fb3818e9ee1d011c75cffe54ca0f8df3104b69e`.
- Public v0.6.0: `7c759c72bfc1cb08790c903085c3babdc9ea77d0`.
- Module-191 private beta-checked source: `68f6b188a477f8f57830c7bfddd43e53631992b4`.

See [version policy](../VERSIONING.md) and
[verification hierarchy](verification-hierarchy.en.md).
