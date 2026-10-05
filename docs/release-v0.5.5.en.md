# Release v0.5.5 verification record

This release adds multiple-target Grover search on four real amplitudes, its
integration, compiler regressions, compatibility bridge and English scope card.

## Source and packaging

Private source: `7f08c02b55b137cc895b287e88b018329acf1794`.
Previous public main: `aaf4a6442736277cb89ef35500c59cc49c24c136`.
Package version: 0.5.5.

The existing allowlisted exporter supplies every required file. All 144 Lean
sources, including Verification.lean, match the selected private snapshot byte
for byte. Root, central and axiom-audit imports, MasterSuiteComponents, the
integration recipe, Python/compiler tests and catalog are included. The original
QuantumGroverSearch remains unchanged. Public package settings, CI, dependency
manifest, license, historical release records and corrected scope cards are retained.
No Russian cards or simulation archives are exported. The exporter rewrites the
word Russian globally; two resulting misleading phrases in the historical report
are corrected in the public copy without changing proof source or validation data.

## Mathematical scope

The oracle negates each marked coordinate; diffusion reflects about the mean.
Their composition preserves norm on arbitrary real four-vectors. Starting from
uniform amplitudes 1/2, every natural iterate is normalized. The derived two-class
amplitude recurrence gives these exact success weights:

| Targets M | Success weight after k steps |
|---|---|
| 0 | 0; uniform is fixed |
| 1 | 1 if k mod 3 = 1, otherwise 1/4 |
| 2 | 1/2 for every k |
| 3 | 0 if k mod 3 = 1, otherwise 3/4 |
| 4 | 1; the global sign is (-1)^k |

For 0<M<4 the normalized marked and unmarked uniform vectors are orthonormal,
have unique plane coordinates and span an invariant plane containing all iterates.
The algebraic rotation matrix and c²+s²=1 are proved. These two vectors do not span
all of R^4; the unmarked vector is not the full orthogonal complement of the marked
line. Plane agreement with rank-one reflection is sufficient, not necessary.
T={0,1}, v=(1,-1,0,0) refutes general agreement; T={0}, v=(0,1,-1,0) gives agreement
outside the symmetric plane. Coordinate conversions prove exact compatibility
with the old singleton oracle, diffusion and search result on the applicable states.

Regressions cover all target counts, nonadjacent targets, symbolic iteration
counts, three-target overshoot and sign, degenerate endpoints, arbitrary-state
legacy compatibility and norm preservation, plane uniqueness and both counterexamples.
This is exact N=4 real algebra, not arbitrary-N search, query complexity, fractional
phase reflections, complex gate synthesis, physical measurement, quantum noise or
hardware. Born-rule interpretation is external. No formal trigonometric-angle
formula or separate topological-closedness theorem is claimed.

## Validation

- **107 unique direct imports**, **143 Lean files** under Verification/.
- Fresh strict build: **3525 jobs**, zero warnings.
- Full local verify-all: **143 modules**, **9378 declarations**, no violations or source changes.
- Independent pinned audit: **9378 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **42 public tests** passed in **74.485 seconds**, no errors, failures or skips.
- Integration is idempotent; all source hashes still match after live tests.
- Catalog, local links and the 256-node static placement provenance checks pass.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.QuantumGroverMultipleTargets QuantumGroverMultipleTargetsSuite
```

The independent audit additionally uses leanprover-community/axiom-audit v0.1.2,
pinned and checked at `46024e005996495c65ef609368e11ab39c4222e3`, with allowlist
`propext,Classical.choice,Quot.sound`. Compiling AxiomAudit.lean alone is not a
substitute for that independent tool. The CLI has no audit-all/test-all subcommands.

The [validation snapshot](../tools/validation_snapshot.json) records proof hashes
and measured public results. The [scope card](../knowledge/03_quantum_physics_and_optics/QuantumGroverMultipleTargets.md)
details theorem boundaries. The [historical private report](grover-multiple-verification.en.md)
retains its separate 45-test result, not a public test count.

## Isolation and retained obligations

All work takes place in isolated source and public clones, with independent
project build artifacts. Publication sends main and a new annotated tag atomically,
without force or overwriting a tag. The source clone is detached at the selected SHA.

Numerical obligations are unchanged: rationalization, cell-boundary comparisons
and new SimLab search procedures remain unformalized. Python, JSON/RFC 8259,
SHA-256 implementations, authenticated provenance and external input-byte binding
remain separate obligations. Digest equality does not imply byte equality.
Historical indeterminate outcomes remain alongside separate exact evidence.

Control snapshots confirm unchanged original HEAD and all **406 tracked-file
hashes**. Concurrent SimLab activity added 4 metadata entries and changed 2 existing
entries, with 0 removed. This task made no writes to simulations and did not revert
concurrent work; directory-wide immutability is not claimed. Both isolated Git trees
are clean at completion.
