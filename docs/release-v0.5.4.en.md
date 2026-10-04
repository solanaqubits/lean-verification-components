# Release v0.5.4 verification record

This release adds exact two-bit Quantum Phase Estimation, its controlled U/U² circuit model, Fourier conventions, regression tests and English documentation.

## Source and export

Private source: `13ee7282c5dd63c88eb4e4c2fd237e8dbd082e8d`.
Previous public main: `fe1097fd863e619737ed773f7c9461914f89229e`.

The existing allowlisted exporter supplies the QPE module, root/central/audit integration, MasterSuiteComponents, integration recipe, Python and Lean regressions, English card and historical source validation report. Current public settings, CI, dependency manifest, license, older release records and previously corrected scope cards are retained. The package version is 0.5.4.

All 143 Lean sources, including Verification.lean, match the selected private source byte-for-byte. The Chandy–Lamport unused-import correction from v0.5.3 is already backported in this private snapshot. No proof edits or disabled checks are needed for the export. The historical hundred-module manifest is unchanged; its quantum package inherits the QPE field.

## Mathematical scope

The control basis is ordered 00, 01, 10, 11. The supported phases are exactly 0, 1/4, 1/2 and 3/4, with index 2*b1+b2. The low bit controls U and the high bit U². Phase kickback is derived from these complex-linear operations and the exact eigenstate equation. The positive-exponent Fourier matrix and its negative-exponent inverse have proved exponential identities, two-sided inverse laws and norm preservation. Applying the inverse to the derived prestate returns exactly the intended basis vector.

A norm-preserving complex-linear target operator and normalized exact eigenstate are supplied hypotheses. The joint output leaves that target unchanged and yields squared-modulus marginal weights 1 for the correct index and 0 elsewhere. The Born-rule interpretation is external; no measurement implementation or random sampler is certified. Approximate phases, spectral leakage/error bounds, eigenstate preparation, arbitrary register sizes, elementary-gate synthesis of inverse QFT, physical gate errors, hardware and Shor are outside scope.

Regressions cover all four phases, bit significance, a normalized target with two nonzero complex coordinates, and counterchecks for the wrong Fourier sign and reversed controlled powers. Zero-target normalization is rejected. The exponential eigenstate hypothesis is explicitly connected to the circuit result.

## Validation

- **106 unique direct imports**, **142 Lean files** under Verification/.
- Fresh strict build: **3524 jobs**, zero warnings.
- Full local verify-all: **142 modules**, **9224 declarations**, no disallowed axioms or source changes.
- Independent pinned audit: **9224 declarations**, only the three allowed standard axioms.
- **41 public tests** passed in **74.651 seconds**, with no errors, failures or skips.
- Integration plan is empty on repetition; current source hashes match the audited snapshot after live tests.
- English catalog, local links and the exact 256-node placement manifest pass their checks.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.QuantumPhaseEstimation QuantumPhaseEstimationSuite
```

The CLI has no audit-all/test-all subcommands. The independent audit uses leanprover-community/axiom-audit v0.1.2, pinned and checked at `46024e005996495c65ef609368e11ab39c4222e3`, with allowlist `propext,Classical.choice,Quot.sound`.

The [validation snapshot](../tools/validation_snapshot.json) records proof hashes and measured public results. The [scope card](../knowledge/03_quantum_physics_and_optics/QuantumPhaseEstimation.md) describes theorem interfaces. The [historical private report](qpe-verification.en.md) retains its separate 44-test result; it does not supply a public test count.

## Preserved boundaries and isolation

Earlier numerical boundaries remain unchanged: rationalization, exact cell-boundary comparison and SimLab search are not formalized by these modules. Python, JSON/RFC 8259, SHA-256, authenticated provenance and binding external parameters to bytes remain separate obligations. Digest equality does not prove byte equality. Historical indeterminate results are retained alongside separate exact-zero or exact-midpoint evidence.

All work takes place in isolated source and public clones. The source snapshot is detached and read-only; the public project has its own dependency artifact copies and a fresh project build directory. No simulation archive is copied. This task does not write to the original workspace or simulations. Publication sends public main and a new annotated tag atomically, without force.

Control snapshots confirm the original workspace HEAD and all **406 tracked-file hashes** are unchanged. Concurrent SimLab work added 9 metadata entries and changed 5 existing entries during these snapshots, with none removed. This task neither wrote nor reverted those artifacts; directory-wide immutability is not claimed. Both isolated Git trees are clean at completion.
