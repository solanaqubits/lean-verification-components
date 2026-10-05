# Release v0.5.6 verification record

This release adds the general Deutsch-Jozsa circuit, integration and compiler regressions.

## Source and packaging

Private source: `6a991c4e68244e11ca95a97a456ad8511c54eb32`.
Previous public main: `0b9080416243a9a44f37237fe8abd12be98cb8ad`.
Package version: 0.5.6.

The existing allowlisted exporter supplies the package. All 145 Lean sources,
including Verification.lean, match the private snapshot byte for byte. The package
includes MasterSuiteComponents, integration recipes, Python and Lean tests and the
English catalog. The original QuantumDeutschJozsa module is unchanged. Public
settings, dependencies, CI, license, prior release records and corrected scope cards
are retained. No Russian cards or simulation archives are copied. The exporter's
global language substitution required correcting "no English cards" to "no Russian
cards" in the historical private report; proof sources are unchanged.

## Mathematical scope

The register is Fin n → Bool. The explicit normalized character kernel defines
H^⊗n; orthogonality, involution and preservation of arbitrary-state inner products
and norms are proved, with a recursive tensor-kernel identity. The circuit is
Hadamard, phase oracle, Hadamard, and its output amplitude formula is derived.
The explicit XOR oracle on an ancillary minus state yields phase kickback and the
joint-circuit factorization; marginal squared amplitudes agree with the reduced
circuit. The zero-output amplitude equals the mean of the Boolean signs.

On a nonempty finite domain, constant functions give zero-output weight one,
balanced functions give zero-output weight zero. Under the promise every outcome
of positive weight classifies correctly. Balanced outputs need not form one basis
state. The n=0 case has one input and no balanced functions; n=1 agrees with both
amplitudes and predicates of the original module. No extra parity hypothesis is
needed for promise separation. Empty abstract domains are excluded there.

The amplitude formula and normalization also cover functions outside the promise;
a two-bit AND example has zero-output weight 1/4. This does not grant zero-error
classification without the promise. A nonlinear balanced example has several
nonzero output amplitudes. Regressions also cover ancillary-state requirements.

Born-rule interpretation, measurement runtime, physical implementation and noise,
oracle gate synthesis, query-cost semantics and complexity or speedup bounds are
outside the proved scope.

## Validation

- **108 unique direct imports**, **144 Lean files** under Verification/.
- Fresh strict build: **3526 jobs**, zero warnings.
- Full local verify-all: **144 modules**, **9547 declarations**, no violations or source changes.
- Independent pinned audit: **9547 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **43 public tests** passed in **76.34 seconds**, no errors, failures or skips.
- Integration is idempotent; all source hashes still match after live tests.
- Catalog, local links and the 256-node static placement provenance checks pass.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
python3 tools/verifier_skill.py integrate Verification.QuantumDeutschJozsaGeneral QuantumDeutschJozsaGeneralSuite
```

The separate independent audit uses leanprover-community/axiom-audit v0.1.2,
pinned at `46024e005996495c65ef609368e11ab39c4222e3`, with allowlist
`propext,Classical.choice,Quot.sound`. AxiomAudit.lean compilation alone is not a
replacement for this tool. The CLI has no audit-all/test-all commands.

The [validation snapshot](../tools/validation_snapshot.json) records measured public
results. The [historical private report](deutsch-general-verification.en.md) retains
its distinct 46-test result. See the [scope card](../knowledge/03_quantum_physics_and_optics/QuantumDeutschJozsaGeneral.md).

## Isolation and remaining obligations

Work uses isolated remote source and public clones. The source is detached at the
selected commit. Main and the new annotated tag are sent with git push --atomic;
no force push or tag replacement is used.

Numerical rationalization, cell-boundary comparison and SimLab search remain
unformalized. Python, JSON/RFC 8259, SHA-256 implementations, source authenticity
and binding external inputs to bytes remain separate obligations. Digest equality
does not imply byte equality. Historical indeterminate results retain their status.

Control snapshots confirm unchanged original HEAD and all **406 tracked-file
hashes**. Concurrent SimLab activity added 5 metadata entries and changed 2 existing
entries, with 0 removed. This task made no writes to simulations and did not revert
concurrent work; directory-wide immutability is not claimed. Both isolated Git trees
are clean at completion.
