# General Deutsch–Jozsa verification record

Private baseline: `7f08c02b55b137cc895b287e88b018329acf1794`.
The original QuantumDeutschJozsa module and its registry field are unchanged.

## Result and limits

The module defines real states on Bits n = Fin n → Bool, derives orthogonality of
bit characters, H²=I, linearity and inner-product preservation, and proves the
recursive tensor-kernel identity. The phase oracle is connected to the explicit
XOR oracle acting on a normalized minus ancilla. Joint execution is related to
H ∘ phaseOracle ∘ H, with unchanged ancilla and normalized marginal weights.
The full output formula is derived from these operators for every Boolean function.

Finite counting proves zero-string weight 1 for constants and 0 for balanced
functions on nonempty domains. The promise gives correct classification for every
positive-weight output, with total nonzero weight 1 in the balanced case. Empty
finite domains require separate treatment; n=0 has one input and only constant
functions. Both one-bit amplitudes and classification predicates match the old
module exactly. Two-bit AND and a nonlinear three-bit balanced function refute
unconditional classification and a fixed nonzero output respectively. Replacing
the minus ancilla by a plus-shaped vector also has a formal counterexample.

The model is exact finite-dimensional real algebra, not a physical implementation.
Born-rule interpretation, gate synthesis, noise, oracle construction cost, query
complexity, classical lower bounds and exponential speedup are not certified.
Functions outside the promise are modeled, but zero-error classification is not
claimed for them. Python, JSON, SHA-256 and SimLab input-byte binding obligations
remain unchanged. Mathematical novelty is not assessed.

## Validation

The registry has **108 unique direct imports**, with **144 Lean files** under
Verification/. Strict full build passed **3526 jobs**, with zero warnings.
Module verify and audit each checked **200 imported project declarations**.
Full verify-all and the independent pinned audit each checked **9547 declarations**,
allowing only propext, Classical.choice and Quot.sound. The strict AxiomAudit hook
also passed. All **46 private live tests** passed in **74.975 seconds**, with no
failures, errors or skips. Source hashes remain unchanged after the live tests.

Repeated integration returns an empty diff. The RU/EN catalog, source-line links
and 256-node exact placement provenance pass. The public exporter preserves all
**145 Lean sources**, including the root, byte-for-byte and includes the new tests.
Its English catalog passes; no Russian cards or simulation archives are copied.
This is export preparation, not a new public release.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify Verification/QuantumDeutschJozsaGeneral.lean
python3 tools/verifier_skill.py audit Verification/QuantumDeutschJozsaGeneral.lean
python3 tools/verifier_skill.py integrate Verification.QuantumDeutschJozsaGeneral QuantumDeutschJozsaGeneralSuite --apply
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The independent audit uses leanprover-community/axiom-audit v0.1.2, pinned and
checked at `46024e005996495c65ef609368e11ab39c4222e3`, with the same three-axiom
allowlist. No audit-all/test-all subcommands are assumed. No new linter is disabled.

Integration targets MasterSuiteComponents and preserves the old deutsch_jozsa
field. The public exporter includes the new Python and Lean regressions, English
card and historical report; public publication is not part of this task.
The [scope card](../knowledge/03_quantum_physics_and_optics/QuantumDeutschJozsaGeneral.md)
and [validation snapshot](../tools/validation_snapshot.json) record the interfaces
and exact source hashes.

## Isolation

All implementation writes occur in an isolated clone or external task scratch
paths. Original HEAD and all **406 tracked-file hashes** are unchanged.
Concurrent SimLab work added 17 metadata entries and changed 3, with
0 removed, between control snapshots. This task made no writes to simulations
and did not revert concurrent work; directory-wide immutability is not claimed.
The isolated Git working tree is clean after the commit and private-main push.
