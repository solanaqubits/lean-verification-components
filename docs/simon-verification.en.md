# Simon private-source verification record

This historical source-development record precedes public publication. For the
separately measured public results, see [release v0.5.12](release-v0.5.12.en.md).

## Source and formal statements

Baseline: 2fbb1074ecec7634393cd3081938b2f9fb22edba. Development and checks use an isolated clone; only private main is published. The resulting commit is identified by Git history; no self-referential commit hash is embedded here.

Source SHA-256: `f59fb92293df5dadc613ad9b4e64c21ea7793ba107e4025726427edf59c66361`.

- `simon_oracle_unitarity`: for every finite n,m and arbitrary function f, the complex XOR operator is involutive and preserves the Hermitian product on arbitrary states. `oracle_linear`, `oracle_self_adjoint` and `oracle_norm` prove linearity, adjoint identity and norm preservation.
- `hadamard_linear`, `hadamard_involution`, `hadamard_inner`, `hadamard_norm`: the lifted complex input Hadamard preserves the old real kernel and is unitary on arbitrary states.
- `simon_circuit_amplitude`: the actual H–XOR–H composition on the zero basis state equals the fiber-character amplitude, for every f without a promise.
- `simon_amplitude_zero_when_odd_dot`: under SimonPromise f s, dot(y,s)=1 implies zero amplitude at every output label.
- `simon_exact_probability_distribution`: under the same promise, P(y)=2/(2^n) if dot(y,s)=0 and 0 otherwise.
- `simon_distribution_normalized`: sum_y P(y)=1 for every f, including functions outside the promise.
- `simon_linear_system_recovery`: for s≠0, a finite Y with each row orthogonal to s and finrank(rowSpan Y)=n−1, the equations hold for v iff v=0 or v=s. No sampling/rank-growth assumption is silently added.

[The source card](../knowledge/03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md) records all model boundaries. This is neither a polynomial-time algorithm theorem nor a physical measurement certificate.

## Measured private validation

| Metric | Result |
|---|---:|
| MasterSuite direct imports | 114 |
| Lean files under Verification/ | 154 |
| Lean sources including root | 155 |
| Full clean project build jobs | 3537 |
| Project declarations, both audits | 11588 |
| New module transitive audit closure | 312 |
| Live tests | 52, zero errors/failures/skips (84.993s) |

Strict compilation and both full-project audits passed. The allowed dependencies are exclusively propext, Classical.choice, Quot.sound. The independent tool is axiom-audit v0.1.2 pinned to 46024e005996495c65ef609368e11ab39c4222e3, built under the project toolchain. Its imported-environment dependency check is complementary to kernel compilation, not a second proof checker. Verification/AxiomAudit.lean also passed as an additional registry check.

The clean build removed only the isolated clone's own .lake/build; pinned dependency artifacts were retained. No warnings were permitted. All Lean source hashes remained stable during verification. Existing proofs were preserved; registry integration adds the simon field without changing prior fields.

## Reproduction

```bash
python3 tools/verifier_skill.py verify Verification/QuantumSimonsAlgorithm.lean
python3 tools/verifier_skill.py audit Verification/QuantumSimonsAlgorithm.lean
python3 tools/verifier_skill.py integrate Verification.QuantumSimonsAlgorithm QuantumSimonsSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
lake env /path/to/pinned/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/export_public.py /path/to/fresh-export
```

The live regression compiles arbitrary complex operator identities, the n=1/m=0 case, n=0 impossibility, exact two-bit parity weights, unreachable output labels, sufficient-rank recovery, an insufficient-rank counterexample, and a function outside the promise. The test wrapper is not a formal proof of Python correctness.

## Export, environment and Reservoir

Exported Lean sources must match all 155 source files byte for byte; English-only cards and both regression files are included. The independent export run passed strict compilation, verify-all, live tests, the registry hook and the pinned full-project axiom audit. The repeated integration planner returned an empty diff with applied=false; registry/root hashes remained unchanged.

The original checkout's HEAD and all 406 tracked-file hashes outside simulations are preserved. This task made no writes to simulations; parallel SimLab activity is not treated as immutable.

The original readiness check inspected public v0.5.11; [Reservoir readiness](reservoir-readiness.en.md) now records the subsequent v0.5.12 release preparation. The public repository meets the observed criteria, but the package page returned 404. That source-development task did not submit an issue, push public main or create a public release; registry acceptance remains unconfirmed. Comparison with openai/math remains deferred research, not an assertion about that repository's contents.

## Measured export validation (unreleased preparation tree)

The fresh English export completed a clean 3537-job strict build without warnings, 49 live tests without errors/failures/skips (83.022s), and both full-project audits of 11588 declarations. The registry audit and catalog/link checker also passed. All 155 Lean sources and the regression code are byte-identical to the checked private source. No Russian-language cards were exported.

The final documentation and snapshot refresh changes only Markdown and validation metadata; every executable/configuration/proof source in the final export is compared byte-for-byte with the tested export. No new public version or tag is created.
