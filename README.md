# Mathematical Verification Components in Lean 4

[![Lean verification](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml)

Machine-checked mathematical components built with Lean 4 and Mathlib: algebraic
invariants, finite computations, conditional protocol properties, and explicit
scalar models. Browse the proofs by subject, inspect their assumptions, and reuse
the components in larger formal developments.

**[Knowledge base](knowledge/README.md)** · **[Results and value](knowledge/SUMMARY.en.md)** ·
[Technical reference](docs/verification-details.en.md)

## Proof sections

| Section | Focus |
|---|---|
| [Collatz and discrete dynamics](knowledge/collatz/README.md) | Finite orbits, congruences, and coefficient bounds |
| [Explicit logarithmic bounds](knowledge/riemann/README.md) | Prescribed analytic functions |
| [Almost-complex algebra](knowledge/hopf/README.md) | Algebraic identities and cross products |
| [Polynomial functionals](knowledge/lamzouri/README.md) | Integrals, quotients, and exact minima |
| [Coordinate geometry](knowledge/finsler/README.md) | Forms, polarization, and diagonal transformations |
| [Proof certificates and DAGs](knowledge/proof-graphs/README.md) | Conditional checker soundness |
| [Cryptographic algebra](knowledge/cryptography/README.md) | Diffusion, traces, folding, and commitment identities |
| [Quantum algebra, photonics, and mechanics](knowledge/quantum-physics/README.md) | Matrices, symmetries, and prescribed energy models |
| [Finance and mechanisms](knowledge/finance/README.md) | Balances, reserves, fees, and portfolio risk |
| [Distributed consensus](knowledge/distributed/README.md) | Quorums, conditional election safety, and local log append |
| [Registry and audit](knowledge/verification/README.md) | Selected suites and axiom dependencies |

## Verified snapshot

The [validation record](knowledge/VERIFICATION.en.md) covers **64 Lean files** under `Verification/`, including 62 subject modules and
two verification files. [MasterSuite](Verification/MasterSuite.lean) collects ten
suites and directly imports **41 modules**. The project-wide audit checked
**3,197 declarations**, including generated declarations, with only `propext`,
`Classical.choice`, and `Quot.sound`. This is not a count of independent theorems.

The full build completed with 3,369 jobs, including dependencies; all 19 automated
tests passed. These are recorded validation results, not a promise that every
future commit or toolchain will pass.

## What the proofs establish

Each result applies to its formal definitions and hypotheses. This repository
does not prove the Collatz or Riemann conjectures, resolve the Hopf problem, or
establish end-to-end security of the named protocols. Scalar commitment identities
do not prove cryptographic hiding or binding. Scientific priority of individual
formalizations has not been established.

Every module has an English knowledge card with its result, scope, and source links.

## Build and audit

Lean **4.33.1** and Mathlib **v4.33.1** are pinned. With elan installed:

```bash
lake build --wfail
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 tools/verifier_skill.py verify-all
python3 scripts/check_knowledge.py
```

`AxiomAudit.lean` checks the selected registry theorem's transitive axiom
dependencies. `verify-all` checks all project modules and audits all project
declarations in the imported environment. CI also runs an independent axiom audit.

## Verification tooling

The [verifier CLI and Python API](docs/verifier-skill.en.md) support strict module
verification, fresh axiom audits, integration using explicit recipes with source
rollback, and draft English knowledge cards. The tool operates on trusted local
projects; it is not a sandbox for untrusted Lean or Lake code.

[Contribution guide](knowledge/CONTRIBUTING.en.md) ·
[Machine-readable catalog](knowledge/catalog.json) ·
[Validation snapshot](tools/validation_snapshot.json)

## License and releases

Licensed under [Apache License 2.0](LICENSE). This repository is an independent
English-language source distribution with its own Git history and releases.
See [publication notes](docs/publication.en.md) for Reservoir requirements.
