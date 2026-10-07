# Simon statement-conformance pilot

[Knowledge base](../knowledge/README.md)

This report records pilot checkpoint 6090a301baa8bdbe53dc18cf566a27f7dc448f84; current totals are in the [validation record](../knowledge/VERIFICATION.en.md).

This is meta-audit tooling. MasterSuite retains **114 subject imports**. The two
support modules under Verification/Specs do not introduce a new subject suite.
The approved source baseline is 8a58301154937e277e38e417dda503cff403e1b6.

## Independent contract and bridge

[QuantumSimonsSpec](../Verification/Specs/QuantumSimonsSpec.lean) imports only
Mathlib, with independently written registers, XOR, characters, Hadamard,
initial state, actual H/XOR/H composition, marginal probability, binary pairing
and row span. It does not import the Simon implementation or the registry.
GoldSimonPromise retains the nonzero-period and exact two-point-fiber conditions.
GoldDistribution specifies 2/(2^n) on the binary orthogonal hyperplane and zero
elsewhere. GoldRecovery retains nonzero s, orthogonal rows and rank n-1 of their
span, and concludes that the solutions are exactly {0,s}.

GoldSimonSuite contains all seven original obligations: oracle and Hadamard
unitarity, circuit amplitude, odd-dot cancellation, distribution, normalization
and recovery. No physical measurement, iid sample-count theorem, runtime bound
or implemented Gaussian solver is added.

The gold file proves simon_promise_satisfiable using a constant function from a
one-bit input to a zero-bit output with period 1. It also proves satisfiability
of the recovery hypotheses at n=1 with an empty row set and rank zero. These are
concrete witnesses, not a universal theorem that every collection of premises
is consistent. The output register of size zero still has one basis state.

[QuantumSimonsConformance](../Verification/Specs/QuantumSimonsConformance.lean)
proves simon_conformance_verified by mapping each field in both directions,
and obtains gold_simon_verified from the existing master theorem.
An equivalence between two already provable propositions would alone be too weak
as an audit: the executable check additionally protects definitions and field types.

## Checker and trust boundary

```bash
python3 tools/statement_conformance_checker.py --help
python3 tools/statement_conformance_checker.py
python3 -m unittest discover -s tests -p 'test_statement_conformance.py' -v
```

The checker validates reviewed SHA-256 pins for the gold, bridge, probe and
Lean toolchain, checks the local source policy, rebuilds the required modules,
and invokes Lean with warningAsError for each of them. It then runs the pinned
Lean Meta probe: 16 definition comparisons and seven constructor-field type
comparisons use definitional equality, including the definitions underlying
probability and rank. The master must be a theorem of the expected suite type.
A generated fieldwise proof establishes GoldSimonSuite from the candidate.
A transitive axiom audit permits only propext, Classical.choice and Quot.sound.

The probe includes a narrow syntactic diagnostic for explicit False antecedents
in the selected field expressions. The main safeguard against the specified
mutations is comparison with the independently fixed contract. It is not a
universal detector of unsatisfiable hypotheses, tautologies, hidden assumptions
or all semantically equivalent reformulations. Structurally different statements
require a separately reviewed contract/adapter change; the pilot does not search
for arbitrary logical equivalences. Valid structural recursion is not rejected
as a circular proof.

The JSON report distinguishes conformance_status, axiom_status,
satisfiability_status and epistemic_scope. Failure or timeout never counts as
acceptance. A printed success-shaped record is insufficient if Lean exits with
an error. The checker verifies that project proof sources and configuration have
not changed during the check.

This is for a TRUSTED LOCAL Lean project. Lean elaborators, imports and Lake
configuration can execute code. The checker is not Comparator's sandbox, does
not safely execute hostile metaprograms, and does not implement an independent
proof kernel. Python, the parser and SHA-256 implementation remain external.
The checker, reviewed manifest, probe, gold and pinned dependencies are trusted;
changing all of them together is outside its threat model. Do not regenerate
pins from a candidate or treat a candidate-supplied manifest as an authority.

Comparator's separation of challenge and solution motivated this design:
https://github.com/leanprover/comparator
No Comparator or external-kernel execution is claimed by this pilot.

## Mutation matrix

All tests run against real Lean processes; the standalone suite has no skip flag.
Candidates use temporary, isolated names and are removed with their build artifacts.

| Candidate | Required outcome |
|---|---|
| Existing Simon implementation | Accept |
| Same definitions, independently assembled fieldwise proof | Accept |
| False antecedent added to distribution | Reject field type / explicit False |
| Distribution conclusion replaced by True | Reject field type |
| Public promise drops the nonzero-period condition | Reject definition body |
| Recovery replaces rank by row cardinality | Reject field type |
| Marginal probability replaced by zero | Reject definition body |
| Missing master theorem | Reject |
| Invalid module name | Reject before compilation |
| Modified trusted gold file | Reject before compilation |

The cardinality mutant is a compilable changed structure without a master proof;
its false universal claim is not fabricated as a theorem. Its field mismatch is
checked before master lookup. The weakened-promise and zero-probability fixtures
retain the original proved suite while changing a public definition, ensuring
that inspecting only the suite theorem cannot hide definition drift.

Initial development exposed overlong generated fixture lines rejected by the
strict linter. Those were fixed in the fixture generator; final negative tests
require rejection by the contract probe, not an incidental compilation failure.

## Integration and validation

The root library imports the bridge so ordinary builds cover both support files.
MasterSuite, MasterSuiteComponents and the old subject proofs remain unchanged.
verify-all recursively checks support files. The knowledge catalog lists them
separately as support_modules; source export preserves their nested paths and
copies the checker, reviewed pins, probe and tests. No public release is made.

## Measured validation

| Check | Result |
|---|---:|
| MasterSuite direct imports | 114, unchanged |
| Lean files under Verification/ | 154 top-level + 2 support = 156 |
| Lean sources including root | 157 |
| Clean strict build jobs | 3,539 |
| Local and independent project audit declarations | 11,636, no violations |
| Full private live tests | 62, no failures or skips (242.760s) |
| Standalone pilot tests | 10, no failures or skips (159.398s) |
| Exported pilot tests | 10, no failures or skips (173.461s) |
| Definitions / suite fields compared | 16 / 7 |

The declaration increase from 11,588 to 11,636 is 48 support declarations, not a
new subject module. All 154 previous Lean files, MasterSuite, its components and
integration recipes remain byte-identical to the baseline. The root import adds
the conformance bridge. Integration-recipe idempotence passed in the live suite.
Both full audits permit only propext, Classical.choice and Quot.sound. The
registry hook also passed; it is not a substitute for the full audits.

Executed commands in the isolated checkout:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
python3 -m unittest discover -s tests -p 'test_statement_conformance.py' -v
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

The independent auditor is pinned to commit
46024e005996495c65ef609368e11ab39c4222e3 and built for the project toolchain.
Its executable path above is the validation environment's local path. The
[validation snapshot](../tools/validation_snapshot.json) records proof hashes;
the [contract manifest](../tools/statement_conformance_contract.json) records
the separately pinned gold, bridge, probe and toolchain hashes. Historical scope
records in the snapshot retain their original module-specific meaning.

An English export passed the ten pilot tests and the catalog check with all 157
Lean sources and contract pins preserved. This is export preparation, not a new
public release or a claim that the entire exported live suite was rerun.
The original workspace HEAD and all 406 tracked files outside simulations/
retained their hashes. This task performed no writes to simulations/.

The first full build was interrupted and replaced by the completed clean run.
A catalog check accidentally overlapped temporary mutation fixtures and rejected
their unregistered paths; serialized checking after fixture cleanup passed.
Neither catalog rules nor proof checks were weakened. Initial development logs
and final command logs are preserved separately from the public source export.
Source integrity does not imply universal semantic adequacy of the gold contract.
