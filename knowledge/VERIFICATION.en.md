# Verification record — v0.4.1

[Knowledge base](README.md)

The public v0.4.1 distribution was validated locally with Lean and Mathlib
4.33.1. It contains 110 Lean files under `Verification/`, plus the root
`Verification.lean`, and 86 direct imports in `MasterSuite`. The 7,048 audited
declarations include generated declarations; this is not an independent theorem count.

## Completed checks

- Clean strict package build: 3,492 jobs, no warnings or errors.
- `verify-all`: all 110 modules passed compilation, policy checks, and axiom audit;
  source hashes remained unchanged during verification.
- Independent project-wide `axiom-audit`: 7,048 declarations passed, using tool
  commit `46024e005996495c65ef609368e11ab39c4222e3` (v0.1.2).
- Public regression suite: 19 tests passed, with live Lean checks enabled and no skips.
- Knowledge catalog: 110 modules in 11 sections; local links checked in 129 Markdown files.

Both audits allowed only `propext`, `Classical.choice`, and `Quot.sound`.
No custom axioms were found. All 111 exported Lean source files are byte-identical
to the source distribution. English documentation and public tooling were
validated separately; private simulation files were not included.

The source hashes, verifier hash, counts, and scope are recorded in
[validation_snapshot.json](../tools/validation_snapshot.json).

## Reproduction

```bash
lake clean lean-verification-components
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

Run live tests after the full audit: some tests temporarily create Lean fixtures.
The CLI provides `verify-all`; it does not provide `audit-all` or `test-all`.
The independent axiom audit is also configured in the CI workflow. The results
above are local release checks, not a claim about a subsequent hosted CI run.

## Scope retained

Raft Leader Completeness is conditional on Log Matching, record provenance,
and admissible voter histories. The operational state machine proves election
safety for reachable states and historical single voting. Its Log Matching
preservation lemmas have explicit local compatibility and freshness premises.
Global reachable-state Log Matching and the bridge to `HistoryValid` and
`VoterEvolution` remain open.

The MZI results concern scalar redistribution of intensity over the reals;
unitarity of a physical device is not established. The 9.812 MPa packaging value
is a one-dimensional stress proxy, not certification of a tensor stress field.
The `DistributedPaxos` same-ballot safety theorem assumes `SingleVote`.

Formal claims retain their hypotheses. Compilation and an allowed axiom list
do not establish end-to-end protocol security, correctness of a production
implementation, physical validity, or scientific novelty.
