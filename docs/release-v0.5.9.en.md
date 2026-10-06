# Release v0.5.9 — two-participant 3PC safety and conditional completion

Private source: `a6fafc6f74f01dcd5de7b2d5a216f47834af0080`.
Previous public main: `38bfd9d4cb8a981d89f2ac93a7df58caa2763584`.

The package contains DistributedThreePhaseCommit, DistributedThreePhaseCommitCore
and DistributedThreePhaseCommitCertificate, registry integration, live regression
tests, the candidate-data reproducer and English cards and reports.
All 152 Lean sources, including the root file, match the private snapshot byte for byte.

## Guarantees and external contracts

Safety is derived for a fixed two-participant operational model with bounded
request/response queues. Agreement includes terminal decisions of stopped nodes;
terminal decisions are permanent. Commit requires both Yes votes, and final commit
follows the acknowledgment barrier. Recovery uses complete reports and a separate
alignment phase. A stopped nonterminal PreCommit does not universally forbid Abort.

Finite completion-path existence is distinct from eventual completion of every
execution under the stated progress assumptions: a nonempty stable surviving
membership, a live unique owner, no further failures and weak fairness of productive
actions. Accurate detection/membership, unique coordinator appointment and atomic
epoch fencing are external contracts. Election or failure-detector implementations,
unconditional removal of blocking, arbitrary participant counts, dynamic joining,
partitions, Byzantine faults, crash recovery and WAL/fsync are not proved.

A finite invariant certificate is checked by the Lean kernel using ordinary decide;
closure and induction cover arbitrary finite trace lengths. Python supplies candidate
data only and is not trusted by that proof. Python correctness, JSON/SHA-256 and
external SimLab byte binding remain separate obligations. Historical numeric results
are preserved. See the [exact theorem contract map](three-phase-commit-verification.en.md).

## Public validation

- **111 unique direct imports**, **151 Lean files** under Verification/.
- Strict build: **3533 jobs**, zero warnings. Dependency caches are isolated copies; this is not a from-source rebuild of Mathlib.
- Full local verify-all: **151 modules**, **11063 declarations**, no violations or source changes.
- Independent pinned audit: **11063 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **46 public live tests** passed in **85.045 seconds**, without errors, failures or skips.
- Integration is idempotent; all audited source hashes still match after tests.
- Catalog, local links and static 256-node placement provenance checks pass.
- The candidate-data reproducer matches all 7,824 certificate states; Python correctness is not inferred.
- All **152 Lean sources** match the private snapshot.
- Original HEAD and all **406 tracked-file hashes** are unchanged.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/check_three_phase_commit_certificate.py --check
python3 scripts/generate_chip_manifest.py --check
```

The independent audit uses leanprover-community/axiom-audit v0.1.2 pinned at
`46024e005996495c65ef609368e11ab39c4222e3`, permitting only propext,
Classical.choice and Quot.sound. AxiomAudit.lean is an additional strict hook.

## Isolation and publication

The private source checkout and public release checkout are isolated. Existing
public settings and release history are retained. No Russian cards or simulations
archive are exported. This task makes no writes to simulations; concurrent SimLab
changes are not reverted or claimed absent. Publication uses an annotated tag and
`git push --atomic origin main v0.5.9`, without force or tag replacement.
