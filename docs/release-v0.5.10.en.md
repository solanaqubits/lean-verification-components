# Release v0.5.10: static-epoch AND deadlock detection

Private proof snapshot: `ac3e2363e6711b981f31e1cc782ec1b51cf69b35`.
Original import-correction baseline: `766668434c2f1c1220f384ecb4db3047a7819393`.
Previous public main: `b9a026b03e486e530480f9b6e01ef522d9dbd4b6`.

## Scope

The new CMH-inspired module has explicit probe queues, real consuming deliveries,
path provenance and inductive detection soundness for a fixed finite AND wait graph.
It proves existence of a finite detection path and eventual detection after an
actual initiation on a cycle under the explicit payload-delivery contract.
A cycle is a nonempty closed walk through the initiator. Upstream processes are
not asserted to receive their own probes. Local fanout is atomic; duplicate
suppression and a message-complexity bound are not proved.

Graph replacement requires an external fresh isolated epoch that discards prior
probes and reports. This is not an implemented distributed reset or fencing protocol.
The formal dynamic counterexample refutes checking edges only when sending while
retaining old probes across graph changes. It does NOT refute the original dynamic
Chandy–Misra–Haas algorithm with its additional controller and request/reply rules.
Arbitrary dynamic CMH correctness is not established by this module.

An idle execution demonstrates why storing probes without eventual delivery is
insufficient. OR waiting, process failures, packet loss and deadlock resolution
are outside scope. Python, JSON/SHA-256 and external SimLab byte binding remain
separate obligations. Historical results are preserved.
See the [theorem contract](cmh-verification.en.md) and
[English card](../knowledge/09_distributed_systems/DistributedChandyMisraHaasDeadlock.md).

## Import compatibility correction

A fresh public build rejected the broad `import Mathlib.Tactic` in the original
private baseline. Removing that unused import makes the subject module pass the
strict build. The regression file imports `Mathlib.Tactic.FinCases` explicitly.
No theorem statement or proof body changes. The final source comparison records
this correction explicitly; no byte-identity claim is inferred from semantic equivalence.

## Public validation

- **112 unique direct imports**, **152 Lean files** under Verification/.
- Strict build: **3534 jobs**, zero warnings. Dependency caches are isolated copies; this is not a from-source rebuild of Mathlib.
- Full local verify-all: **152 modules**, **11347 declarations**, no violations or source changes.
- Independent pinned audit: **11347 declarations**, only the three allowed axioms.
- The strict AxiomAudit.lean hook also passed.
- **47 public live tests** passed in **84.632 seconds**, without errors, failures or skips.
- Integration is idempotent; all audited source hashes still match after tests.
- Catalog, local links and static 256-node placement provenance checks pass.
- The candidate-data reproducer matches all 7,824 certificate states; Python correctness is not inferred.
- All **153 Lean sources** match the corrected private snapshot byte-for-byte.
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

Independent audit: leanprover-community/axiom-audit v0.1.2 pinned at
`46024e005996495c65ef609368e11ab39c4222e3`, with the allowlist
propext, Classical.choice, Quot.sound. AxiomAudit.lean is an additional registry check.

## Isolation and publication

Both checkouts are isolated. Existing public configuration and release history
are preserved; Russian cards and simulations are excluded. This task makes no
writes to simulations and does not revert concurrent SimLab work.
Publication uses an annotated tag and `git push --atomic origin main v0.5.10`,
without force or tag replacement.
