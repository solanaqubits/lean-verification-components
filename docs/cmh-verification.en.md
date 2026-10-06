# Static-epoch AND probe verification record

This is the private verification record, including the import compatibility follow-up.
Public v0.5.10 validation is recorded in [the release report](release-v0.5.10.en.md).

Baseline: `a6fafc6f74f01dcd5de7b2d5a216f47834af0080`.

## Model and contract

This module is a static-epoch, AND wait-graph edge-chasing specialization inspired by Chandy–Misra–Haas. Processes are `Fin n`; proofs also cover the vacuous n=0 case and self-loops for n=1. A process is blocked exactly when it has an outgoing wait edge. The resource-manager semantics behind those edges are assumed, not implemented.

A probe carries initiator, sender and receiver. Initiation and forwarding append all outgoing probes to an explicit queue. Delivery consumes a real queue occurrence; active receivers absorb probes. Local fanout is atomic, network delivery is not. Delivery order is arbitrary. A sent-message history is proof bookkeeping, not an additional wire payload. There is no duplicate suppression, no message-complexity bound and no claim to implement all details of the original dynamic CMH algorithm.

The wait graph is fixed throughout an execution. `EpochReachable.reset` describes an external fresh-epoch contract: replacing the graph clears queued probes and reports. It is not an implementation of distributed reset or stale-packet fencing. Arbitrary graph changes preserving in-flight probes are excluded from the soundness result.

## Proved statements

- `probe_transmission_validity`: every sent probe in a reachable state follows an edge of the fixed graph.
- `probe_path_reconstruction`: every queued or sent probe has a wait path from its initiator to its sender and a final edge to its receiver.
- `cycle_detection_soundness`: every reachable report for i has a nonempty closed wait walk through i. `WaitCycle` means a nonempty closed walk; a separate simple-cycle extraction theorem is not claimed.
- `phantom_deadlock_absence`: in an acyclic fixed graph every reachable report set is empty. These are inductive transition invariants, not guards that assume safety.
- `cycle_detection_path_exists`: a cycle through i permits a finite valid continuation that initiates detection and reports i.
- `cycle_eventually_detected`: after an actual initiation on a cycle, every valid run satisfying `DeliveryFair` eventually reports its initiator. `DeliveryFair` requires each queued probe payload eventually to have a matching delivery event at a later or equal index. It is payload-level service, not FIFO or distinct-instance fairness. It does not assume the desired report. No numerical time bound is proved.
- `reset_epoch_soundness`: the same safety holds within each externally reset isolated epoch.

Only initiators on cycles are covered by the detection theorem. A process that merely reaches a cycle need not receive its own probe. No theorem equates every blocked process with cycle membership.

## Counterexamples and limits

`dynamic_send_checks_insufficient` exhibits a valid trace of the deliberately weakened dynamic protocol: every instantaneous graph is acyclic, every send uses a current edge, yet retained probes return to the initiator and produce a false report. This refutes the proposed send-time-only criterion, not the original CMH algorithm with its additional request/reply and controller conditions. `unfair_execution_counterexample` retains an initiated probe forever in an idle run, showing why message storage alone gives no guaranteed detection.

OR waiting, changing process membership, deadlock resolution, packet loss, crashes, resource grants and physical timers are not modeled. Python, JSON/SHA-256, SimLab input-to-byte binding and runtime implementations remain external obligations. Scientific novelty is not assessed.

Reference: K. M. Chandy, J. Misra and L. M. Haas, [Distributed Deadlock Detection (1983), Section 3](https://www.cs.utexas.edu/~misra/scannedPdf.dir/DistrDeadlockDetection.pdf).

## Validation

- **112 direct imports**, **152 Lean files** in Verification/.
- `lake build --wfail`: **3534 jobs**, no warnings. Dependency caches are independent copies; this is not a from-source rebuild of Mathlib.
- Module verify and audit: **283 declarations**, clean.
- Full verify-all and independent pinned audit: **11347 declarations**, only propext, Classical.choice, Quot.sound.
- **50 private live tests**, **88.279 seconds**, no errors, failures or skips.
- AxiomAudit registry hook, catalog, source hashes and integration idempotence pass.
- Existing 3PC generator check reproduces **7,824** states; static placement data check retains **256** nodes.
- Export covers all **153 Lean sources**, including the root, byte for byte, plus CMH regression files and English documentation. Only English cards are exported; simulations are excluded.
- Original HEAD and **406** tracked-file hashes remain intact. This task wrote nothing in simulations; concurrent SimLab activity is not reverted or interpreted as immutable.

```bash
python3 tools/verifier_skill.py verify Verification/DistributedChandyMisraHaasDeadlock.lean
python3 tools/verifier_skill.py audit Verification/DistributedChandyMisraHaasDeadlock.lean
python3 tools/verifier_skill.py integrate Verification.DistributedChandyMisraHaasDeadlock DistributedChandyMisraHaasSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/check_three_phase_commit_certificate.py --check
python3 scripts/generate_chip_manifest.py --check
```

Independent audit: leanprover-community/axiom-audit v0.1.2, pinned commit
`46024e005996495c65ef609368e11ab39c4222e3`, root Verification and allowlist
`propext,Classical.choice,Quot.sound`. The AxiomAudit registry hook is an additional check.
Only private main is published by this task; no public release is created.

## Import compatibility follow-up

Baseline: `766668434c2f1c1220f384ecb4db3047a7819393`.
The public clean build exposed a forbidden broad `Mathlib.Tactic` import.
The approved correction removes that unused import and imports
`Mathlib.Tactic.FinCases` explicitly in the regression file. Theorem statements
and proof bodies are byte-for-byte unchanged after ignoring that import line.
The report wording also avoids the exporter's language-label substitution,
so its byte-preservation regression passes without weakening the test.

The corrected private snapshot passed the full strict build (3534 jobs),
verify-all (152 files, 11347 declarations), the independent pinned
audit with the standard three-axiom allowlist, and the AxiomAudit registry hook.
All 50 private live tests passed in 82.04 seconds without failures or skips.
Catalog hashes and the retained 7,824-state certificate were also checked.
The public release is validated separately against the corrected source snapshot.
