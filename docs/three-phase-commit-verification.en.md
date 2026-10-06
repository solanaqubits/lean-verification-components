# Two-participant 3PC source verification record

This historical record describes validation of the private source snapshot.
For separately measured public results, see [release v0.5.9](release-v0.5.9.en.md).

Private baseline: `fac78833f819eb57ec9d69e67dc80ef5613e4c8c`.

## Exact model

One transaction, two fixed participants and one separate original coordinator are modeled. Any process can stop irreversibly; stopped participant decisions remain part of agreement. Positive votes are retained in a monotone two-bit mask. A No vote puts its sender in an irreversible aborted state. The existing Vote and Decision types are reused by the public adapters.

The core has individual request-send, request-receive, reply-send and reply-receive events. A bounded request/response slot per participant is an explicit queue encoding: `packets` lists the pending addressed packets. Replies capture the participant state at send time, and the coordinator reads the received reply body. The phase barrier prevents reuse of a slot until its previous exchange has completed. This is not a model of arbitrary unbounded or duplicated RPC traffic. Crashes may occur between individual multicast sends.

The normal path collects votes, aligns participants to PreCommit and collects acknowledgments before sending Commit. A negative vote leads to Abort. Participants do not decide solely on a timeout. Recovery starts a new fenced epoch, collects a complete set of member reports, selects a direction, then performs a separate alignment/acknowledgment phase before final delivery. PreCommit/Committed reports select the commit direction; otherwise the abort direction is selected. Terminal states never reverse.

## Environment contract

A strong external view service detects actual stops, chooses one live backup, supplies exact surviving membership, fences the old epoch at all survivors and cancels old pending packets. It does not inspect participant states to decide the transaction. Its accurate membership, unique appointment and atomic fencing are assumptions of this model; no distributed election, partition tolerance, physical clock or failure detector implementation is proved. `deliverPacket` rejects a mismatched epoch or packet envelope. Crashed processes do not recover.

## Checked results

The supporting certificate contains 7,824 finite control states. Ordinary kernel reduction checks initial membership, closure under every modeled event, agreement including stopped participants, vote provenance, immutable terminal decisions, actual packet consumption, report payload consistency and progress obligations. Induction lifts closure to executions of arbitrary finite length. Python only generates candidate data and is not trusted by the proof. This is a finite-state protocol proof, not a bounded search over trace lengths.

`completion_path_exists` establishes a finite completion from a reachable stable view. `completion_path_after_detection` includes an explicit accurate view-installation step when a survivor exists. `completion_under_progress_assumptions` proves that every valid weakly fair execution completes all survivors after an accurate stable view with a live coordinator and no further failures. Weak fairness concerns continuously enabled concrete sends, receives and local actions; it does not assume a decision or successful completion. There is no numerical wall-clock bound. A perpetual idle execution witnesses why arbitrary withholding is insufficient.

A stopped PreCommit participant may coexist with an aborted surviving participant. The theorem prohibits opposite terminal decisions, not every PreCommit/Aborted pair. An explicit reachable partial-PreCommit trace refutes the naive independent timeout shortcut.

## Theorem contract map

All state-safety results require `Reachable s`; no agreement predicate is a transition guard.

| Result | Hypotheses and conclusion |
| --- | --- |
| `reachable_agreement` | No left/right Committed–Aborted pair, irrespective of crash flags. |
| `terminal_decision_stability` | A valid `Step s e t` preserves each terminal local decision. |
| `commit_requires_yes` | Either participant committed implies the retained Yes mask is 3 (both participants). |
| `precommit_ack_provenance` | A queued or consumed response body equals its participant's state in the current exchange; `receives_consume_authentic_packets` additionally proves packet consumption and send-time payload capture. |
| `normal_commit_barrier` | In final-Commit phase every installed member is PreCommit or Committed. The initial view contains both participants; coordinator advancement requires each member's own consumed acknowledgment slot. |
| `termination_protocol_preserves_agreement` | Every valid finite continuation from a reachable state, including recovery events, preserves agreement. |
| `completion_path_exists` | Reachability and a stable view imply existence of a finite execution ending with all live participants terminal. |
| `completion_path_after_detection` | Reachability and at least one live participant imply existence of such a path including the external view-installation event if needed. |
| `completion_under_progress_assumptions` | A valid infinite run with a reachable stable suffix, no further crashes/view changes and weak fairness of concrete productive actions eventually has all survivors terminal. |
| `stale_epoch_rejected` | A packet whose epoch differs from the current view is rejected. |

`Stable` means a running owner, exact survivor membership, and nonempty membership. Eventual installation of that stable view is an explicit progress assumption, not a proved detector/election algorithm. Weak fairness supplies eventual scheduling and delivery of continuously enabled actions without a numerical delay bound. Stopped nodes need not receive or finish anything.

Complete survivor reports alone would not justify ignoring a stopped terminal decision in an arbitrary protocol. Here their sufficiency follows from the kernel-checked reachable-state invariant and closure under recovery: every recovery transition preserves agreement including the stopped states. In particular, a reachable committed state originates behind the acknowledgment barrier, so it cannot coexist with a surviving Init/Prepared-only view that subsequently aborts. This is a property of the modeled transitions, not an assumption that the recovery decision is already safe.

## Limits and references

This is a two-participant 3PC variant with complete-report termination under the stated view-service contract. It is not a refinement proof of every detail of Skeen's original automata, an arbitrary-n result, or a proof of nonblocking in an asynchronous partitioned network. WAL/fsync, participant recovery, Byzantine authentication, deployed RPCs, Python, JSON/SHA-256 and SimLab byte binding are outside scope. Scientific novelty is not assessed.

Reference: Dale Skeen, [Nonblocking Commit Protocols (1981)](https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/Ske81.pdf).

## Validation

- **111 direct imports**, **151 Lean files** under Verification/.
- Strict build: **3533 jobs**, no warnings. Dependency caches are separate copies, not a from-source Mathlib rebuild.
- Module verify and audit: **950 imported project declarations**, clean.
- Complete verify-all and independent pinned audit: **11063 declarations**, only the three allowed axioms.
- **49 private live tests**, **104.286 seconds**, no failures, errors or skips.
- The strict AxiomAudit hook, catalog, source hashes, static placement data and idempotence pass.
- The candidate generator reproduces all **7,824** states; the Lean kernel proves closure and properties.
- All **152 Lean sources**, including the root file, are exported unchanged; no Russian cards or simulations archive.
- Original HEAD and **406 tracked-file hashes** preserved. No writes to simulations.

```bash
python3 tools/verifier_skill.py verify Verification/DistributedThreePhaseCommit.lean
python3 tools/verifier_skill.py audit Verification/DistributedThreePhaseCommit.lean
python3 tools/verifier_skill.py integrate Verification.DistributedThreePhaseCommit DistributedThreePhaseCommitSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/check_three_phase_commit_certificate.py --check
python3 scripts/generate_chip_manifest.py --check
```

Independent audit: leanprover-community/axiom-audit v0.1.2 pinned at
`46024e005996495c65ef609368e11ab39c4222e3`, with allowlist
`propext,Classical.choice,Quot.sound`. AxiomAudit.lean is an additional registry hook.
No audit-all or test-all subcommands are assumed.

The source-development task published only the private main. Concurrent SimLab activity is not
reverted, and directory-wide immutability is not inferred from this task's lack of writes.
