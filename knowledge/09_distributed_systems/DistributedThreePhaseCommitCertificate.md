---
id: DistributedThreePhaseCommitCertificate
language: en
section: distributed
source: Verification/DistributedThreePhaseCommitCertificate.lean
source_sha256: f511de342b5d1b694770e43a56c704061119cabf2dd8416074c8b0e3947c45e8
novelty: not-assessed
status: reviewed
---

# DistributedThreePhaseCommitCertificate

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedThreePhaseCommitCertificate.lean)

This support module contains generated proof data and kernel-checked closure blocks. The read-only candidate checker is scripts/check_three_phase_commit_certificate.py --check.

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

## Limits and references

This is a two-participant 3PC variant with complete-report termination under the stated view-service contract. It is not a refinement proof of every detail of Skeen's original automata, an arbitrary-n result, or a proof of nonblocking in an asynchronous partitioned network. WAL/fsync, participant recovery, Byzantine authentication, deployed RPCs, Python, JSON/SHA-256 and SimLab byte binding are outside scope. Scientific novelty is not assessed.

Reference: Dale Skeen, [Nonblocking Commit Protocols (1981)](https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/Ske81.pdf).
