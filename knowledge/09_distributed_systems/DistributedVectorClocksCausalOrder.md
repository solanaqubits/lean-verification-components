---
id: DistributedVectorClocksCausalOrder
language: en
section: distributed
source: Verification/DistributedVectorClocksCausalOrder.lean
source_sha256: 321601089def144483e14b8fd1d8c47f6a09a87f9167086aee601d2126f0fc42
novelty: not-assessed
status: reviewed
---

# Vector clocks and independent event causality

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedVectorClocksCausalOrder.lean)

## Model and contract

Processes are Fin n, timestamps are Fin n → ℕ, and event identities are positions
Fin length in a finite trace. Each Event records its process, positive local
sequence number and Local / Send(message identifier, destination) / Recv(message
identifier) payload. Legal histories number an event one greater than the maximum
previous local sequence number (zero for an empty prefix). Sends and receives
have unique identifiers in their respective classes; every receive has an earlier
matching send addressed to the receiving process. Outstanding messages and delivery
out of send order are allowed. The intended domain is n ≥ 1; the general theorems
also cover empty histories without adding an artificial inhabitance assumption.

History.Direct uses earlier positions on the same process or a matching message
edge. HappensBefore is its **strict** transitive closure. It never refers to clocks.
Theorems local_order_iff and matching_send_precedes connect these edges to local
sequence order and legal send/receive pairing. CausalPast adds equality explicitly.

## Operational meaning and proof

Execution.step specifies merging predecessor timestamps and incrementing the
executing process exactly once. compute implements this recurrence by terminating
recursion on event positions; execute constructs an Execution for every legal
history. It does not compute timestamps by asking whether a causal path exists.

The predecessor fold includes all earlier local events. localBefore_latest proves
that it equals the most recent actual local timestamp, or zero before the first
local event. deliveredClock_receive reduces the message fold to the unique sent
timestamp; local and send events have no incoming timestamp. Thus local_update,
send_update and receive_update prove the usual local tick / max-then-tick rules.
Sending attaches the post-increment timestamp; receiving never substitutes an
arbitrary or forged vector. execution_unique proves uniqueness of clock assignment.

causal_past_invariant is proved by induction over trace prefixes. Each coordinate
is exactly the finite maximum of local event numbers in the reflexive causal past,
with empty maximum zero. The explanatory pastClock uses classical reachability;
the operational compute function is executable independently of that definition.

The resulting theorems establish:

- HappensBefore e f iff VectorLE (stamp e) (stamp f) and stamp e ≠ stamp f.
- Distinct event identities have distinct timestamps within one legal execution.
- HappensBefore is irreflexive and transitive.
- Concurrent e f (including e ≠ f) iff neither timestamp is coordinatewise ≤ the other.

Strict vector order means coordinatewise ≤ plus vector inequality, **not** < in
every coordinate. This represents the event order faithfully on its timestamp
image; it does not assert surjectivity onto all of ℕⁿ. Causal incomparability is not
physical simultaneity and is not a commutation theorem for application actions.

## Compatibility and regressions

The n2_*_bridge lemmas preserve tick1, tick2, merge, receive1, receive2 and both
orders from DistributedVectorClocks. The older module is unchanged.

Kernel-checked executions include independent initial events with stamps [1,0]
and [0,1], a three-process relay ending at [1,2,1], receives of message 1 before
message 0 with stamps [2,1] then [2,2], and an outstanding send with stamp [3,0].
The external regression also checks n=1, timestamp reflection, local/message edges,
and concurrency between the final receive and outstanding send.

counterexample_no_increment gives two causally ordered local events with identical
zero labels under the defective rule. counterexample_no_merge gives an actual
send/receive edge whose defective receiver label fails to dominate the sender.
These defective labels are not claimed to satisfy Execution.step.

## Clean Water

Finite-trace safety needs neither FIFO nor a promise of eventual delivery or fair
scheduling. Receives must match authentic previous sends; duplicate deliveries are
excluded by the chosen legality contract. There is no delivery-liveness result.
Unbounded natural counters, a fixed process set and immutable message timestamps
are used. Machine overflow, crashes/restarts, Byzantine timestamp forgery, dynamic
membership, clock compression, physical time and channel delay are not modeled.
Correctness of Python, JSON/SHA-256 and the SimLab → Lean bridge remains open.
Mathematical or formalization priority is not assessed.

## Verification and references

Run the module verify/audit commands, lake build --wfail, verify-all, the live
unittest suite with LEAN_VERIFIER_LIVE_TESTS=1, the independent AxiomAudit.lean and
scripts/check_knowledge.py. Tests use kernel reduction, including decide +kernel;
no native evaluation axiom is introduced. Full command logs and measured counts
belong in the accompanying implementation report.

Conceptual references: C. J. Fidge, *Timestamps in Message-Passing Systems That
Preserve the Partial Ordering* (1988); F. Mattern, *Virtual Time and Global States
of Distributed Systems* (1989). This module fixes its explicit update convention
and proves that model; it is not a transcription of implementation code.

## Public release validation

The [v0.5.27 report](../../docs/release-v0.5.27.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 129 |
| Lean files under Verification/ | 169 top-level + 2 auxiliary = 171 |
| Root-inclusive sources identical to the private snapshot | 172 |
| Clean strict build | 3620 jobs; no warnings |
| Complete verifier audit | 15015 declarations; no violations |
| Pinned independent full audit | 15015 declarations; no violations |
| Public live tests | 74; no failures or skips; 264.431s |
