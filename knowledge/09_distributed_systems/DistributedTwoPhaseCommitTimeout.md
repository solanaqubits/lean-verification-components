---
id: DistributedTwoPhaseCommitTimeout
language: en
section: distributed
source: Verification/DistributedTwoPhaseCommitTimeout.lean
source_sha256: 3808f165b34f312a1c8fc101f0b5bba98d2bc7f7d716b5889422a53656524e7c
novelty: not-assessed
status: reviewed
---

# DistributedTwoPhaseCommitTimeout

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedTwoPhaseCommitTimeout.lean)

## Operational model

One transaction has two fixed honest participants, represented by `Bool`, with independent `init`, `prepared`, `committed` and `aborted` states. The existing `DistributedTwoPhaseCommit.Decision` is reused. The coordinator has separate received-yes flags, an optional immutable decision and a running flag. Its commit rule requires both received yes votes; it may abort while undecided. A timeout observation alone carries no evidence of a crash or of a decision.

The network is an unbounded list of yes/no/decision packets. An enabled receive consumes an actual matching packet; a send appends only the packet prescribed by its rule. Scheduling is asynchronous and need not be FIFO. Packets may be dropped. The coordinator can stop permanently; decision packets already in transit can still be received. Preparation and sending a yes vote are one atomic model step. An initial participant may instead abort before voting yes and send a no vote. Participants cannot later revoke their terminal decision or restart voting.

`Step` combines local control guards with packet availability. It does not assume distributed agreement as a transition guard. `Execution` and `Reachable` represent arbitrary finite executions from the empty network and initial local states. Finite control obligations use kernel-checked computation; the proof architecture lifts the control and packet invariants by induction over executions with unbounded queues and lengths. This is not bounded exploration of a fixed number of network steps.

## Safety and indistinguishable histories

The operational invariant relates local terminal states, received votes, the coordinator decision and every queued packet. Agreement rules out one participant being committed while another is aborted. Pre-vote abort is safe on reachable configurations: once a participant aborts before sending yes, the protocol cannot subsequently commit the transaction. This is an execution property, not a statement about arbitrary fabricated states or packets.

For a prepared participant, local observations include its own protocol actions and timeout observations, while hiding the other participant's actions and unobserved coordinator events. The counterexample uses complete local observation sequences of two reachable histories, not merely equality of final local states. In one history the peer has aborted; in the other it has committed. The target participant remains prepared with the same observations.

Any deterministic strategy that must choose a terminal decision from those observations chooses the same decision in both histories. Choosing commit violates agreement in the abort history; choosing abort violates it in the commit history. Waiting is not ruled out. These hypothetical unilateral overrides are outside the legitimate protocol transition relation and do not contradict the reachable-state agreement theorem.

## Conditional blocking and delivery

The blocking theorem assumes both participants are prepared and the coordinator has stopped. Under those explicit hypotheses, absence of a queued decision packet characterizes absence of any finite protocol execution reaching a terminal participant state; the combinatorial equivalence does not additionally require reachability. Reachability and packet provenance are needed for interpreting delivered decisions as safe protocol decisions. Vote delivery, drops and timeout observations cannot create a coordinator decision packet after the coordinator stops.

Conversely, an existing decision packet permits a delivery step and therefore a finite escape for its recipient even after the crash. This is existential enabledness, not guaranteed eventual delivery, termination of both participants or a fairness theorem. A scheduler may withhold or drop the packet. Two prepared participants alone do not imply permanent blocking, and this characterization is not an unrestricted equivalence over all network states.

## Validation and limits

Standalone `verify` completed successfully: 733 declarations in the imported project environment, with dependencies restricted to `propext`, `Classical.choice` and `Quot.sound`. These are declarations, not 733 new independent theorems. See the [verification report](../../docs/two-phase-commit-timeout-verification.en.md) for the complete project checks, commands and scope.

The model covers one transaction and two participants, with an honest fail-stop coordinator and abstract asynchronous packets. It excludes participant crash/recovery, coordinator recovery or replacement, peer/cooperative termination, 3PC, dynamic membership, persistent WAL/fsync, physical clocks, probabilistic delays, Byzantine forgery and a deployed RPC implementation. Resource locks and application database effects are not modeled. No unconditional liveness claim follows.

The original decision-table module remains unchanged; its reflexive agreement statement is not used as a substitute for operational agreement. Python correctness, JSON/SHA-256 implementations, authentication and binding external SimLab inputs to bytes remain separate obligations. Novelty is not assessed.

## Specification reference

Jim Gray and Leslie Lamport, [Consensus on Transaction Commit](https://arxiv.org/pdf/cs/0408036), sections 2–3. Equivalence to the paper’s TLA+ specification is not separately proved.
