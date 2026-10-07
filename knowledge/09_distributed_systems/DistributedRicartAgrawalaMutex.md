---
id: DistributedRicartAgrawalaMutex
language: en
section: distributed
source: Verification/DistributedRicartAgrawalaMutex.lean
source_sha256: 5241798d73c0e06b663aff4057793c93a718562332e31f73bff38440fdd88544
novelty: not-assessed
status: reviewed
---

# Ricart–Agrawala mutual exclusion

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRicartAgrawalaMutex.lean)

## Operational contract

A fixed finite cluster uses NodeId = Fin n. The requested setting n >= 2 is covered;
the same proofs also cover the single-node case, and n=0 has no requests. Processes
are crash-free, non-Byzantine and serialize their own requests. There is no shared
runtime memory: State collects local states and message histories for the semantics.
Each process has Released, Wanted(timestamp), or Held(timestamp), and a natural
Lamport clock. Request creation uses clock+1; REQUEST receipt uses max(clock,t)+1.
The two updates are related explicitly to DistributedLamportClocks.

A request is identified by its timestamp and owner. Local fanout enqueues a REQUEST
for each other node in one atomic local action; receipt at each peer is separate.
REQUEST and REPLY channels are unordered finite sets with unique request/peer keys.
Their pending contents are obtained by subtracting receipt histories. This is an
exact-once, loss-free channel model with arbitrary reordering, not a FIFO queue.
Reply history and received-request history are proof bookkeeping; they are not
unbounded payloads placed on the wire. No message-complexity or memory bound is proved.

Receipt, reply sending, reply delivery, entry and exit are distinct events. A peer
answers when Released or when its Wanted request has lower priority than the
incoming request; it defers while Held or while its own Wanted request comes first.
Deferred obligations are received, unanswered requests whose reply condition is
false. After exit they become serviceable; sending them is subject to local fairness.
A process may make another request before finishing that service, but its advanced
clock cannot give the new request precedence over the received request. Replies
carry the original request identity and the responding peer; one peer cannot count
as two peers and an old response cannot authorize a new invocation.

Entry requires replies from every other node. Exit alone changes Held to Released.
There is no cancellation, fabricated receive, state reset or timestamp wraparound.
Neither mutual exclusion nor future progress is a transition guard.

## Safety and provenance

- priority_irreflexive, priority_asymmetric, priority_transitive and
  priority_trichotomy establish the lexicographic priority order.
- reachable_invariant is proved by induction on actual executions. Its clauses
  track request origin, receipt, replies, clock bounds and the entry barrier.
- permission_order: every sent reply r from peer j precedes every currently active
  request of j. A reply sent before j starts its next request is handled by the
  receive-clock invariant, not by assuming it could never have been sent.
- mutual_exclusion_safety: any two distinct nodes in a reachable configuration
  cannot both be Held. No delivery or fairness assumption is used.
- reply_deferral_until_release excludes a response to a lower-priority incoming
  request while the responder's earlier request remains active.
- historical_request_clock and fresh_request_unique exclude request-key reuse.
  no_stale_reply_for_fresh_request rules out inherited credit from old replies.

## Conditional progress

Run is an infinite sequence starting at initial with an actual enabled transition
at every step, including explicit idle events. ReliableDelivery requires eventual
receipt of each REQUEST and each sent REPLY. WeakFairness requires execution of
continuously enabled reply-send and entry actions; it does not force clients to
create requests. FiniteCS requires every Held invocation eventually to reach
Released. These are separate external assumptions and contain no promise that a
Wanted invocation will enter Held.

request_eventually_enters proves that every request observed in Wanted eventually
reaches Held with the same timestamp, even with later client requests. The proof
uses strong induction on n*timestamp+nodeId to discharge earlier requests, then
finite CS residence, monotone receipt histories, and weak fairness. Thus
deadlock_freedom_minimal_request follows for any current minimal Wanted request,
and deadlock_freedom follows whenever at least one request is pending. A request
that is minimal among current Wanted nodes is not asserted to enter immediately
or to precede every later-generated request.

The explicit withheldRun makes a real request and then idles forever. It never
enters Held and violates ReliableDelivery. It separates channel storage from
actual eventual service. This is an unfair execution, not a counterexample under
the three progress assumptions. No numerical waiting-time bound is proved.

## Regressions and boundaries

Kernel-checked traces cover simultaneous equal timestamps and node-ID tie-breaks,
deferral, two successful invocations, a fresh third request, stale and duplicate
reply rejection, unsolicited replies, a reply sent before the responder's own
request, and three-node delivery reordering. Generic regressions apply the safety
and progress theorems without specializing n.

Crashes, recovery, network partitions, loss, Byzantine behavior, changing membership,
real-time clocks, counter overflow and an implementation of the scheduler are not
modeled. Finite message storage and application code inside the critical section
are not verified. Python, JSON/SHA-256 and SimLab byte binding remain external.
No refinement theorem to the original program or scientific novelty is claimed.

Primary reference: G. Ricart and A. K. Agrawala, *An Optimal Algorithm for Mutual
Exclusion in Computer Networks*, CACM 24(1), 1981, pp. 9–17,
[original paper](https://courses.grainger.illinois.edu/cs425/fa2023/358527.ricart-agrawala.pdf).
The model uses explicit request-tagged replies and separates local reply service;
its proof concerns the stated transition system.

## Measured verification

Base private commit: 6090a301baa8bdbe53dc18cf566a27f7dc448f84.

| Check | Result |
|---|---:|
| MasterSuite direct imports | 115 |
| Lean files in Verification/ | 155 top-level + 2 support = 157 |
| Root-inclusive proof export | 158 byte-identical sources |
| Clean strict build | 3,540 jobs, no warnings |
| Both full project axiom audits | 12,035 declarations, no violations |
| Full private live suite | 63, no failures or skips (247.094s) |
| Exported live suite | 60, no failures or skips (253.342s) |

The module's verify and audit commands each checked 509 transitive declarations.
Only propext, Classical.choice and Quot.sound are permitted. The independent
auditor is pinned at 46024e005996495c65ef609368e11ab39c4222e3. Counts include
definitions and generated declarations, not just mathematical theorems.

Executed in an isolated checkout:

```bash
python3 tools/verifier_skill.py verify Verification/DistributedRicartAgrawalaMutex.lean
python3 tools/verifier_skill.py audit Verification/DistributedRicartAgrawalaMutex.lean
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

The auditor path is local to the validation environment. The English export also
passed its strict build, full live tests, catalog check and independent axiom audit.
Source hashes and exact scope are recorded in the
[validation snapshot](../../tools/validation_snapshot.json). Integration recipes
remain idempotent. Existing subject proofs and the Simon contract pins are unchanged;
only the root, registry components and audit hook changed for integration.
The original workspace HEAD and all 406 tracked-file hashes outside simulations/
were preserved. This task did not write to simulations/ or publish a public release.

Development initially exposed strict-linter issues and a nonreducing decidability
implementation in the trace tests. Direct state case analysis fixed the latter
without changing ReplyCondition. No proof guard, axiom policy or linter was weakened.
The withholding regression also verifies WeakFairness and FiniteCS for that run,
isolating the missing delivery assumption.
