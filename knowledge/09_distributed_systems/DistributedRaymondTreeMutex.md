---
id: DistributedRaymondTreeMutex
language: en
section: distributed
source: Verification/DistributedRaymondTreeMutex.lean
source_sha256: 68fd823edc7264d201c5f80dd277aa662cc2f81a33524885a851e13aa3cf08ec
novelty: not-assessed
status: reviewed
---

# Raymond tree mutual exclusion

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaymondTreeMutex.lean)

## Operational model

Nodes are Fin n on a fixed connected acyclic SimpleGraph. The requested n≥2 case
is covered; the proofs also support one node, while zero nodes admit no initial owner.
Initialization has one token owner, no messages, empty queues and idle processes.
tree_initialization_exists constructs holder routes for every finite tree and owner.

Each node has a holder pointer, FIFO queue, asked flag, mode and local handler phase.
External events invoke ASSIGN_PRIVILEGE followed by MAKE_REQUEST as separately scheduled
internal steps. A node serializes its own handlers; different nodes and network deliveries
interleave. REQUEST receipt appends the sender, a local invocation appends self, and
ASSIGN_PRIVILEGE removes only the head. A head equal to self enters CS; a different head
receives the token. MAKE_REQUEST sends toward holder only for an unforwarded nonempty
queue. Leaving CS invokes the same handlers. Safety is not a transition guard.

The global semantics records a finite set of owners and one optional in-flight
PRIVILEGE (source,destination). Arbitrary State values can violate uniqueness; the
reachable invariant proves owners.card + flight.toList.length = 1. There is no loss,
duplication or fabrication transition. REQUEST histories have occurrence serials solely
for message identity; handlers do not compare serials. Only genuine pending messages
can be received, exactly once. Channels may reorder REQUEST and PRIVILEGE: FIFO network
delivery is not assumed. The local queues are ordinary lists, with Nodup derived from
request-credit accounting rather than imposed by a constructor or insertion filter.

The state machine formalizes this explicit serialization of Raymond's handlers.
A machine-checked refinement to the original pseudocode or an implementation is not
claimed. Histories and traffic counters are ghost observations, not global knowledge
used to decide which client to serve.

## Safety and routing

privilege_conservation_invariant and mutual_exclusion_safety hold on all reachable
states without fairness. Each inCS node is an actual owner. Edge locality ensures
that network traffic and non-self holder pointers respect the fixed graph.

holder_graph_acyclicity proves simple holder paths to the unique owner or, while
the token travels, its destination. At that virtual root the path stops; its outgoing
raw pointer is deliberately ignored. effective_holder_termination bounds the resulting
pointer traversal by fewer than n hops. This is not a claim about all raw pointers:
raw_holder_two_cycle_reachable proves a two-node execution in which a token from 0
to 1 is in flight, holder(0)=1 and holder(1)=0. The destination resets holder to self
on receipt. Treating holder=self as the definition of possession at arbitrary states
would obscure the separately proved ownership invariant.

queue_nodup_preservation derives absence of duplicates. RequestBalance relates
outstanding REQUEST messages, queued neighbour requests, token transit and asked
credits. CreditRouting associates each such demand with its actual provider. These
invariants are proved by induction over all enabled transitions, including reordered
messages and concurrent client requests.

## Conditional absence of starvation

Run is an infinite legal execution, including idle steps. ReliableDelivery requires
eventual receipt of every sent REQUEST and delivery of every in-flight PRIVILEGE.
WeakFairness schedules continuously enabled internal assign/makeRequest steps.
FiniteCS requires eventual leave after every observation of inCS. These contracts do
not assume eventual token acquisition or service, and do not force a new client request.

starvation_freedom_under_liveness proves that every requesting observation eventually
reaches inCS on such a run. Later invocations by other clients are allowed. The proof
first uses the finite FIFO position: infinitely many removals at a node must serve
any existing entry. If a client never enters, its queue cannot be serviced infinitely
often. Finite membership gives a cutoff after the last service of every such node.
Reliable delivery and local fairness propagate its persistent demand along the finite
holder path to the token location, contradicting a permanently unserved owner's queue
once FiniteCS is applied. No strong fairness or global FIFO order is assumed.

Distance to the token is not asserted to decrease under arbitrary concurrent requests.
The liveness theorem gives eventual service, not a latency or waiting-time bound.

## Exact isolated traffic

IsolatedExecution permits arbitrary legal interleavings and delays from quiescent
initialization, with application requests restricted to one node u. At every completed
entry, isolated_request_message_bound proves separately
requestSends = dist(u,initialOwner) and privilegeSends = dist(u,initialOwner), hence
exactly 2*dist messages. Repeated entries by that same client need no further traffic
because the token is retained. Distance zero yields zero network messages.

The proof establishes a token-distance potential: each transfer decreases distance
to u by one. A separate accounting invariant equates REQUEST sends to PRIVILEGE sends
plus pending/queued network work; that work is zero at completed entry. The result
covers all such executions, not just a chosen favorable schedule. It counts sends,
not deliveries, local steps or wall-clock time. On a chain the cost is 2*(n-1) between
endpoints. No universal O(log n) bound, nor this exact bound under contention, is claimed.

## Regressions and Clean Water boundaries

Kernel-checked regressions cover retained-token reentry, two-node transit, fabricated
and duplicate receipt rejection, handler serialization, competing requests on a star,
a REQUEST overtaking PRIVILEGE on the same edge, both clients completing, and a five-node
chain with four REQUEST and four PRIVILEGE sends. Generic regressions preserve arbitrary
n, the actual tree assumptions, all three liveness contracts and the isolated-execution
hypothesis of the traffic theorem. The master suite includes safety, initialization,
routing, queue integrity, liveness, exact traffic and the raw-pointer counterexample.

Node/link failures, token regeneration, dynamic membership or topology, Byzantine
behavior, bounded storage, gate/network implementation and real-time costs are outside
scope. Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open.
Scientific priority has not been assessed.

Primary reference: K. Raymond, *A Tree-Based Algorithm for Distributed Mutual Exclusion*,
ACM TOCS 7(1), 1989, 61–77, [DOI](https://doi.org/10.1145/58564.59295).
The precise transition semantics above governs these proofs.
Measured checks and source hashes: [validation snapshot](../../tools/validation_snapshot.json).

## Historical private implementation and export validation

Base snapshot: `5e714619c1455a47bc58d0f87d8cfe8a94db0c7b`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 121 |
| Lean files under Verification/ | 161 top-level + 2 support = 163 |
| Root-inclusive byte-identical export | 164 sources |
| Clean strict private build | 3585 jobs; no warnings |
| Both full axiom audits | 13610 declarations; no violations |
| Private live tests | 69; no failures or skips; 254.938s |
| Export live tests | 66; no failures or skips; 267.346s |
| Export clean strict build | 3585 jobs; no warnings |

Module verify and audit each covered 687 declarations.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3; executable
SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source records v4.32.0-rc1, with the
executable pinned separately. The registry hook passed separately; no second
independent proof kernel is claimed. Counts include generated declarations.
Project build directories started empty, with isolated pinned dependency caches.
Integration is idempotent. Earlier subject proofs are unchanged. Original workspace
HEAD and 406 tracked files outside simulations/ are preserved. That implementation task made no writes to simulations/ and did not publish a public release.
Fresh public measurements appear in the [v0.5.19 report](../../docs/release-v0.5.19.en.md).
