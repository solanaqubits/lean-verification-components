---
id: DistributedMultiPaxosConsensus
language: en
section: distributed
source: Verification/DistributedMultiPaxosConsensus.lean
source_sha256: bd34269434e9cd7ea1aeddbdb27dd3eb38b81277f2963cfc32b16f814b553185
novelty: not-assessed
status: reviewed
---

# Operational Multi-Paxos: inter-ballot agreement and executed prefixes

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedMultiPaxosConsensus.lean)

## Model and proved results

Nodes are Fin n, slots are natural numbers, and application values have an arbitrary
Lean Type. The intended group is static and nonempty. The general safety lemmas
also cover the vacuous n=0 case; executable examples use n=1 and n=3.
Ballot contains a natural counter and a node ID. Its linear order is implemented
by counter*n+node.val and proved equivalent to lexicographic order.

Each acceptor keeps an optional promise and the latest accepted pair per slot.
Prepare, Promise with a finite snapshot, Accept, and Accepted are actual protocol
messages. Promise raises the epoch only strictly; acceptance requires an epoch
at least the promise and raises the promise as well. ExactSnapshot serializes
all occupied slots, and serialize_exact proves that such finite serialization
exists in every reachable configuration.

A majority of Promise messages installs an immutable certificate for a ballot.
One certificate supports proposals for arbitrarily many distinct slots. Selection
uses the highest accepted ballot in that slot across the certificate snapshots;
a slot empty in all snapshots permits a fresh client value. A proposal for
(ballot,slot) is recorded once. Unique leader identity alone would not prevent
repeated arbitrary client choices, so write-once proposal storage is explicit.
The owner of a normal proposal is the leader encoded in its ballot.

Chosen uses historical Accepted events, not only current acceptor registers.
Overwriting the current entry at a higher ballot does not undo an earlier choice.
A current majority is proved to imply historical choice. Reachability induction
derives promise monotonicity, accepted-entry bounds, message provenance, proposal
uniqueness, snapshot origins and coverage of all lower-ballot historical votes.
The snapshot coverage invariant also excludes votes cast after a higher promise.
None of these invariants assumes Agreement, SingleVote or safe-value selection
as an external safety oracle.

Strong induction on ballot rank, quorum intersection and the maximum-selection
rule prove preservation of an already chosen slot value by every higher-ballot
proposal in the same execution. This yields Agreement across arbitrary ballots.
The previous DistributedPaxos.SingleVote premise is derived for the projected
acceptance history, for any encoding of application values into natural numbers.

The core retains a sent-message archive. Network adds a finite list interpreted
as a message multiset: inputs can be selected out of order, delayed, duplicated
or dropped. Packets may remain available for retransmission. Protocol actions
require their inputs in the network; no FIFO or reliable-delivery assumption is
needed for safety. Network refinement proves that all available messages came
from the protocol archive and that the core is reachable. Conversely, every core
execution has a loss-free network realization. There is no per-recipient channel
or implementation-level serialization model.

System adds per-replica executed lists. Execution appends only the next slot,
using a majority of available Accepted messages. Induction derives a hole-free
chosen prefix at every replica, hence pairwise prefix comparability. Equal-length
prefixes produce equal states of the same deterministic fold from the same initial
state. Execution is enabled by this condition, not forced immediately by it.

## Executable regressions and faulty variants

Three nodes choose three distinct slot values after one Prepare and one installed
certificate. Another trace changes leaders and preserves an earlier choice;
a stale Accept is rejected. A chosen slot beyond a hole cannot advance the empty
executed prefix. A single replica has an actual reachable execution of one command.
All core regression traces have network realizations.

FaultStep defines separate weakened protocols. Omitting maximum-ballot selection
allows distinct values at different ballots. Allowing a second actor to reuse
another leader's ballot and overwrite its slot proposal allows distinct values
at the same ballot. These are reachable counterexample traces, not just unrelated
records. Neither faulty constructor belongs to the correct Step relation.

## Clean Water boundaries

The result is safety of an ideal static, non-Byzantine asynchronous protocol and
its executed prefixes. Arbitrary scheduling can stop progress forever. No liveness
theorem or FLP theorem is proved here. A future progress contract needs a stable
leader, an available quorum, suitable delivery/retransmission and scheduling
fairness; a stable leader alone does not suffice. Stopping processes can be modeled
by absence of steps. Restart after lost promise/accepted state is outside scope.
Reconfiguration, checkpointing, compaction, durable-storage recovery, Byzantine
forgery, client deduplication, exactly-once effects and linearizability are not
proved. Python, JSON/SHA-256 and SimLab correctness obligations remain open.
Scientific novelty is not assessed.

References: [Lamport, Paxos Made Simple (2001)](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf);
[Fischer, Lynch, Paterson (1985)](https://groups.csail.mit.edu/tds/papers/Lynch/jacm85.pdf).

## Validation

Base snapshot: 2fff8672332796ab463396cdf799e0112e3886eb.
All project and export checks passed; measured results follow.

## Source theorem links

- [ballot_lt_iff](../../Verification/DistributedMultiPaxosConsensus.lean#L49)
- [quorum_intersection](../../Verification/DistributedMultiPaxosConsensus.lean#L92)
- [promise_monotonicity](../../Verification/DistributedMultiPaxosConsensus.lean#L201)
- [reachable_invariants](../../Verification/DistributedMultiPaxosConsensus.lean#L415)
- [proposal_uniqueness](../../Verification/DistributedMultiPaxosConsensus.lean#L420)
- [inter_ballot_value_preservation](../../Verification/DistributedMultiPaxosConsensus.lean#L433)
- [multi_paxos_slot_agreement](../../Verification/DistributedMultiPaxosConsensus.lean#L461)
- [state_machine_convergence](../../Verification/DistributedMultiPaxosConsensus.lean#L503)
- [serialize_exact](../../Verification/DistributedMultiPaxosConsensus.lean#L571)
- [network_refinement](../../Verification/DistributedMultiPaxosConsensus.lean#L609)
- [reachable_replica_prefixes](../../Verification/DistributedMultiPaxosConsensus.lean#L725)
- [counterexample_ignore_max_ballot](../../Verification/DistributedMultiPaxosConsensus.lean#L1017)
- [counterexample_reused_ballot](../../Verification/DistributedMultiPaxosConsensus.lean#L1028)
- [derived_single_vote](../../Verification/DistributedMultiPaxosConsensus.lean#L1051)
- [distributed_multi_paxos_consensus_master_suite](../../Verification/DistributedMultiPaxosConsensus.lean#L1116)

## Private snapshot validation: Operational Multi-Paxos

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 137 |
| Lean sources | 179 under Verification/; 180 including root |
| Strict clean private build | 3727 jobs; no warnings |
| Both full axiom audits | 17615 declarations; no violations |
| Private live tests | 85; no failures or skips; 277.39s |
| Export live tests | 82; no failures or skips; 291.973s |
| Strict clean export build | 3727 jobs; no warnings |

Module verify and audit each covered 740 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent audit source commit: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both builds started with empty project
.lake/build directories and isolated pinned dependency caches. All 180 exported
Lean files match byte-for-byte; repeated exports agree. Integration is idempotent.
Original HEAD and 406 tracked files are preserved. No writes to simulations/.
That earlier private integration did not publish a public release.

Inter-ballot agreement is derived from protocol transitions. Chosen records
historical votes. Immutable certificates and write-once proposals enforce phase
one reuse and per-slot uniqueness. Network and replica execution refine the core.
Safety does not require delivery fairness; no liveness theorem is claimed.

## Public release validation

The [v0.5.35 report](../../docs/release-v0.5.35.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 137 |
| Lean files under Verification/ | 177 top-level + 2 auxiliary = 179 |
| Root-inclusive sources identical to the private snapshot | 180 |
| Clean strict build | 3727 jobs; no warnings |
| Complete verifier audit | 17615 declarations; no violations |
| Pinned independent full audit | 17615 declarations; no violations |
| Public live tests | 82; no failures or skips; 278.315s |
