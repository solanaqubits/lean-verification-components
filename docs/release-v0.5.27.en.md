# Release v0.5.27: Vector clocks and causal order

Private proof snapshot: `035b98853ca060ea70ea70815a56ae55d0d7e1d4`.
Previous public main: `e7311c61a6d187bee760c891f93021c31a108168`.

## Proven scope and assumptions

The new module formalizes vector clocks on Fin n over finite legal histories.
Events have a process, positive local sequence number, and Local, Send or Recv
payload. Message identifiers distinguish actual sends and receives. Every receive
matches an earlier send addressed to that process; timestamps are immutable.
Sends and receives are unique within their respective identifier classes.
Outstanding messages and delivery out of send order are permitted.

HappensBefore is the strict transitive closure of local event order and matching
send-to-receive edges. Its definition does not use vector clocks. CausalPast adds
reflexivity separately. An executable, terminating recurrence computes timestamps
from predecessors using coordinatewise maxima and one increment of the executing
process. The local predecessor fold is proved equal to the last local timestamp;
the message fold is proved equal to the unique delivered send timestamp.
These lemmas recover the ordinary local/send tick and receive max-then-tick rules.

Induction over trace prefixes proves the causal-past invariant: each coordinate
is the maximum local event number of that process in the reflexive causal past,
or zero if empty. It yields both directions of HappensBefore e f iff V(e)<V(f),
timestamp injectivity and causal incomparability iff vector incomparability for
distinct events. Strict vector comparison means coordinatewise <= and unequal
vectors, not strict inequality in every coordinate. The order isomorphism is onto
the image of event timestamps, not onto the entire space of natural-number vectors.
Concurrency here does not mean physical simultaneity or commutation of application
operations. No desired causal invariant is assumed in execution legality.

The n=2 bridge preserves the existing DistributedVectorClocks tick, merge, receive
and comparison operations. Kernel regressions cover independent first events,
a three-process causal relay, out-of-order delivery, outstanding messages, n=1,
and exclusion of self-concurrency. Formal counterexamples show that omitting the
increment can identify causally ordered events and omitting merge can lose a
send-to-receive causal dependency.

These finite-trace safety results require neither FIFO delivery nor an eventual
delivery or scheduler-fairness assumption. Receives must be authentic and match
previous sends; duplicate receives are excluded. Delivery liveness is not claimed.
Counters are unbounded naturals. Bounded-machine counter overflow, node failures,
process restarts, Byzantine timestamp forgery, dynamic membership, clock compression,
physical time and network latency are not modeled. Python correctness, JSON/SHA-256
correctness and SimLab-to-Lean correspondence remain open. Novelty is not assessed.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 129 |
| Lean files under Verification/ | 169 top-level + 2 auxiliary = 171 |
| Root-inclusive sources identical to the private snapshot | 172 |
| Clean strict build | 3620 jobs; no warnings |
| Complete verifier audit | 15015 declarations; no violations |
| Pinned independent full audit | 15015 declarations; no violations |
| Public live tests | 74; no failures or skips; 264.431s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

All 172 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.27. Existing tags are not overwritten. This is not an atomic push.
A separate receipt records the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedVectorClocksCausalOrder.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
