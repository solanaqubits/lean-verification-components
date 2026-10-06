# Static-epoch edge-chasing contract

The first module studies a CMH-inspired probe detector over Fin n (all n; useful
instances normally have n >= 2). Each WFG edge denotes a blocking AND dependency.
The WFG is fixed for an entire detection execution. Active means no outgoing
wait edge. An initiation enqueues one probe for every outgoing dependency.
Delivery consumes a real pending probe; a blocked non-initiator floods all outgoing
dependencies. Return to a blocked initiator records detection. Active receivers
absorb probes. Channels are an explicit list with arbitrary selection of a pending
occurrence: no FIFO assumption is needed for the static graph results. Local fanout
is atomic; there are no faults or message loss. No global path or cycle test is a
transition guard. No duplicate suppression or message-complexity claim is made.

Induction must reconstruct actual graph paths for queued/sent probes and a nonempty
closed walk for every reported initiator. Nonempty closed walks are the explicit
cycle predicate; simple-cycle extraction and resource-manager operational semantics
are not claimed. A process upstream of a cycle need not receive its own probe.

Prove existence of a finite detection continuation for a cycle, separately from
conditional eventual detection under a stated delivery assumption. An idle schedule
must remain possible absent such an assumption. Demonstrate why checking an edge
only at send time does not justify soundness in an arbitrarily changing acyclic WFG.
No general dynamic CMH theorem or refinement to the original controller algorithm
is claimed. Graph updates require a fresh, isolated epoch with old probes discarded;
that reset is an external contract, not a distributed snapshot implementation.

Source: Chandy, Misra and Haas, Distributed Deadlock Detection, TOCS 1(2), 1983,
https://www.cs.utexas.edu/~misra/scannedPdf.dir/DistrDeadlockDetection.pdf .
The original includes dependent flags, request/reply conditions and reset-on-activity;
this module is the stated static specialization, not the full dynamic algorithm.
