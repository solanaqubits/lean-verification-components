# Two-participant 3PC design contract

Baseline: fac78833f819eb57ec9d69e67dc80ef5613e4c8c.

There are two fixed participants and a separate original coordinator. One transaction
is implicit in the state. Participants and coordinators may stop irreversibly.
Local votes and terminal decisions survive as mathematical state after a stop;
there is no recovery or disk implementation. A backup is a surviving participant.

Normal execution has individual vote-request, vote response, PreCommit, acknowledgment,
and decision messages. The coordinator may crash between individual sends. Each
phase has one request/response slot per member, recording pending, delivered, replied,
and acknowledged status. This finite channel discipline prohibits duplicate counting.
Packet contents are captured when sent; receiving does not read another process's state.

An external accurate view service detects actual stops, installs one surviving
backup, fences the old epoch at all survivors and cancels its obsolete packets.
This is a strong, explicit environment contract, not a proved election or failure
detector. It does not read participant phases to choose the transaction decision.
New epochs solicit participant reports, use a complete member response set, and
run a separate alignment/acknowledgment phase before the final decision. No participant
commits or aborts merely because a timeout occurred. Further stops invalidate a view
and may require another installation. Network partitions and false suspicions are excluded.

Safety includes decisions of stopped participants. Progress concerns only survivors.
Existence of a finite completion is separate from eventual completion of every weakly
fair execution after a stable accurate view, with no subsequent stops. Fairness
requires execution of continuously enabled concrete send/receive/local actions;
it does not assume termination. Arbitrary tick stuttering remains possible without it.

The protocol has finite control for two participants and at most two view changes
before no participants survive. A generated finite invariant certificate is checked
by ordinary Lean kernel reduction, then lifted by induction to arbitrary execution
lengths. The Python enumerator is untrusted proof-data generation, not an axiom.
No bounded trace search substitutes for closure or progress theorems.

This is a specifically stated 3PC variant with a complete-report termination protocol,
not a refinement proof of Skeen's entire protocol. Reference:
Dale Skeen, Nonblocking Commit Protocols (1981),
https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/Ske81.pdf.
