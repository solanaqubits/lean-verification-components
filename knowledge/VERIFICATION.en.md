# Public verification record

[Knowledge base](README.md) · [Release v0.5.30](../docs/release-v0.5.30.en.md)

## Current public snapshot: State-based LWW register

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 132 |
| Lean files under Verification/ | 172 top-level + 2 auxiliary = 174 |
| Root-inclusive sources identical to the private snapshot | 175 |
| Clean strict build | 3623 jobs; no warnings |
| Complete verifier audit | 16006 declarations; no violations |
| Pinned independent full audit | 16006 declarations; no violations |
| Public live tests | 77; no failures or skips; 271.527s |

All 175 proof sources match private snapshot `fb5b736e7f4794f96e1ee5f61d9b50af7cd8a571`.

The model is a state-based LWW register for a fixed group of replicas. Stamps
are ordered lexicographically by logical counter and replica ID. Operational
freshness proves that equal issued stamps carry equal values. Merge forms a
bounded join semilattice on states compatible with a common valid history;
commutativity is not asserted for malformed conflicting values at one full stamp.

The payload is the maximum of its included update history. Equal included update
sets imply equal payloads, independently of ordering and duplicates. This strong
convergence result is distinct from conditional dissemination. Reliable availability
of authentic immutable snapshots, fair sending and per-useful-snapshot weak
fairness imply eventual information subsumption. After new writes cease, all
replica payloads permanently stabilize to the global maximum.

An incremental adapter replays snapshots along actual DistributedCausalBroadcast
application delivery logs. Its finite-batch and checkpoint theorems derive
saturation from reliable arrival and weak fairness. A coupled serializer and
arbitrary ongoing-write transport implementation are not asserted. Regressions
cover bottom, one replica, concurrent equal counters resolved by ID, stale and
duplicate snapshots, fresh relay writes, and malformed tie/stale-write rules.

Convergence concerns the register value, not clocks or ghost logs. Linearizability,
distributed consensus, preservation of all concurrent versions, physical-clock
or NTP synchronization, crash recovery or recovery after nonvolatile-memory failure,
Byzantine participants and dynamic membership are not modeled. Mathematical natural
counters do not overflow; bounded machine-counter implementations are outside scope.
Python, JSON/SHA-256 and SimLab obligations remain open. Scientific novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.29](../docs/release-v0.5.29.en.md)

## Historical public snapshot v0.5.29: Causal broadcast

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 131 |
| Lean files under Verification/ | 171 top-level + 2 auxiliary = 173 |
| Root-inclusive sources identical to the private snapshot | 174 |
| Clean strict build | 3622 jobs; no warnings |
| Complete verifier audit | 15608 declarations; no violations |
| Pinned independent full audit | 15608 declarations; no violations |
| Public live tests | 76; no failures or skips; 272.330s |

All 174 proof sources match private snapshot `77948161a169a42dee824a8a2e1236e582665be4`.

DistributedCausalBroadcast formalizes fixed-group causal multicast with authentic
immutable messages and delivered-prefix vector counters. Broadcast atomically
self-delivers; Arrive only buffers; Deliver requires the next sender sequence
and every cross-sender dependency. Induction over operational transitions proves
continuous prefixes, at-most-once application delivery, exact reflexive causal-past
timestamps and causal delivery safety: if m1 precedes m2 and m2 is delivered at t,
m1 was delivered at a strictly earlier step. Independent message causality is
linked to actual delivery-before-broadcast events, not defined by vector comparison.

Eventual delivery requires reliable network arrival and per-message weak fairness.
It follows by induction on finite causal pasts; readiness is derived rather than
assumed. Reordered and duplicate network arrivals are allowed. Regressions cover
three-process relay, independent broadcasts, immediate self-delivery, a one-node
group, and counterexamples to weakened cross-sender or next-sequence guards.
Buffered arrival alone does not create an application causal dependency.

Causal order does not imply total order or physical simultaneity. Crashes, restarts,
Byzantine messages, dynamic membership, bounded-machine counter overflow, vector
compression and physical delays are outside this model. Mathematical natural
numbers themselves do not overflow. The full ISIS membership and virtual-synchrony
protocol is not claimed. Python correctness, JSON/SHA-256 correctness and the
SimLab-to-Lean correspondence remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.28](../docs/release-v0.5.28.en.md)

## Historical public snapshot v0.5.28: Postselected photonic controlled-Z

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 130 |
| Lean files under Verification/ | 170 top-level + 2 auxiliary = 172 |
| Root-inclusive sources identical to the private snapshot | 173 |
| Clean strict build | 3621 jobs; no warnings |
| Complete verifier audit | 15177 declarations; no violations |
| Pinned independent full audit | 15177 declarations; no violations |
| Public live tests | 75; no failures or skips; 269.270s |

All 173 proof sources match private snapshot `629e2ceb6441538c0abdf75331db6e1be6f2bcd7`.

The module derives a coincidence-postselected controlled-Z operation from three
disjoint ideal lossless beam splitters. The six modes are a0,a1,b0,b1,va,vb;
the pairs (a0,va), (a1,b1), (b0,vb) use the imported complex B(T), for 0 <= T <= 1.
The normalized two-boson basis enumerates 21 unordered mode pairs. Equal-mode
creation monomials carry the factor 1/sqrt(2). A generic polynomial-substitution
theorem connects the symmetric lift to single-particle scattering. Both the
six-mode network and its 21-dimensional two-photon lift are proved unitary.

The dual-rail encoding J is an isometry. Its orthogonal projection JJ† accepts
exactly one photon in each logical rail pair and none in the auxiliary modes.
The success map is defined by compression K(T)=J†U(T)J; its diagonal
(T,T,T,2T-1) is derived. At T=1/3, K=CZ/3 and K†K=I/9. Every normalized input
has success probability 1/9; the normalized successful branch is CZ psi.
The matrix identity K rho K†=(1/9)CZ rho CZ† holds for every matrix rho,
and the success trace is 1/9 for every trace-one density matrix.

CZ is unitary, Hermitian and involutive. Four Pauli conjugation identities are
proved. The product input |++> becomes the graph state (1,1,1,-1)/2. A local
Hadamard maps this state to the Bell state Phi+. Its global density is pure;
both reduced densities are I2/2 and reduced purity is 1/2. The state is proved
not to factor into two local vectors. A product-state purity theorem supplies
an additional bridge to pure-state separability. A general theory of convex
mixed-state separability is not claimed.

Regressions cover all four basis inputs with success probability 1/9 and signs
(+,+,+,-), T=1/2 with K=diag(1/2,1/2,1/2,0), and T=1 with K=I. At T=1/2,
the |11> input bunches in the central computational modes and fails coincidence
selection; this particular input does not leak into the auxiliary vacuum modes.

This is a finite homogeneous-polynomial model of ideal indistinguishable bosons,
not an infinite Fock-space or canonical-commutation-relation construction.
Born-rule interpretation and ideal coincidence selection are model assumptions.
Full scattering is unitary; the accepted branch is conditional. Exact probability
1/9 does not mean deterministic success or a nondestructive herald.
Scalable KLM architectures, Kerr interactions, spectral wave-packet overlap,
partial distinguishability, photon loss and detector noise are not modeled.
Python correctness, JSON/SHA-256 correctness and SimLab-to-Lean correspondence
remain open. Novelty is not assessed. The network isolates the controlled-sign
core associated with Ralph, Langford, Bell and White (2002), using the project's
complex phase convention; exact identity with the paper's full CNOT diagram
is not asserted.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.27](../docs/release-v0.5.27.en.md)

## Historical public snapshot v0.5.27: Vector clocks and causal order

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 129 |
| Lean files under Verification/ | 169 top-level + 2 auxiliary = 171 |
| Root-inclusive sources identical to the private snapshot | 172 |
| Clean strict build | 3620 jobs; no warnings |
| Complete verifier audit | 15015 declarations; no violations |
| Pinned independent full audit | 15015 declarations; no violations |
| Public live tests | 74; no failures or skips; 264.431s |

All 172 proof sources match private snapshot `035b98853ca060ea70ea70815a56ae55d0d7e1d4`.

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

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.26](../docs/release-v0.5.26.en.md)

## Historical public snapshot v0.5.26: Raymond tree message complexity

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 128 |
| Lean files under Verification/ | 168 top-level + 2 auxiliary = 170 |
| Root-inclusive sources identical to the private snapshot | 171 |
| Clean strict build | 3619 jobs; no warnings |
| Complete verifier audit | 14727 declarations; no violations |
| Pinned independent full audit | 14727 declarations; no violations |
| Public live tests | 73; no failures or skips; 267.488s |

All 171 proof sources match private snapshot `9cc2a20c343c62e126b0fc1f7fd34fd4ad88f78a`.

The module reuses DistributedRaymondTreeMutex without changing its transition
semantics. A completed isolated request starts with one token owner, empty queues
and no network traffic. Only one client invokes requests. The imported accounting
identity counts actual network sends: REQUEST=dist(u,t), PRIVILEGE=dist(u,t).
Local handler steps, message receipt and elapsed time are not counted as sends.

Finite maxima define treeDiameter and treeHeight. The new theorems establish
M(u,t)=2 dist(u,t)<=2 diameter<=4 height(root). Reaching 4h requires an explicit
pair of maximum-depth vertices whose shortest path passes through the root.
Height alone does not imply diameter=2h.

Finite legal completion is proved separately, by a bounded increasing integer
service rank and existence of an enabled service step while the client remains
requesting. The diameter theorem supplies valid holder routes, an actual finite
IsolatedExecution reaching inCS and send count exactly 2 diameter. This is an
existence theorem using classical choice, not an executable scheduler or a claim
that every arbitrary schedule terminates. No service assumption is inserted into
the existence witness. The prior module's fairness contracts remain separate.

Complete k-ary trees are explicit graphs of words over Fin k of length at most h,
with dropLast as parent. Connectivity and acyclicity are proved. For k>=2, h>=1:
N=sum(j=0..h) k^j=(k^(h+1)-1)/(k-1), height=h, diameter=2h, and Mmax=4h.
The inequalities k^h<=N<k^(h+1) give h=Nat.log k N. A Mathlib IsBigO theorem
formalizes logarithmic cost in actual vertex count, atTop in h for each fixed k.
Isomorphisms transfer these graphs to Fin(card V), where actual protocol traces
attain the stated maxima. Chain and star graphs are explicitly constructed too.

Regressions cover local ownership (zero sends), a chain (2(N-1)), a star for N>=3
(four sends), and the binary height-three tree (15 nodes, diameter six, exactly
12 sends and not eight). A ternary height-two example has 13 nodes and eight
sends. Degenerate single-node and height-zero counting cases are also checked.

Only isolated REQUEST and PRIVILEGE sends are analyzed. Concurrent request costs,
amortized queues, random traffic, physical latency and faults are not modeled by
this extension. Logarithmic cost is specific to this tree family; a chain remains
linear. Implementation refinement, Python correctness, JSON/SHA-256 correctness
and SimLab-to-Lean correspondence remain open. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.25](../docs/release-v0.5.25.en.md)

## Historical public snapshot v0.5.25: Two-photon Hong–Ou–Mandel interference

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 127 |
| Lean files under Verification/ | 167 top-level + 2 auxiliary = 169 |
| Root-inclusive sources identical to the private snapshot | 170 |
| Clean strict build | 3618 jobs; no warnings |
| Complete verifier audit | 14510 declarations; no violations |
| Pinned independent full audit | 14510 declarations; no violations |
| Public live tests | 72; no failures or skips; 260.670s |

All 170 proof sources match private snapshot `611ba17cda45a492ff45c83f698456408ea402e8`.

For 0<=T<=1 and R=1-T, the normalized occupation basis is
|2,0>, |1,1>, |0,2>. The symmetric-square construction is tied to the imported
complex splitter B(T) by a polynomial substitution theorem with factorial
normalizations. This is a finite two-photon sector, not a construction of the
full Fock space or canonical commutation relations.

The lifted matrix U_two_photon satisfies both U†U=I and UU†=I and preserves
the squared Hermitian norm of arbitrary complex input vectors. On |1,1>,
the actual output is (i sqrt(2TR), T-R, i sqrt(2TR)). Born probabilities are
defined as Complex.normSq of these components, yielding P20=P02=2TR and
P11=(2T-1)², nonnegative and summing to one. At T=1/2, P11=0 and the exact
state is (i/sqrt(2))(|2,0>+|0,2>).

The single-mode phase gauge diag(1,i) induces the occupation gauge
Q=diag(1,i,-1). The lifted complex matrix equals Q U_real Q†, and U_real
agrees with QuantumBeamSplitterTransform. For general inputs both input and
output coordinates are rephased. For |1,1> this changes the input by only
a global phase, so all three outcome probabilities agree directly.

The distinguishable reference retains particle labels and assigns independent
joint weights |B(j,0)|² |B(k,1)|². Their nonnegativity, normalization and
factorization into actual marginals are proved. Coincidence is the disjoint
event j!=k, giving P_dist=T²+R²>=1/2>0. The reference assumption is explicit.
HOM visibility uses (P_dist-P11)/P_dist, not a maximum-plus-minimum denominator.
It equals 2TR/(T²+R²), lies in [0,1], and equals one exactly when T=1/2.

Ideal indistinguishable modes, the stated preparation and lossless optics are
model assumptions. The temporal wave-packet profile P(tau), spectral overlap,
dip shape or width, partial distinguishability, photon loss, frequency jitter,
detector noise and hardware implementation are not modeled. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.24](../docs/release-v0.5.24.en.md)

## Historical public snapshot v0.5.24: Complex beam splitter and MZI phase response

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 126 |
| Lean files under Verification/ | 166 top-level + 2 auxiliary = 168 |
| Root-inclusive sources identical to the private snapshot | 169 |
| Clean strict build | 3617 jobs; no warnings |
| Complete verifier audit | 14415 declarations; no violations |
| Pinned independent full audit | 14415 declarations; no violations |
| Public live tests | 71; no failures or skips; 263.419s |

All 169 proof sources match private snapshot `0556810415b74197251b6a7e8c2e712f5375b97f`.

For 0<=T<=1 the lossless symmetric splitter is
B=[[sqrt(T),i sqrt(1-T)],[i sqrt(1-T),sqrt(T)]]. The arm operator is
D(phi)=diag(exp(i phi),1), and U=B†DB explicitly uses the inverse second splitter.
Both inverse identities and Hermitian Euclidean norm preservation hold for B and U.
The reflection factor i=exp(i pi/2) belongs to this chosen convention, not every
reflecting device; a zero component does not have a defined relative phase.

For input (1,0), the actual matrix output gives c0=T exp(i phi)+1-T and
c1=i sqrt(T)sqrt(1-T)(1-exp(i phi)). Probabilities are defined by Complex.normSq,
then proved to equal P0=1-4T(1-T)sin²(phi/2) and P1=4T(1-T)sin²(phi/2).
They lie in [0,1], sum to one, have period 2pi and satisfy the endpoint cases.
At T=1/2 they are cos²(phi/2) and sin²(phi/2). For nonnegative input power,
the corresponding intensities exactly equal the SolarisMithraCore formulas.

For positive I0, port-0 extrema are I0 and I0(2T-1)², with both bounds proved
and attained at phases 0 and pi. They construct a valid InterferencePattern with
V=4T(1-T)/(1+(2T-1)²), equal to one at T=1/2. A constant phase offset shifts
the attainment points but leaves the extrema and visibility unchanged.
Geometric dependence is substitution under the external premise phi=kappa*DeltaL+phi0;
kappa=0 does not allow scanning the phase curve by changing path length.

These results follow from the specified complex matrix model, not from Maxwell's
equations. Material dispersion, polarization, loss, detectors, hardware synthesis
and full Fock-space dynamics are not modeled. Decoherence and stochastic phase
noise are not inferred from a deterministic phase offset. Python, JSON/SHA-256
and SimLab-to-Lean correspondence remain open obligations. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.23](../docs/release-v0.5.23.en.md)

## Historical public snapshot v0.5.23: Balanced Deutsch-Jozsa oracle classification

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 125 |
| Lean files under Verification/ | 165 top-level + 2 auxiliary = 167 |
| Root-inclusive sources identical to the private snapshot | 168 |
| Clean strict build | 3616 jobs; no warnings |
| Complete verifier audit | 14330 declarations; no violations |
| Pinned independent full audit | 14330 declarations; no violations |
| Public live tests | 70; no failures or skips; 262.919s |

All 168 proof sources match private snapshot `2dba8201d6046e7017c2353c95941dd5d51237f8`.

The module reuses Bits n, IsBalanced, runDJ and outcomeWeight from
QuantumDeutschJozsaGeneral. BalancedFamily is the subtype of all oracles satisfying
that existing predicate. Support and Boolean characteristic maps are explicit
inverses. For n>=1 their restriction gives an equivalence with subsets of
cardinality 2^(n-1), yielding choose(2^n,2^(n-1)) via Finset.card_powersetCard.

For n=0 the domain is a singleton and the balanced family is empty. The unguarded
formula is false because natural subtraction saturates: choose(2^0,2^(0-1))=1.
The total formula branches on n=0. Counts for n=0,1,2,3 are exactly 0,2,6,70.
Positive cases use the general theorem and kernel reduction of binomial arithmetic.

For arbitrary n and arbitrary f, without DJPromise, balance is equivalent to zero
signed-mean amplitude, zero squared probability, and zero operational amplitude
and outcomeWeight at the all-zero basis state in runDJ. The circuit result is
inherited through the existing proved amplitude bridge, not postulated afresh.
The first-bit projection witnesses balance for every positive n. A relabeling
between Bits n and Fin (2^n) preserves trueCount and IsBalanced.

Under DJPromise a paired theorem proves (P0=0 iff balanced) and (P0=1 iff constant).
This is not a claim to classify arbitrary unpromised oracles from one nonzero
measurement. The finite cardinality presentation uses noncomputable/classical
constructions where needed. Efficient enumeration, generation or sampling of
oracles, asymptotic density, hardware synthesis and physical noise are not modeled.
Python, JSON/SHA-256 and SimLab remain open obligations. Novelty is not assessed.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.22](../docs/release-v0.5.22.en.md)

## Historical public snapshot v0.5.22: General Chandy-Lamport snapshots

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 124 |
| Lean files under Verification/ | 164 top-level + 2 auxiliary = 166 |
| Root-inclusive sources identical to the private snapshot | 167 |
| Clean strict build | 3615 jobs; no warnings |
| Complete verifier audit | 14271 declarations; no violations |
| Pinned independent full audit | 14271 declarations; no violations |
| Public live tests | 69; no failures or skips; 260.408s |

All 167 proof sources match private snapshot `d06eee279392f800cbb8a5ff8dff3af30b051edc`.

The model covers arbitrary finite directed networks with edge-indexed FIFO queues,
arbitrary application payloads and local data. A node captures its actual local
value and event counter once, atomically appending markers to outgoing queues.
The cut is consistent: every receipt before the destination cut has a matching
send before the source cut. Phase observations are linked to strict event order.

Every closed channel records exactly the ordered crossing messages: sent before
the sender cut and received after the receiver cut. Packet identities distinguish
repeated payloads. Snapshots and closed channel records remain unchanged.

Termination requires directed reachability of all nodes from the initiator,
ReliableDelivery and WeakFairness. ReliableDelivery means each already queued
item is eventually processed or offered at the FIFO head; it includes progress
past earlier packets and is stronger than absence of transport loss alone.
Weak fairness governs continuously enabled initiation and marker reactions.
The theorem supplies a finite common completion index, not a uniform latency bound.
An explicit reliable fair execution witnesses satisfiability of the assumptions.

A non-FIFO counterexample adds only an adjacent swap: a marker overtakes an older
packet, and the closed channel record misses that packet. This demonstrates failure
of exact recording; it does not claim every reordering violates cut consistency.
A reliable fair disconnected execution demonstrates the need for root reachability.

One snapshot and fixed topology are modeled. Permutation/causal equivalence via
commuting application events, global termination detection, snapshot collection,
crashes, loss, recovery, dynamic topology, overlapping snapshots and Byzantine
behavior are outside the model. Python, JSON/SHA-256 and SimLab remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.21](../docs/release-v0.5.21.en.md)

## Historical public snapshot v0.5.21: Schnorr identification

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 123 |
| Lean files under Verification/ | 163 top-level + 2 auxiliary = 165 |
| Root-inclusive sources identical to the private snapshot | 166 |
| Clean strict build | 3614 jobs; no warnings |
| Complete verifier audit | 13805 declarations; no violations |
| Pinned independent full audit | 13805 declarations; no violations |
| Public live tests | 68; no failures or skips; 257.020s |

All 166 proof sources match private snapshot `0c7104839e071108f4f9d08d6a75c4799f6d2581`.

The model reuses the Pedersen Setup: an abstract finite additive group of prime
order q with Module (ZMod q) structure. Only the nonzero generator g is used;
oneGeneratorSetup permits h=g. A public Statement contains X, with witness
relation X=x•g. Every group element has a unique witness, derived from the setup.

Perfect completeness proves s•g=R+c•X for R=r•g and s=r+c*x. Two accepting
transcripts with the same R and distinct challenges c₁≠c₂ yield c₁−c₂≠0 and
X=((s₁−s₂)/(c₁−c₂))•g. If X=x•g, the extractor returns exactly x.

The simulator takes only X,c and a uniform response s, and sets R=s•g−c•X.
Perfect special HVZK is an exact equality of full joint transcript PMFs for each
fixed c. The explicit bijection r↦r+c*x relates the real nonce and simulated
response. Equality also holds for any fixed independent challenge PMF, including
the uniform verifier challenge; the real interaction samples its nonce first.
The support is exactly the accepting transcripts with the specified challenge.
Zero secrets, zero nonces, zero challenges and q=2 are included.

Special soundness here is algebraic extraction from two supplied transcripts.
No PPT adversary model, polynomial runtime, adversarial rewinding algorithm,
impersonation bound or computational DLOG hardness is proved. Adaptive malicious
verifiers choosing challenges as a function of R, random oracles, Fiat-Shamir,
noninteractive signatures, concurrent composition and implementation security
are outside this module. The older real-scalar modules remain unchanged.
Python, JSON/SHA-256 and SimLab linkage remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1,
and the executable is pinned separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Public checks were rerun against this release candidate.
Counts include generated declarations, not just independent mathematical theorems.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.20](../docs/release-v0.5.20.en.md)

## Historical public snapshot v0.5.20: Pedersen homomorphic sums

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 122 |
| Lean files under Verification/ | 162 top-level + 2 auxiliary = 164 |
| Root-inclusive sources identical to the private snapshot | 165 |
| Clean strict build | 3613 jobs; no warnings |
| Complete verifier audit | 13704 declarations; no violations |
| Pinned independent full audit | 13704 declarations; no violations |
| Public live tests | 67; no failures or skips; 248.050s |

All 165 proof sources match private snapshot `2c01798362d54124a711be83a0855e40dbf0efdc`.

The setup is an abstract finite additive abelian group of prime order q, with a
Module (ZMod q) structure and two nonzero generators g,h. No discrete logarithm
relation is supplied. Finite weighted sums satisfy
sum cᵢ • C(mᵢ,rᵢ) = C(sum cᵢmᵢ,sum cᵢrᵢ), including empty families.

Perfect hiding is an exact PMF equality: uniform masking gives a uniform group
value for every fixed message. Aggregate hiding requires an index in the family
with a nonzero coefficient and a fresh independent uniform mask. Coefficients
and messages are fixed; the remaining masks may have an arbitrary joint law.
The refreshed coordinate's joint law with the remaining vector is proved to
factor. All-zero weights give a point mass at zero, not a uniform group value.
Uniform marginals alone do not suffice: correlated masks [t,−t] cancel exactly.

A collision C(m,r)=C(m′,r′) with m≠m′ implies r≠r′ and
h = ((m−m′)/(r′−r)) • g. This is an algebraic DLOG extraction, not a theorem of
computational binding or DLOG hardness. Aggregation concerns the scalar weighted
sum; vectors [1,0] and [0,1] have equal aggregates under weights [1,1].
A concrete setup proves satisfiability, while a known generator relation permits
alternative openings. The older real-scalar commitment module is unchanged.

PPT adversaries, computational hardness, IND-CPA/EUF-CMA games, multi-generator
vector commitments and implementation security are not claimed. Python,
JSON/SHA-256 and SimLab linkage remain open obligations.

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Its deleted temporary checkout was restored at that commit and rebuilt with Lean
v4.33.1; the resulting binary exactly matches the previous pinned hash.
The auditor source toolchain file records v4.32.0-rc1; the executable is pinned
separately. No second independent proof kernel is asserted.

The project build directory started empty; pinned dependency caches were copied
into the isolated tree. Actual public checks were rerun, rather than inferred
from the earlier private/export evidence. Counts include generated declarations.

[Commands and hashes](../tools/validation_snapshot.json).


[Knowledge base](README.md) · [Release v0.5.19](../docs/release-v0.5.19.en.md)

## Historical public snapshot v0.5.19: Raymond tree mutual exclusion

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 121 |
| Lean files under Verification/ | 161 top-level + 2 auxiliary = 163 |
| Root-inclusive sources identical to the private snapshot | 164 |
| Clean strict build | 3585 jobs; no warnings |
| Complete verifier audit | 13610 declarations; no violations |
| Pinned independent full audit | 13610 declarations; no violations |
| Public live tests | 66; no failures or skips; 253.584s |

All 164 Lean sources including the root file match private snapshot `d4a72dfb113fbdb5f4a4157db0f9f824ff5ffb48`.
Both complete audits permit only propext, Classical.choice and Quot.sound.
The strict registry hook and knowledge catalog passed separately. The two nested
specification files remain auxiliary tooling rather than subject-module increments.
[Hashes and measured commands](../tools/validation_snapshot.json).

[Raymond contract](09_distributed_systems/DistributedRaymondTreeMutex.md).

The model uses a fixed finite connected acyclic graph, one initial token owner,
empty queues/channels, and serialized local ASSIGN_PRIVILEGE / MAKE_REQUEST handlers.
The network permits reordering; receipt is exact-once and rejects fabricated messages.
Occurrence serials identify REQUEST packets, not protocol priorities. No mechanical
refinement to an implementation or the original pseudocode is asserted.

Reachable-state proofs establish exactly one privilege token across nodes and transit,
mutual exclusion (each inCS node is an actual owner), and duplicate-free FIFO queues.
Queue uniqueness is derived from request accounting, not imposed by a constructor.

Effective holder paths end at the current owner or the destination of an in-flight
PRIVILEGE. A reachable two-node counterexample has holder(0)=1 and holder(1)=0 while
the token travels from 0 to 1. Thus raw holder pointers need not be globally acyclic;
the effective path stops at the packet destination and suppresses its outgoing edge.

Every requesting observation eventually reaches inCS under ReliableDelivery (eventual
receipt of every REQUEST and PRIVILEGE), WeakFairness of local internal handlers and
FiniteCS (eventual exit). These contracts do not assume eventual service. Concurrent
later requests are allowed. The proof uses finite FIFO positions and the finite holder
path; it does not assert that distance to the token decreases under contention.

For isolated executions from quiescent initialization with only application client u,
at completed entry each message kind has exactly dist(u,initialOwner) sends: total
2*dist. Arbitrary legal delays and interleavings are allowed. Retained-token reentry
adds no traffic. This counts sends, not time or local steps. A chain can require
2*(n-1) messages; O(log n) is not a universal bound and no such bound is claimed under
arbitrary contention.

Node/link failures with token loss, token regeneration, dynamic topology/membership,
Byzantine behavior and real-time guarantees are outside scope. Python, JSON/SHA-256
and external SimLab input-to-byte binding remain open obligations. Scientific priority
has not been assessed.

## Historical verification records

[Knowledge base](README.md) · [Release v0.5.18](../docs/release-v0.5.18.en.md)

Measured: 120 direct imports, 162 Lean files under Verification/,
12,922 project declarations, 3547 strict build jobs and 65 public live tests
without failures or skips (253.994s). Both complete audits allow only
`propext`, `Classical.choice`, and `Quot.sound`. The strict registry hook also passed.
The two nested specification files are auxiliary meta-audit tooling.
[Hashes and measured commands](../tools/validation_snapshot.json).

## Shor LCM/GCD recovery scope

[Theorems and assumptions](03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md).

listLCM is executable structural recursion over a finite list of natural-number
candidates. Neither the unknown order nor spectral numerators are inputs. The empty
LCM is one; append and membership invariance cover incremental use, reordering and
duplicates. No time or bit-complexity bound is asserted.

For r>0 and a nonempty list with every q dividing r, L=listLCM(qs) divides r and
L=r iff foldr (fun q acc => gcd(r/q,acc)) 0 qs = 1. Nonemptiness is necessary for
this unanchored GCD criterion. For spectral denominators q=r/gcd(s,r), the exact
identity is L=r/gcd(r,foldr gcd 0 ss); thus L=r iff the anchored GCD is one.
This version includes empty ss: empty input recovers only order one. At r=6,
ss=[3,2] gives denominators [2,3] and recovers six without any individual q=r.

The bridge reuses module 119's canonical reduced denominators and the existing
Shor Parameters (N>=2, coprime a,N, positive actual order and padded target register).
Given Q=2^n>=N² and each observed y<Q satisfying Nearest to its latent s/r with s<r,
the correct denominator occurs among the corresponding continued-fraction candidates.
This does not identify the latent label or select its denominator from the observable list.

The modular check proves r divides L. With separately established L divides r,
it gives equality. A certified divisor means mathematical provenance, not merely
a successful modular check. No automatic candidate-selection algorithm is supplied.

A kernel-checked counterexample has N=31,a=2,order=5,y=410,Q=1024. Candidate
denominators [1,2,5] have LCM 10, which passes the modular check but is not the order.
Regressions verify 31²<=1024 and |410/1024-2/5|<=1/(2*1024), so this failure persists
at adequate QPE resolution. Taking the LCM of all candidates is unjustified.

No i.i.d. measurement law, probability of a coprime sample family, number of runs,
factorization via gcd(a^(r/2)±1,N), physical implementation or gate synthesis is proved.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
The algebra reuses pinned Mathlib Nat.div_lcm_eq_div_gcd; scientific priority has
not been assessed. This is conditional multi-sample recovery, not a full Shor algorithm.

## Shor continued-fraction scope

[Theorems and assumptions](03_quantum_physics_and_optics/QuantumShorContinuedFractions.md).

The algorithm computes finite partial quotients and convergents of the exact rational
y/Q by Euclidean descent, terminating at an integer. Its inputs y,Q,N do not contain
the unknown spectral numerator s or period r. The candidate list filters denominators
strictly below N. Membership in the unfiltered list is equivalent to being a Mathlib
Real.convergent, including its repeated terminal values.

For N≥2, a coprime to N, r=orderOf(a : ZMod N), 0≤s<r and 0≤y<Q, the existing Shor
model proves 0<r<N. With Q=2^n≥N², the modular QPE Nearest condition implies ordinary
|y/Q-s/r|≤1/(2Q). The proof handles s=0 and rules out wrap-around at this resolution.
Since q=r/gcd(s,r)≤r<N, the error is strictly below 1/(2q²). Pinned Mathlib's strict
Legendre theorem supplies the convergent, and the finite-list bridge proves its
presence among the executable candidates.

The correct reduced denominator q divides r. Other list entries are not asserted
to divide r. If gcd(s,r)=1, q=r and r belongs to the modularly checked list. The
modular check a^q mod N = 1 mod N proves r divides q; proper multiples can pass.
If q divides r is separately established, mutual divisibility gives equality.
For s=0 the reduced denominator is one, recovering the order only when r=1.

The number of Euclidean stages is at most 2*Nat.log 2 Q+1 for Q>0. This counts partial
quotients, not every list operation, bit operation, modular exponentiation or total
runtime. No O(log N) claim is made without additionally bounding Q in terms of N.

The existing actual-input QPE mixture gives a contribution bound 4/(r*pi²) for a
single component's nearest sample, combined here with candidate membership. This
is distinct from the conditional component bound 4/pi². Guaranteed single-run
success, independent repeated measurements, LCM recovery, classical factorization,
long-integer bit complexity, physical noise and gate synthesis are outside scope.
Python, JSON/SHA-256 and external SimLab input-to-byte binding remain open obligations.
No scientific-priority claim or full factoring algorithm is asserted.

## Suzuki–Kasami scope

[Model and theorem details](09_distributed_systems/DistributedSuzukiKasamiMutex.md).

The fixed-membership, crash-free model uses Fin n, unbounded natural request
sequences and serialized client invocations. Reachability implies exactly one token,
counting both holders and the channel, mutual exclusion, and a duplicate-free queue.
The payload is a global semantic coordinate exposed only to the holder; it is
unchanged in transit. No runtime shared memory is assumed.

ReliableDelivery requires eventual delivery of actual REQUEST and token messages.
WeakFairness schedules continuously enabled send and enter actions. FiniteCS requires
every critical-section visit eventually to leave. Under these contracts, every
Requesting observation eventually reaches InCS, including runs with later requests.
Safety does not require fairness. No numerical waiting-time bound is proved.

The model separates immediate idle-holder handoff into queue reservation and a
separately scheduled send. New local requests cannot bypass an already reserved
handoff. This serialization is explicit; no mechanized refinement to the original
program is claimed. FIFO holds after queue insertion, not as global request order.
REQUEST fanout is atomically enqueued; individual deliveries are separate, unordered
and exact-once. Token transport uses one in-flight slot, without loss or duplication.

RN and LN are nondecreasing, with LN[j] ≤ RN_j[j] ≤ LN[j]+1 at the sender. The stronger
claim LN[j] ≤ RN_holder[j] is false: a reachable three-node trace leaves node 2 holding
a token with LN[1]=1 and RN_2[1]=0 before a delayed REQUEST arrives. Receiving the token
does not silently synchronize RN. Retained-token reentry does not increment the
network request number and need not join the queue. LN is not a count of every CS visit.

Crashes, lost-token recovery, dynamic membership, partitions, Byzantine behavior,
finite counter overflow, real-time bounds and network/application implementations
are outside scope. Python, JSON/SHA-256 and binding external SimLab inputs to bytes
remain open obligations. No scientific-priority claim is made.

## Spectral order-finding scope

[QuantumShorOrderFindingCore](03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md)
constructs a permutation of every residue modulo N for a coprime base, fixes padded
register states, and proves inverse and unitary operator identities. Its orbit
spectrum is orthonormal and decomposes |1⟩ without requiring knowledge of the order
for input preparation. The actual QPE joint output yields a normalized marginal
mixture with weights 1/r. The nearest-sample 4/π² bound applies to each component;
the guaranteed contribution of one component to the mixture is 4/(rπ²).
Order recovery, continued fractions, repeated-run LCM recovery, factorization,
gate synthesis, complexity and physical noise are outside scope. Python,
JSON/SHA-256 and binding external SimLab inputs to bytes remain external obligations.

## General QPE scope

[QuantumPhaseEstimationGeneral](03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md)
derives the output for an arbitrary finite target and n-bit control register from
controlled powers and the inverse Fourier transform. Fourier unitarity, exact
dyadic recovery, probability normalization and the nearest-sample lower bound
4/π² hold in the exact complex model. The measured-output claims use a supplied
normalized eigenvector of a unitary operator. Both midpoint choices, modular
wraparound, negative phases, the singular geometric-sum branch and n=0 are covered.
The n=2 bridge identifies the complete old operational output.
Eigenstate preparation, gate synthesis and cost, physical noise, decoherence and
full Shor are not proved. Python, JSON/SHA-256 and SimLab byte binding remain external.

## Operational snapshot scope

DistributedChandyLamportSnapshot derives saved-cut consistency and exact completed-channel contents from two-process FIFO transitions. Open-channel recording has separate received-so-far semantics. There is one snapshot instance; no failures, arbitrary n-node topology, fairness, eventual completion or completion detector are verified.

All 163 Lean sources, including the root file, match private snapshot `5e714619c1455a47bc58d0f87d8cfe8a94db0c7b` byte-for-byte.

## Exact QPE scope

QuantumPhaseEstimation has two control qubits and a one-qubit complex target. Controlled U/U² derive phase kickback from an exact eigenstate equation; the inverse Fourier transform returns the correct basis state. The four supported phases are 0, 1/4, 1/2 and 3/4. A normalized eigenstate and norm-preserving complex-linear operator are supplied. Physical measurement, preparation, gate noise and approximate QPE are not certified.

## Numerical scope

- NumericBinaryGrid supplies the exact binary64 magnitude decoder and parity lemmas.
- NumericRoundingCertificates checks rational interval and exact-midpoint witnesses,
  with signed zero, subnormals and overflow. The mathematical checker is not a
  verification of Python or CPU instructions.
- NumericRealRounding transports rational endpoint certificates to enclosed real values.
- NumericSQLIntervalBounds encloses `sqrt(hbar/(mass*frequency))` under explicit
  positive input intervals and containment hypotheses. Physical calibration is external;
  the separate gap expression is handled by NumericSQLGapBounds.
- NumericSQLGapBounds derives affine gap bounds, exact zero iff balance for positive
  parameters, canonical +0 and composition with real rounding. Rationalization,
  exact cell-boundary comparison and the new SimLab search are not formalized.
- NumericCertificateDigestBridge composes explicit pure digest/parser parameters
  with the mathematical checker. Expected digest, parser, grid and SQL inputs are
  external context. SHA-256, JSON/RFC 8259, Python equivalence, byte binding of those
  inputs and source authenticity are not proved. Digest equality is not byte equality.

Historical indeterminate intervals remain indeterminate. Later exact-midpoint or
exact-zero evidence is separate. No simulation runtime or full simulation archive
is distributed. The curated rounding provenance JSON is external metadata; its
source simulation paths are not included in this package.

The earlier placement certificate retains its exact 256 rational records, boundary
and pairwise-disjointness guarantees. The deterministic converter is checked
externally; its JSON parser and hashing are not Lean-verified.

Scalar MuSig2 does not establish cryptographic security; the forking module proves
an elementary finite-matrix bound, not a general ROM reduction. Visibility does
not prove quantum decoherence. The documented optomechanical approximation regime
is not derived in Lean. Historical hundred-module aggregation preserves these limits.

## Multiple-target Grover scope

QuantumGroverMultipleTargets proves all-subset N=4 real dynamics, all-natural-iteration
success weights, arbitrary-state norm preservation, singleton compatibility and
an invariant orthonormal plane for nonempty proper target sets. It also proves
both rank-one reflection counterexamples. No arbitrary-N search, query-complexity,
trigonometric-angle formula, separate topological-closedness theorem, physical
measurement, noise or hardware certification is claimed.

## Raft commit application scope

DistributedRaftCommitApplication and its two support modules derive actual
commit-event provenance for server and RPC prefixes, retained committed prefixes,
and ordered deterministic local application. A reachable 45-transition example
shows why an old-term majority alone is insufficient. Cross-node fold agreement
requires equality of full entries, including commands. This extension does not
prove a new global State Machine Safety theorem, liveness, client exactly-once
behavior, timeout handling, crash/recovery or fsync/WAL.

## Operational 2PC timeout scope

Two independent participants and a stopped coordinator distinguish safe pre-vote
abort from unsafe forced decisions on identical prepared local views. Under both
prepared and coordinator stopped, no queued decision is equivalent to no finite
continuation reaching a terminal participant. Other packets may remain in flight.
Decision delivery is possible, not guaranteed. Fairness, recovery, peer termination,
3PC and disk durability are not claimed.

## Two-participant 3PC scope

The fixed two-participant model uses bounded request/response queues and crash-stop
failures. Reachable agreement includes stopped terminal decisions. Completion paths
and eventual completion under weak fairness are separate theorems. Exact surviving
membership, unique coordinator appointment and atomic epoch fencing are external
contracts. No arbitrary-n protocol, dynamic joining, network partition tolerance,
crash recovery or runtime implementation is certified.

## Static-epoch CMH scope

The graph is fixed within each detector execution. Probe provenance and detection
soundness are inductive invariants; eventual detection after initiation requires
the explicit payload-delivery contract. Graph replacement requires an external
isolated reset. The dynamic counterexample refutes a naive send-time-only check,
not the original CMH protocol. See the [release scope](../docs/release-v0.5.10.en.md).

## Arbitrary-phase Grover scope

The one-target C^4 model proves complex linearity, explicit adjoints and inverse
identities, Hermitian norm preservation and a complex plane invariant under every
pair of real phases. Equal phases from uniform have
P(phi)=1-3*(1+cos(phi))^2/16 and P=1 iff cos(phi)=-1. At pi the raw step is the
negative of the canonical step; measurement weights agree. This is not a general
Hoyer phase-matching theorem or Long iteration schedule. Hardware, noise and
Python/JSON/SHA-256/SimLab byte binding remain outside the result.

## Simon scope

The complex H/XOR/H circuit yields exact uniform probability 2/(2^n) on s-perp under SimonPromise with nonzero s. Recovery requires orthogonal rows spanning rank n-1 over F2. No sample-count bound or implemented Gaussian solver is certified. See the [Simon card](03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md).
