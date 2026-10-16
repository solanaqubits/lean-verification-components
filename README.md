# Mathematical Verification Components in Lean 4

[![Lean verification](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml)

Machine-checked mathematical components built with Lean 4 and Mathlib: algebraic
invariants, finite computations, conditional protocol properties, and explicit
scalar models. Browse the proofs by subject, inspect their assumptions, and reuse
the components in larger formal developments.

**[Knowledge base](knowledge/README.md)** · **[Results and value](knowledge/SUMMARY.en.md)** ·
[Technical reference](docs/verification-details.en.md)

## Proof sections

| Section | Focus |
|---|---|
| [Collatz and discrete dynamics](knowledge/collatz/README.md) | Finite orbits, congruences, and coefficient bounds |
| [Explicit logarithmic bounds](knowledge/riemann/README.md) | Prescribed analytic functions |
| [Almost-complex algebra](knowledge/hopf/README.md) | Algebraic identities and cross products |
| [Polynomial functionals](knowledge/lamzouri/README.md) | Integrals, quotients, and exact minima |
| [Coordinate geometry](knowledge/finsler/README.md) | Forms, polarization, and diagonal transformations |
| [Proof certificates and DAGs](knowledge/proof-graphs/README.md) | Conditional checker soundness |
| [Cryptographic algebra](knowledge/cryptography/README.md) | Diffusion, traces, folding, and commitment identities |
| [Quantum algebra, photonics, and mechanics](knowledge/quantum-physics/README.md) | Matrices, symmetries, and prescribed energy models |
| [Finance and mechanisms](knowledge/finance/README.md) | Balances, reserves, fees, and portfolio risk |
| [Distributed consensus](knowledge/distributed/README.md) | Quorums, reachable Log Matching, and operational Leader Completeness |
| [Registry and audit](knowledge/verification/README.md) | Selected suites and axiom dependencies |

## Verified snapshot

**189 direct imports**, **232 Lean sources including Verification.lean**
(229 top-level modules and 2 auxiliary specs under Verification/).
All 232 sources match private snapshot `330ea2350bae059cac7b546fb9d8748ccf4ae0ef`.
This is a **gamma-level release** (formerly Z) under the [version policy](VERSIONING.md).
[Current scoped evidence](docs/release-v0.5.87.en.md) is separate from the
[last full-validation baseline](knowledge/VERIFICATION.en.md), public commit
`b3410720b9af49c2fb70d15d65d3d012091cbf0b` (v0.5.73).

## Release v0.5.87

[Qutrit two-of-three secret sharing](knowledge/03_quantum_information/QuantumQutritTwoOfThreeSecretSharingContract.md)
proves an explicit modulo-three isometric code, perfect single-share privacy
and CPTP recovery from every pair. The same recoveries preserve arbitrary
external references, while no single share permits exact recovery.

## Release v0.5.86

[Subsystem erasure correctability](knowledge/03_quantum_information/QuantumErasureCorrectabilityContract.md)
constructs the partial-trace Kraus channel and identifies its complement with
the lost subsystem. Exact recovery is equivalent to independence of the lost
part, with reference preservation. Explicit fixed-factor and entangled-auxiliary
codes are verified alongside the repetition-code obstruction.

## Release v0.5.85

[Reference-preserving recovery](knowledge/03_quantum_information/QuantumReferencePreservingRecoveryContract.md)
extends exact recovery to every finite reference with the same recovery channel,
derives reference/environment factorization and proves the normalized maximally
entangled-state criterion by matrix-block extraction. Bell coherence regressions
include the impossibility of full-qubit dephasing recovery.

## Release v0.5.84

[Knill-Laflamme recovery necessity](knowledge/03_quantum_information/QuantumKnillLaflammeRecoveryNecessity.md)
proves scalar structure of composite Kraus operators and derives the general
Knill-Laflamme conditions from arbitrary exact CPTP recovery. Together with the
previous sufficiency and environment criteria, it establishes the finite-dimensional
equivalence and rules out exact recovery of full-qubit dephasing.

## Release v0.5.83

[General Knill-Laflamme recovery](knowledge/03_quantum_information/QuantumKnillLaflammeGeneralRecoveryTheorem.md)
derives coefficient Hermiticity and constructs the spectral certificate using
Mathlib. It proves exact CPTP recovery of every complex logical matrix from
general Knill-Laflamme conditions, without a supplied diagonalization certificate.
This is sufficiency; necessity and an executable numerical decoder remain outside scope.

## Release v0.5.82

[Recovery with certified unitary diagonalization](knowledge/03_quantum_information/QuantumUnitaryKrausDiagonalizationRecoveryContract.md)
uses complex Kraus mixing with the exact transpose bridge W=U^T. It derives
nonnegative normalized spectral weights and preserves the physical channel.
The explicit CPTP recovery from module 183 then recovers every complex logical
matrix. A unitary diagonalization certificate is supplied as input; existence
of such a certificate and the general recovery equivalence are outside scope.

## Release v0.5.81

[Orthogonal error recovery](knowledge/03_quantum_information/QuantumOrthogonalErrorRecoveryContract.md)
constructs a recovery CPTP channel for diagonal Knill-Laflamme data. Normalized
error adjoints are completed with reset operators on the unused output space.
The channel recovers every complex logical matrix, including coherences, and
handles zero error weights. General non-diagonal coefficient reduction and the
full recovery theorem remain open.

## Release v0.5.80

[Knill-Laflamme environment criterion](knowledge/03_quantum_information/QuantumKnillLaflammeEnvironmentCriterion.md)
proves the equivalence between compressed Kraus-product scalar identities and
constancy of the complementary channel on an encoded space, for all complex
logical matrices. Isometric encoding with positive logical dimension yields a
normalized positive environment state. Complex regressions check the ordinary
transpose convention. Recovery CPTP maps and full error correction remain open.

## Release v0.5.79

[Complementary quantum channel](knowledge/03_quantum_information/QuantumComplementaryChannelContract.md)
constructs the environment output of a supplied Kraus/Stinespring representation,
proves its CPTP properties and both partial-trace identities, and relates a given
isometric environment change to the unchanged main channel and conjugated
complement. Examples cover unitaries, reset, dephasing and zero padding.
The joint matrix need not be pure; information absent from both marginals can
remain in correlations. General dilation uniqueness, minimality, quantum
capacity and general recovery maps are outside scope.

## Release v0.5.78

[Utilization feedback stability](knowledge/01_defi/DeFiLendingUtilizationFeedbackStability.md)
extends the existing rational kinked rate to a real projected feedback law,
with an exact rational bridge. It proves invariant unit-interval bounds,
contraction conditions across the kink, finite-time disturbance bounds and
zero-noise convergence to a specified equilibrium. Rational trajectories and
integer-rate rounding have explicit correspondence theorems. A large-step
example cycles between zero and one while remaining bounded by projection.
The response law is a prescribed model, not a proof of market stability,
liquidity or economic solvency.

## Release v0.5.77

[Tendermint evidence accountability](knowledge/05_distributed/DistributedTendermintAccountableSafety.md)
constructs explicit accusations and a deduplicated offender set for conflicting
votes, uncertified precommits and unjustified lock switches. Conflicting commits
force strictly more than one third of the total weight into that set.
No-framing is proved for reachable core histories under a sufficient view of an
externally authenticated complete reference transcript. The checker verifies
relative prevote coverage; it cannot establish the reference's own completeness.
Missing evidence is rejected. Concrete signatures, slashing, evidence deadlines,
dynamic membership and deployed-protocol equivalence remain outside this result.

## Release v0.5.76

[Conditional range extraction](knowledge/04_cryptography/CryptoBulletproofsRangeWitnessExtraction.md)
composes actual IPA tree extraction with polynomial/grid interpolation from
certified openings of A,S,V. It returns a range witness opening the original V
or a concrete nontrivial zero relation among the original generators, including
blinding generators. Vector agreement is derived rather than assumed.
Obtaining the supplied openings, rewinding, runtime bounds and Fiat–Shamir/ROM
security remain outside this result. This release also names the existing scope
ranks alpha/beta/gamma and documents delta iterations in parallel streams.

## Release v0.5.75

[Stinespring dilation](knowledge/03_quantum_information/QuantumStinespringDilationContract.md)
constructs an isometry from supplied rectangular Kraus operators, recovers the
channel through the existing partial trace and identifies its dual map.
Joint density matrices and their recoverability are proved. Exact regressions
cover unequal dimensions, dephasing and redundant zero Kraus blocks.
Minimality, uniqueness and general unitary extension are outside this module.

## Release v0.5.74

[Finite-grid range interpolation](knowledge/04_cryptography/CryptoBulletproofsRangeInterpolation.md)
turns pointwise equalities on an injective Y/Z grid for fixed witnesses into a
formal polynomial identity, bit constraints and a natural range bound under
explicit no-wrap hypotheses. This is not a full transcript witness extractor.
The release includes targeted regressions, a checked grid interface and the
approved X/Y/Z verification policy.

## Release v0.5.73

[CPTP channel contract](docs/release-v0.5.73.en.md) proves quantum trace-distance
contraction, dual effect pullback and trace preservation for Kraus channels, with
an additional theorem for the existing abstract CPTP interface. Identity and
unitary channels preserve distance; basis-state reset and dephasing demonstrate
loss of distinguishability. Stinespring dilation, full equivalence of channel
representations and relative-entropy DPI are outside this module.
The updated verification workflow retains incremental caches and runs a single
full final release gate.

## Earlier additions in v0.5.72

[Bad debt accounting](docs/release-v0.5.72.en.md) allocates authorized writeoff
losses first to reserves and then to supplier claims, preserving the accounting
balance with fixed cash. It proves indexed debt consistency, supplier-share price
decline, exact integer loss allocation and explicit rounding bounds. The signed
debt-ledger/index gap is separated from reconciliation dust. Actual uncollectibility,
withdrawal liquidity, economic solvency and specific protocol mechanisms remain
outside scope. Full Bulletproofs range extraction, Tendermint accountability,
Python, JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.71

[Liquidation accounting](docs/release-v0.5.71.en.md) connects liquidation admission
to indexed debt repayment, splits the collateral bonus between liquidator and a
separate treasury, and conserves both asset balances. The checked integer policy
has explicit rounding bounds and distinguishes the debt-ledger/index gap from
reconciliation dust. Health-factor improvement is conditional. Oracle accuracy,
market execution, debt recoverability, economic solvency and deployed-contract
correspondence remain outside scope. Full Bulletproofs range extraction,
Tendermint accountability, Python, JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.70

[Trace distance and measurement contraction](docs/release-v0.5.70.en.md) proves
metric laws on density matrices, an attained maximum over effects, the equal-prior
Helstrom identity and TV contraction under finite POVM measurements and classical
postprocessing. A binary spectral POVM attains the maximum over all finite outcome
counts. General quantum-channel contraction, numerical spectral certification and
physical implementation remain outside scope. Full Bulletproofs range extraction,
Tendermint accountability, Python, JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.69

[Holevo–Helstrom state discrimination](docs/release-v0.5.69.en.md) proves the optimal
binary state discrimination bound without commutation assumptions, attainment by a
spectral projector, freedom of selection at zero eigenvalues, Bayes decision rule
optimality and classical postprocessing contraction of optimal guessing probability.
Exact noncommuting qubit regressions give trace norm 1/sqrt(2). Certified numerical
spectral algorithms, sampling, physical implementation and general quantum DPI remain
outside this model. Full Bulletproofs range extraction, Tendermint accountability,
Python, JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.68

[Recursive IPA tree extraction](docs/release-v0.5.68.en.md) proves deterministic
extraction from a supplied complete accepting four-branch tree. It recovers full
witness vectors or explicit nonzero coefficients of a zero combination of the
root generators. Relation lifting preserves evaluation and nontriviality; the
checker validates every branch against the actual verifier's derived contexts.
Honest trees recover their exact vectors at every depth. The tree has n^2 leaves,
separate from the 2k group elements of a single IPA transcript. Probabilistic tree
construction, full range extraction and bitness, computational binding, HVZK,
Fiat-Shamir/ROM, Tendermint accountability, Python, JSON/SHA-256 and SimLab
obligations remain open.

## Earlier additions in v0.5.67

[Local Bulletproofs witness extraction](docs/release-v0.5.67.en.md) proves a
one-step IPA extraction dichotomy from four accepting folded-witness responses
with a common prefix and distinct nonzero challenge squares: an original witness
or explicit nonzero coefficients of a zero generator combination. Generator
independence is not assumed. The checked interface rejects invalid inputs.
Three-point Vandermonde interpolation recovers the range-reduction polynomial's
coefficients; it does not establish bitness. Full recursive extraction,
probabilistic transcript-tree construction, computational binding, HVZK and
Fiat-Shamir/ROM remain open, as do Tendermint accountability and external Python,
JSON/SHA-256 and SimLab obligations.

## Earlier additions in v0.5.66

[Debt-index accrual and rounding reconciliation](docs/release-v0.5.66.en.md)
proves interval composition, the strict subdivision effect and guarded accrual,
borrowing and repayment accounting. Natural accrual preserves balance by assigning
the interest residual to suppliers. Index-derived reconciliation dust is at most
n-1 and is explicitly separated from independent ledger/index drift. Local error
bounds do not imply a uniform global bound over arbitrary update chains. Debt
recoverability, default freedom, withdrawal liquidity and deployed-contract
refinement remain outside scope. Tendermint accountability, Bulletproofs security
and external Python, JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.65

[Kinked utilization rates and rounding](docs/release-v0.5.65.en.md) proves exact
utilization admission, continuity and monotonicity of the borrow curve, convexity
under ordered slopes, supply-rate monotonicity and conditional spread. Executable
natural arithmetic has explicit rounding order and end-to-end error bounds against
the rational lift of the same encoded parameters. The checked quote rejects U>1
even when rounding would hide the excess. Rate order is an instantaneous property;
pool solvency, defaults, withdrawable liquidity and accrual over time are outside
scope. Deployed-contract refinement and external Tendermint, Bulletproofs, Python,
JSON/SHA-256 and SimLab obligations remain open.

## Earlier additions in v0.5.64

[Classical POVM data processing](docs/release-v0.5.64.en.md) proves stochastic
postprocessing of finite POVMs, support preservation and classical KL contraction
under absolute continuity. Bistochastic channels cannot decrease Shannon entropy;
binary symmetric noise strictly increases it for nonuniform inputs when
0<epsilon<1/2. Deterministic merging provides the entropy-decrease counterexample
for general stochastic channels. Singular infinite KL and general quantum Umegaki
DPI remain outside scope. The exact real analysis is noncomputable; no numerical
logarithm implementation is certified. External correspondence, Tendermint
accountability and Bulletproofs security obligations remain open.

## Earlier additions in v0.5.63

[Weighted Tendermint core safety](docs/release-v0.5.63.en.md) proves quorum
intersection, same-round uniqueness and cross-round commit safety from reachable
states. Strict >2/3 quorums retain safety at exactly one-third Byzantine weight;
a concrete reachable conflict is exhibited above that boundary. Executable guards
check actual certificates and unique signers. This is a fixed-height safety
abstraction, with full implementation refinement, liveness, signatures and
attributable slashing evidence outside scope. External correspondence and
Bulletproofs security obligations remain open.

## Earlier additions in v0.5.62

[Lending liquidation health factor](docs/release-v0.5.62.en.md) proves
exact liquidation accounting, conditional health improvement, residual debt
coverage and directed integer rounding. Zero debt has no numeric health factor.
Executable guards distinguish liquidation admission from preserving coverage;
counterexamples show why admissibility alone does not ensure either health
improvement or residual coverage. Oracle truth, market execution, pool-wide
solvency and external correspondence obligations remain outside these guarantees.

## Earlier additions in v0.5.61

[Bulletproofs multi-range aggregation](docs/release-v0.5.61.en.md) proves
block-weighted polynomial reduction, formal coefficient recovery and honest
composition with the recursive IPA. The single-block verifier equals module 159.
The IPA payload contains exactly 2(a+b) group elements and two scalars;
the proof body and envelope with public commitments are counted separately.
Witness extraction, binding, HVZK, Fiat-Shamir/ROM and external correspondence
obligations remain open.

## Earlier additions in v0.5.60

[POVM information entropy](docs/release-v0.5.60.en.md) proves the general
Maassen-Uffink lower bound for finite POVMs and density matrices through
Hadamard interpolation, Naimark phase contractions and spectral mixtures.
The overlap uses the Euclidean operator norm. Exact Pauli examples attain one
bit; noncommuting qutrit measurements can share a zero-entropy eigenstate.
Finite sampling, quantum side information and numerical logarithm certificates
are outside this exact analytic model. Existing cryptographic and external
correspondence obligations remain open.

## Earlier additions in v0.5.59

[Constant product with virtual reserves](docs/release-v0.5.59.en.md) proves exact
real-reserve solvency, the retained-fee product identity, fixed-fee price impact
and executable natural swaps with directed rounding. Successful finite chains
with variable valid fees have nondecreasing product. Fees remain in trading
reserves; external-price value preservation and MEV/arbitrage security are not
asserted. Existing Bulletproofs security and implementation obligations remain open.

## Earlier additions in v0.5.58

[Bulletproofs batch verification](docs/release-v0.5.58.en.md) proves perfect
completeness, equivalence to one expanded MSM, paired permutation invariance and
an error bound of at most 1/q relative to individual verification. The probability
bound applies to a fixed batch with fresh independent uniform field weights.
Scalar checks reject invalid challenges deterministically. Original IPA transcripts
are retained. Knowledge extraction, computational binding, HVZK, Fiat-Shamir/ROM
and implementation of secure randomness remain open.

## Earlier additions in v0.5.57

[Bulletproofs algebraic range reduction](docs/release-v0.5.57.en.md) proves
formal polynomial equivalence with bit constraints, natural range recovery under
explicit bounds, the corrected public IPA target and honest composite completeness.
Knowledge extraction, computational binding, HVZK and Fiat-Shamir/ROM remain open.
An identity of formal polynomials is distinguished from equality at a fixed challenge.

## Earlier additions in v0.5.56

[Bulletproofs inner product algebra](docs/release-v0.5.56.en.md) proves the
halving invariant, recursive completeness, equivalence of expanded verification
and an exact payload of 2k group elements plus two scalars for dimension 2^k.
Knowledge extraction, range reduction, HVZK and Fiat-Shamir/ROM remain outside scope.
Logarithmic proof size does not imply logarithmic verifier work.

## Earlier additions in v0.5.55

[Stable Marzullo event merge sorting](docs/release-v0.5.55.en.md) proves
stable ordering, exact insertion-sort equivalence and the comparator-call bound
N * ceil(log2 N). The merge-based backend preserves peak and safe-hull semantics.
Rational bit complexity and the complete consensus runtime remain outside scope.

## Earlier additions in v0.5.54

[Linear interactive Pedersen range proofs](docs/release-v0.5.54.en.md) prove
natural bit ranges, fixed-opening completeness, two-transcript witness extraction
and equality of full joint special HVZK distributions. The simulator includes
correlated bit commitments with the fixed aggregate. Computational binding,
Fiat-Shamir/ROM and malicious-verifier security remain outside scope.

## Earlier additions in v0.5.53

[Discrete concentrated-liquidity reference arithmetic](docs/release-v0.5.53.en.md)
proves directed token rounding, finite-grid swap budget bounds, and nonnegative
position-derived liquidity through tick crossings. This executable exhaustive
reference model does not establish equivalence to Solidity SwapMath/TickMath,
efficient execution on wide price grids, or a complete pool lifecycle.

## Earlier additions in v0.5.52

[Executable Marzullo interval consensus](docs/release-v0.5.52.en.md) proves rational
event-sweep overlap counts, exact maximal peak intervals and deterministic
selection by length and left endpoint. The computed safe hull equals the existing
real-valued thresholdHull. A selected peak need not contain true time; its
containment in the safe hull is non-strict. Full NTP and physical clock control
remain outside scope.

## Earlier additions in v0.5.51

[Informationally complete POVMs](docs/release-v0.5.51.en.md) connect measurement
injectivity to a positive definite, invertible frame operator and exact quantum
state reconstruction through its canonical dual. The module proves the d²
outcome bound, constructs a tetrahedral qubit SIC-POVM and exhibits states that
basis measurements cannot distinguish. Finite-sample statistics, numerical
conditioning and SIC existence in arbitrary dimensions remain outside scope.

## Earlier additions in v0.5.50

[Mixed-state no-broadcasting](docs/release-v0.5.50.en.md) proves that a pair of
finite-dimensional density matrices admits one exact CPTP broadcasting channel
if and only if the states commute. Correlated outputs and degenerate spectra are
included. Necessity uses a constructed symmetric logarithmic derivative and an
operator sum of squares. Infinite dimensions, approximate broadcasting and
physical implementations remain outside scope.

## Earlier additions in v0.5.49

[FROST threshold Schnorr signatures](docs/release-v0.5.49.en.md)
proves partial and aggregate verification for any signing set at or above the
threshold, canonical session contexts and independently recomputed alternative
coalitions. A single response error is rejected; opposite errors can cancel in
the aggregate. ROM security, nonce-use enforcement, DKG/VSS and serialization
remain outside scope.

## Earlier additions in v0.5.48

[Raft joint-consensus reconfiguration](docs/release-v0.5.48.en.md)
proves reachable Election Safety, Log Matching and Leader Completeness for one
old-to-joint-to-new transition, with historical commit-index soundness and local
configuration rollback. Arbitrarily many reconfigurations, snapshots, Byzantine
faults, crash/recovery and liveness remain outside scope.

## Earlier additions in v0.5.47

[Finite-field Shamir sharing](docs/release-v0.5.47.en.md)
proves t-of-n interpolation over ZMod q, joint PMF secrecy below threshold,
group-point reconstruction and finite weighted linearity. The explicit secret-shift
equivalence preserves every observed share. VSS, active share forgery, DKG,
refresh, threshold signatures and efficient DLOG decoding remain outside scope.

## Earlier additions in v0.5.46

[Vector Pedersen commitments](docs/release-v0.5.46.en.md)
proves vector linearity and weighted homomorphism, perfect hiding through a uniform
PMF, exact collision relations and conditional logarithm extraction. Equal bases
and known relations yield explicit alternate openings. Generators are an indexed
family, not a linearly independent basis. Computational binding, parameter
generation, coordinate opening proofs and ZKP protocols remain outside scope.

## Earlier additions in v0.5.45

[Group ElGamal weighted homomorphism](docs/release-v0.5.45.en.md)
proves group and exponential decryption correctness, scalar uniqueness,
finite weighted homomorphism, algebraic rerandomization and nontrivial malleability.
Decryption returns a group point; scalar uniqueness does not provide an efficient
discrete-logarithm decoder. IND-CPA/IND-CCA proofs, DDH reductions, concrete curves
and serialization remain outside scope.

## Earlier additions in v0.5.44

[BLS aggregation in bilinear groups](docs/release-v0.5.44.en.md)
proves individual and aggregate completeness, common-message aggregation and
composition of valid partial signatures. Pairing injectivity is derived from
cyclicity and nondegeneracy. A concrete scalar model witnesses the assumptions.
Rogue-key and error-cancellation counterexamples delimit what verification
establishes. Concrete curves, hash-to-curve, serialization, PoP and computational
security reductions remain outside scope.

## Earlier additions in v0.5.43

[Signed Byzantine broadcast](docs/release-v0.5.43.en.md)
proves Agreement and CommanderValidity in f + 1 synchronous rounds with ideal
signatures, n >= f + 2 nodes and at most f static Byzantine faults. Signature
origins and dissemination follow from execution transitions. Final honest
lieutenant views coincide. A delayed-chain counterexample establishes why the
round-length filter matters. Computational signature security, asynchrony and
dynamic faults remain outside scope.

## Earlier additions in v0.5.42

[Three-generals oral Byzantine broadcast](docs/release-v0.5.42.en.md)
proves that Agreement and CommanderValidity cannot both hold for three nodes
and at most one static Byzantine fault in synchronous oral messages. Honest
local-state equality is derived inductively in three constructed executions
for every fixed finite horizon T. General n <= 3f, signed messages, randomized
protocols and termination without a common finite bound are outside scope.

## Earlier additions in v0.5.41

[Finite-group Schnorr aggregation](docs/release-v0.5.41.en.md)
proves partial and aggregate algebraic completeness for a static key vector in
a cyclic prime-order group. Accepted partial responses with a common challenge
assemble into an accepted aggregate. A naive rogue-key witness exhibits key
cancellation and a passing signature. A common ring identity connects the real
scalar model and modular specialization. AGM/ROM security, hashed-coefficient
rogue-key resistance, interactive MuSig2/BIP327 and serialization are outside scope.

## Earlier additions in v0.5.40

[Coordinated attack impossibility](docs/release-v0.5.40.en.md)
derives delivery-removal indistinguishability from deterministic local transitions.
For every fixed finite horizon, Agreement and ValidityZero force retreat on every
input and delivery schedule, contradicting ReliableSuccess. The model permits
synchronous rounds and arbitrary message losses, with no sender-visible delivery
feedback. Regressions cover zero rounds, an always-retreat protocol, lost
acknowledgements and commuting delivery removals. Unbounded stopping times,
randomized agreement, quantum channels and Byzantine behavior are outside scope.

## Earlier additions in v0.5.39

[Exact unitary no-cloning](docs/release-v0.5.39.en.md)
derives overlap constraints from unitary evolution and tensor factorization.
Pure states cloned by one unitary with a fixed blank must be orthogonal or have
identical density matrices. Global phases are handled explicitly. CNOT copies
the computational basis and entangles a superposition. Universal cloning in
dimension at least two and joint cloning of the four BB84 states are impossible.
General CPTP cloning, mixed-state no-broadcasting and physical QKD security are
outside scope.

## Earlier additions in v0.5.38

[Finite POVMs and Naimark dilation](docs/release-v0.5.38.en.md)
proves the finite-dimensional Naimark theorem, preservation of Born probabilities
and density matrices, and unitary extension with a fixed pure ancilla. Partial
trace yields the canonical Lueders instrument. Identical POVM effects need not
determine identical state updates. The constructions are noncomputable; minimality,
infinite-dimensional spectral measures and physical circuit synthesis are outside scope.

## Earlier additions in v0.5.37

[Quantum depolarizing channel and CHSH damping](docs/release-v0.5.37.en.md)
proves Kraus completeness, trace preservation and complete positivity for every
finite ancilla dimension. It derives Bloch scaling, channel composition, the noisy
E91 singlet, CHSH damping and key QBER. The physical parameter range is [0,1].
Channel capacity, key secrecy, DI-QKD and finite-key statistics are outside scope.

## Earlier additions in v0.5.36

[Quantum E91 correlations and CHSH violation](docs/release-v0.5.36.en.md)
derives all nine correlations from singlet Born probabilities, proves the exact
CHSH value -2 sqrt(2), and separates key, test and discarded rounds. It proves
classical bounds for finite local laws and separable qubit mixtures. The explicit
XZ intercept/resend instrument on the supplied singlet produces a separable state.
Universal Tsirelson bounds, device-independent secrecy and finite-key statistics
are outside scope.

## Earlier additions in v0.5.35

[Operational Multi-Paxos consensus](docs/release-v0.5.35.en.md) derives slot
Agreement across ballots from reachable protocol transitions and Promise snapshots,
without an external SingleVote premise. One phase-one certificate supports multiple
slots; replica execution preserves comparable chosen prefixes. Safety tolerates
arbitrary message delays and duplicates. Liveness is not proved; progress requires
additional leader, quorum, delivery and scheduler assumptions.

## Earlier additions in v0.5.34

[BB84 QBER from Born measurement](docs/release-v0.5.34.en.md) derives a
trace-preserving intercept-resend channel with prefactor one half. The sifted
error probability is exactly one quarter under full interception, and f/4 for
independent interception with probability f. For m independent sifted rounds,
detection probability is 1-(3/4)^m; evasion remains possible on every finite sample.
The model assumes ideal Z/X preparations, projective measurement and an
authenticated classical channel. Full QKD secrecy is outside its scope.

## Earlier additions in v0.5.33

[Linear-optical quantum teleportation](docs/release-v0.5.33.en.md) derives ten
Kraus operators from the Bell analyzer on an invariant twenty-dimensional sector.
Success is one half for every density operator. Conditional Pauli corrections
recover the input exactly, with squared Uhlmann fidelity one. The unconditioned
channel gives Bob the maximally mixed state. The scheme assumes an ideal supplied
Bell resource, ideal optics and detection; deterministic teleportation is outside scope.

## Earlier additions in v0.5.32

[Linear-optical Bell analyzer](docs/release-v0.5.32.en.md) derives a unitary
normalized ten-dimensional two-photon evolution from balanced splitters.
It computes all four Bell outputs and derives positive, complete detector POVM
effects and the Born identity. Psi-plus/minus are identified without error;
Phi-plus/minus have identical outcome distributions. Success is one half for
the uniform ensemble and one for a Psi-only ensemble. The result concerns this
fixed ideal scheme; the universal bound for arbitrary optical networks is outside scope.

## Earlier additions in v0.5.31

[Observed-remove set and causal add-wins](docs/release-v0.5.31.en.md)
derives fresh tags from operational counters and proves add-wins for concurrent
operations and complete post-operation snapshots. Componentwise metadata union is
an unconditional join semilattice. Equal included updates give equal states;
authentic reliable snapshots and explicit fairness imply dissemination and,
after updates cease, stabilization. The causal-broadcast adapter and counterexamples
to tag reuse and premature tombstone collection are included. Tombstone GC,
ORSWOT compression and linearizability remain outside scope.

## Earlier additions in v0.5.30

[State-based LWW register and strong convergence](docs/release-v0.5.30.en.md)
derives unique stamps from fresh writes and constructs a join semilattice on
compatible states. Equal included update sets give equal register payloads.
Fair sending and reception of reliably available useful snapshots imply information
dissemination; after writes cease, replicas stabilize to the global maximum.
An incremental causal-broadcast adapter and collision/stale-write counterexamples
are included. Consensus, linearizability and physical-time ordering are outside scope.

## Earlier additions in v0.5.29

[Causal broadcast and delivery safety](docs/release-v0.5.29.en.md) connects
independent broadcast causality with operational delivered-prefix counters and
buffer guards. Prefix integrity, at-most-once delivery, exact causal-past timestamps
and causal delivery order are proved. Eventual delivery requires reliable arrival
and per-message weak fairness. Reordered arrivals and weakened-guard counterexamples
are covered. The fixed-group model excludes failures, total-order guarantees and
physical delay bounds.

## Earlier additions in v0.5.28

[Postselected photonic controlled-Z](docs/release-v0.5.28.en.md) derives
K(T)=diag(T,T,T,2T-1) from a unitary six-mode optical network and its
21-dimensional two-photon lift. At T=1/3 the accepted branch is CZ/3,
with success probability 1/9 for every normalized input. Pauli conjugation,
graph-state entanglement and reduced density matrices are proved.
The model uses ideal coincidence postselection; nondestructive heralding,
losses, detector noise and scalable KLM implementations are outside its scope.

## Earlier additions in v0.5.27

[Vector clocks and causal order](docs/release-v0.5.27.en.md) proves exact
correspondence between independently defined event causality and vector comparison.
The causal-past invariant gives injective timestamps and detection of causal
incomparability. Executable traces cover reordered delivery and outstanding messages;
a two-process bridge preserves the older clock API. The model uses fixed processes,
unbounded counters and authentic immutable timestamps, without a delivery-liveness claim.

## Earlier additions in v0.5.26

[Raymond tree message complexity](docs/release-v0.5.26.en.md) connects
actual isolated protocol send counters to sharp diameter and height bounds.
Finite completion is proved separately. Complete k-ary trees have exact
node counts, diameter 2h and worst-case sends 4h=4 floor(log_k N), with IsBigO.
The binary height-three regression requires 12 messages. Concurrent load,
amortization, random traffic and physical delays are outside this extension.

## Earlier additions in v0.5.25

[Two-photon Hong–Ou–Mandel interference](docs/release-v0.5.25.en.md) derives
the unitary normalized two-photon lift, output probabilities and balanced bunching.
A unitary gauge connects the real and complex conventions. Independent labeled
paths give the distinguishable baseline and exact HOM visibility. Temporal
wave packets, partial distinguishability, losses and detector imperfections
are outside this finite model.

## Earlier additions in v0.5.24

[Complex beam splitter and MZI](docs/release-v0.5.24.en.md) adds the lossless
unitary convention U=B†DB, output probabilities derived from complex amplitudes,
exact Solaris intensity bridges and a certified interference visibility model.
A static phase offset preserves the extrema and contrast. The pi/2 reflection
phase is model-specific; Maxwell equations, dispersion, polarization and physical
noise are not modeled.

## Earlier additions in v0.5.23

[Balanced Deutsch-Jozsa oracle classification](docs/release-v0.5.23.en.md) adds an
explicit support bijection, exact binomial counts for positive n, the empty
zero-qubit family, and equivalence between balance and zero amplitude/probability
in the existing runDJ circuit. Counts 0,2,6,70 and a first-bit projection witness
are proved. Efficient enumeration, asymptotic density and hardware are not claimed.

## Earlier additions in v0.5.22

[General Chandy-Lamport snapshots](docs/release-v0.5.22.en.md) add consistent cuts,
exact ordered FIFO channel records, and conditional termination on finite directed
networks. Termination requires root reachability, eventual message progress and
weak fairness of local snapshot reactions. Explicit executions demonstrate the
non-FIFO recording anomaly and the need for reachability. Causal permutation
equivalence, failures, dynamic topology and overlapping snapshots are not claimed.

## Earlier additions in v0.5.21

[Schnorr identification](docs/release-v0.5.21.en.md) adds perfect completeness,
algebraic witness extraction from two accepting transcripts with one commitment
and distinct challenges, and exact equality of real and simulated transcript
PMFs. The simulator has no secret input. Perfect special HVZK covers fixed or
independent honest-verifier challenges. Malicious-verifier security, computational
hardness, polynomial runtime and Fiat-Shamir signatures are not claimed.

## Earlier additions in v0.5.20

[Pedersen homomorphic sums](docs/release-v0.5.20.en.md) add exact linear-combination
identities and PMF hiding over a finite prime-order group. Aggregate hiding needs
an independent uniform mask with a nonzero weight. Collisions with distinct
messages yield an algebraic DLOG extractor; computational hardness is not proved.
The aggregate concerns a scalar weighted sum, not the full vector of messages.

## Earlier additions in v0.5.19

[Raymond tree mutual exclusion](knowledge/09_distributed_systems/DistributedRaymondTreeMutex.md)
proves token conservation, mutual exclusion and effective holder routing. Starvation
freedom requires delivery, weak local fairness and finite CS occupancy. Isolated
completed entries cost exactly twice the initial tree distance in messages. A reachable
counterexample establishes that raw holder pointers can form a two-cycle during transit.

**3585 strict build jobs**, **66 public live tests**, no warnings or skips.
All 164 root-inclusive Lean sources match private snapshot `d4a72dfb`.
See the [public release report](docs/release-v0.5.19.en.md).

## Earlier additions in v0.5.18

[Shor LCM/GCD recovery](knowledge/03_quantum_physics_and_optics/QuantumShorOrderRecoveryGCD.md)
proves conditional recovery from certified divisors and the equivalent spectral GCD
criterion. Modular validation alone establishes a multiple of the order. A formal
counterexample shows that taking every candidate denominator can pass the check
while returning a proper multiple. Candidate selection and sampling probabilities
remain outside scope.

**3547 strict build jobs**, **65 public live tests**, no warnings or skips.
All 163 root-inclusive Lean sources match private snapshot `5e714619`.
See the [public release report](docs/release-v0.5.18.en.md).

## Earlier additions in v0.5.17

[Shor continued fractions](knowledge/03_quantum_physics_and_optics/QuantumShorContinuedFractions.md)
adds executable candidates, strict Legendre recovery and the bound
**2·floor(log₂ Q)+1 Euclidean stages**. The correct reduced denominator is r/gcd(s,r).
Exact recovery is conditional; modular validation alone admits multiples of the order.
Bit complexity, repeated-sampling analysis and integer factorization are outside scope.

**3546 strict build jobs**, **64 public live tests**, no warnings or skips.
All 162 root-inclusive Lean sources match private snapshot `189077d1`.
See the [public release report](docs/release-v0.5.17.en.md).

## Earlier additions in v0.5.16

[Suzuki–Kasami mutual exclusion](knowledge/09_distributed_systems/DistributedSuzukiKasamiMutex.md)
proves reachable token conservation, mutual exclusion and queue invariants.
Eventual service requires reliable delivery, weak fairness and finite CS visits.
A reachable counterexample refutes LN ≤ RN at the holder; retained-token reentry
needs no artificial sequence increment. The operational serialization and exclusions
are documented explicitly.

**3543 strict build jobs**, **63 public live tests**, no warnings or skips.
All 161 root-inclusive proof sources match private snapshot `ef9c4813`.
See the [public release report](docs/release-v0.5.16.en.md).

## Earlier additions in v0.5.15

[Shor order-finding core](knowledge/03_quantum_physics_and_optics/QuantumShorOrderFindingCore.md)
constructs padded modular multiplication, its orthonormal orbit spectrum and the
coherent decomposition of the accessible input |1⟩. The actual QPE marginal is
derived as a uniform mixture of spectral components. The nearest-sample bound
is **4/π² per component**, giving an individual contribution of **4/(rπ²)**
to the mixture. Recovering the order, continued fractions, factorization and
physical gate synthesis remain outside scope.

**3542 strict build jobs**, **62 public live tests**, no warnings or skips.
All 160 root-inclusive proof sources match private snapshot `110558af`.
See the [public release report](docs/release-v0.5.15.en.md).

## Earlier additions in v0.5.14

[General Quantum Phase Estimation](knowledge/03_quantum_physics_and_optics/QuantumPhaseEstimationGeneral.md)
derives output amplitudes from an explicit controlled-power cascade and inverse
Fourier transform. It proves Fourier unitarity, exact dyadic recovery, normalized
probabilities and a nearest-sample success bound of **4/π²** for every real phase.
The supplied target eigenstate is normalized; its preparation, gate synthesis,
hardware noise and the full Shor algorithm remain outside scope.

**3541 strict build jobs**, **61 public live tests**, no warnings or skips.
All 159 root-inclusive proof sources match private snapshot `9970e917`.
See the [public release report](docs/release-v0.5.14.en.md).

## Earlier additions in v0.5.13

[Ricart–Agrawala](knowledge/09_distributed_systems/DistributedRicartAgrawalaMutex.md)
proves mutual exclusion on reachable states and eventual entry for each request
under explicit delivery, weak fairness and finite critical-section residence.
The [Simon conformance pilot](docs/statement-conformance.en.md) checks a pinned
independent contract and kernel-checked bridge; it is auxiliary tooling and adds
no subject import. It is not a universal detector of vacuous statements.

**3540 strict build jobs**, **60 public live tests**, no warnings or skips.
All 158 root-inclusive proof sources match private snapshot `09507001`.
See the [public release report](docs/release-v0.5.13.en.md).

## Earlier additions in v0.5.12

[Simon](knowledge/03_quantum_physics_and_optics/QuantumSimonsAlgorithm.md) derives
the complex two-register circuit and exact uniform weights on s-perp under the
nonzero-period promise. The unique nonzero solution is recovered when the
orthogonal observations span rank n-1 over F2. Sampling complexity and physical
implementation remain outside scope. See the [public release report](docs/release-v0.5.12.en.md)
and [Reservoir readiness](docs/reservoir-readiness.en.md).

**3537 strict build jobs**, **49 public live tests**, no warnings or skips.

## Earlier additions in v0.5.11

[Arbitrary-phase Grover](knowledge/03_quantum_physics_and_optics/QuantumGroverArbitraryPhase.md)
proves complex unitarity and invariant-plane preservation for every real phase pair
in dimension four with one marked item. For equal phases and the uniform input,
P(phi)=1-3*(1+cos(phi))^2/16; exact success is equivalent to cos(phi)=-1.
The canonical bridge at pi includes a global minus sign. This case does not
establish a noncanonical fractional correction of overshoot.
See the [public release report](docs/release-v0.5.11.en.md). **3535 strict build jobs**, **48 public tests**, no warnings or skips.

## Earlier additions in v0.5.10

[Static-epoch AND deadlock detection](knowledge/09_distributed_systems/DistributedChandyMisraHaasDeadlock.md)
proves probe provenance and detection soundness in a fixed wait graph, with
progress under explicit delivery assumptions and a dynamic phantom counterexample.
See the [public release report](docs/release-v0.5.10.en.md).

## Earlier additions in v0.5.9

[Two-participant 3PC](knowledge/09_distributed_systems/DistributedThreePhaseCommit.md)
adds operational safety, recovery and conditional completion. Accurate membership,
unique backup appointment and atomic epoch fencing are external contracts.
Eventual completion additionally requires a stable live view and weak action fairness.
See the [public release report](docs/release-v0.5.9.en.md).

## Earlier additions in v0.5.8

[Operational 2PC timeouts](knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md)
derives safe pre-vote abort, reachable-history indistinguishability and the unsafety
of unilateral prepared decisions based only on a timeout. With both participants
prepared and the coordinator stopped, blocking is characterized by absence of
queued decision packets. A decision in flight permits a delivery step; fairness,
recovery and completion of both participants are not established.
See the [public release report](docs/release-v0.5.8.en.md).

## Earlier additions in v0.5.7

[Raft commit application](knowledge/09_distributed_systems/DistributedRaftCommitApplication.md)
derives commit-index provenance, prefix retention and ordered deterministic local
application from operational traces. The package includes a reachable 45-transition
old-term-majority counterexample. Cross-node fold agreement requires equality of
full entries, including commands; no new global State Machine Safety is claimed.
See the [public release report](docs/release-v0.5.7.en.md).

## Earlier additions in v0.5.6

[QuantumDeutschJozsaGeneral](knowledge/03_quantum_physics_and_optics/QuantumDeutschJozsaGeneral.md)
proves the n-qubit Hadamard transform, XOR-ancilla phase kickback, circuit-derived
amplitudes and zero-error classification under the constant-or-balanced promise.
It covers n=0, exact one-qubit compatibility and counterexamples outside the promise.
Physical implementation, gate synthesis and complexity bounds are not claimed.
See the [public release report](docs/release-v0.5.6.en.md).

## Earlier additions in v0.5.5

[QuantumGroverMultipleTargets](knowledge/03_quantum_physics_and_optics/QuantumGroverMultipleTargets.md)
proves exact N=4 real-amplitude dynamics for every target subset and every natural
iteration count, arbitrary-state norm preservation, the invariant symmetric plane
for nonempty proper target sets and exact compatibility with the original singleton
model. Two counterexamples delimit agreement with rank-one reflection.
Arbitrary N, oracle query complexity, fractional phase rotations, physical noise
and hardware remain outside scope. Born-rule interpretation is external.

See the [public release report](docs/release-v0.5.5.en.md).

## Earlier additions in v0.5.4

[QuantumPhaseEstimation](knowledge/03_quantum_physics_and_optics/QuantumPhaseEstimation.md)
proves controlled U/U² phase kickback, inverse Fourier cancellation and deterministic
recovery of the exact phases 0, 1/4, 1/2 and 3/4. The target operator preserves norm,
and its normalized exact eigenstate is supplied as an input hypothesis.
Approximate QPE, spectral leakage/error bounds, eigenstate preparation, noisy gates
and physical quantum hardware are outside scope.

See the [public release report](docs/release-v0.5.4.en.md).
That report records source correspondence and regression coverage. The fresh strict build passed **3524 jobs** and all **41 public tests** passed without skips.

## Earlier additions in v0.5.3

[DistributedChandyLamportSnapshot](knowledge/09_distributed_systems/DistributedChandyLamportSnapshot.md)
derives saved-cut consistency and exact completed-channel transit lists from
explicit two-process FIFO transitions. Partial recording has a separate theorem.
Termination, failures and arbitrary network topologies are not proved.

The public module removes one unused broad tactic import to pass the enabled
header linter on a fresh build; definitions and proof bodies are unchanged.
See the [public release report](docs/release-v0.5.3.en.md).
That report records source correspondence. The fresh strict build passed **3523 jobs** and all **40 public tests** passed without skips.

## Earlier additions in v0.5.2

[NumericSQLGapBounds](knowledge/12_numeric_certificates/NumericSQLGapBounds.md)
proves the affine enclosure of `G=A/I+B*I-2*sqrt(A*B)`, its exact-zero balance
criterion for positive parameters, canonical +0 and composition with real rounding.
Exact zero is distinct from a positive midpoint underflowing to +0.
Historical indeterminate records are retained alongside separate exact evidence.

Rationalization, exact cell-boundary comparison, the SimLab cell-search algorithm,
Python, JSON/SHA-256 and external input-byte binding remain outside these proofs.
The strict build passed 3,522 jobs and all 39 public tests passed without skips.
See the [public release report](docs/release-v0.5.2.en.md).

## Earlier additions in v0.5.1

This release adds exact binary rounding certificates, a real-input extension,
conditional enclosures of `sqrt(hbar/(mass*frequency))`, and a conditional bridge
through caller-supplied digest and parser functions. Three registry suites are
implemented by five Lean source files. The strict public build passed 3,521 tasks and all 38 public tests passed without skips. See the [release record](docs/release-v0.5.1.en.md).

SHA-256 implementation, JSON/Python conformance, authenticated provenance and the
separate SimLab gap `A/I+B*I-2*sqrt(A*B)` remain outside these results. Historical
indeterminate interval records are preserved; separate exact evidence does not
rewrite them.

## Earlier additions in v0.5.0

This release reaches **100 direct registry imports**, with three new domain
packages and an acyclic milestone registry. It adds five Lean files in total.

- [Time interval envelopes](knowledge/09_distributed_systems/DistributedMarzulloAlgorithm.md):
  truth inclusion under an explicit fault bound; maximum-overlap localization is
  refuted by a counterexample. No full NTP implementation is claimed.
- [Elementary transcript forking](knowledge/07_cryptography/CryptoTranscriptForkingLemma.md):
  finite matrix counting and scalar extraction, not the general multi-query
  Bellare–Neven lemma or a ROM security proof.
- [Beam splitter](knowledge/03_quantum_physics_and_optics/QuantumBeamSplitterTransform.md):
  real mode and finite two-boson norm preservation, with an ideal balanced HOM zero;
  complex phases, full Fock space, and physical detectors remain outside scope.
- [Milestone registry](knowledge/11_meta_registry/MasterHundredRegistry.md):
  selected existing guarantees assembled without changing hypotheses.
  `MasterSuiteComponents` prevents cyclic imports and preserves component names.
  The import count is not a count of independent domain results.

## Earlier additions in v0.4.5

This release adds finite-field batch counting and conditional scalar noise
optimization, bringing the registry to 96 direct imports.

- [Schnorr batch verification](knowledge/07_cryptography/CryptoSchnorrBatchVerification.md)
  proves completeness and exact accepting fractions `1/q` and `(1/q)^k` for
  a fixed nonzero discrepancy over a prime field. The coefficient space contains
  all vectors, including zeros. Uniform independent sampling is the interpretation
  of the finite counting ratios, not an implemented sampler. EUF-CMA security,
  CSPRNG correctness, and the BIP340 coefficient algorithm are outside scope.
- [Conditional standard quantum limit](knowledge/03_quantum_physics_and_optics/QuantumStandardQuantumLimit.md)
  proves the attained minimum `2*sqrt(A*B)`, balance, and unique positive optimizer
  `sqrt(A/B)` of `A/I + B*I`. SQL-shaped bounds require explicit calibration.
  The omitted noise correlation term is a modeling choice; no physical derivation
  of calibration or detector certification is claimed.

## Earlier additions in v0.4.4

Release v0.4.4 added two scalar algebraic models, bringing the registry to 94 direct imports.

- [MuSig2-style aggregation](knowledge/07_cryptography/CryptoMuSig2Aggregation.md)
  proves two-signer, two-nonce completeness and a restricted barrier to naive key
  subtraction. Weights and challenges are supplied real scalars. Hash-based
  rogue-key resistance, secp256k1, and the two-round network protocol are not proved.
  Fixed weights admit a chosen target key; scalar public keys reveal their secrets.
- [Interference visibility](knowledge/03_quantum_physics_and_optics/MithraicPhaseCollapse.md)
  proves bounds, exact zero/unit contrast criteria, fixed-maximum monotonicity,
  and threshold validity. Equality at the threshold is accepted. These results
  do not establish quantum decoherence or physical dump-port control.

## Earlier additions in v0.4.3

This release adds the Raft network induction and complete bridge, with eleven new
Lean files including supporting proofs. `reachable_global_log_matching` and
`reachable_leader_completeness` follow from the unchanged operational transitions.
Commitment is witnessed by an actual `Step.commit` in a finite execution, including
the majority replication evidence and current-term anchor.

A node already holding the entire committed prefix retains it through later steps
of that execution. Delayed acknowledgements, message loss, duplication, arbitrary
delivery order, and conflict-sensitive partial AppendEntries are covered.
The model has a fixed nonempty cluster and protocol-generated messages. Dynamic
membership, crash/recovery, Byzantine packet injection, and liveness are outside
scope; this is not a certification of a deployed Raft implementation.

See the [complete bridge card](knowledge/09_distributed_systems/DistributedRaftCompleteBridge.md)
and [validation record](knowledge/VERIFICATION.en.md).

## Earlier additions in v0.4.2

Release v0.4.2 added scalar Feldman share verification, translation and rectangular
placement geometry, an exact 256-node placement certificate, and scalar
optomechanical coupling. The concrete certificate is a separate registry module,
bringing that release to 90 direct imports.

- Feldman verification and reconstruction are algebraic statements over the reals.
  The public scalar commitment reveals the secret as `A0/G`; hiding is not claimed.
- The placement certificate checks 256 nodes in a 4000 by 4000 micrometre die,
  positive dimensions, unique identifiers, and pairwise disjoint closed rectangles.
  Bounds and nonintersection are separate statements. The packaged JSON and
  deterministic converter permit an external provenance check; Lean does not
  verify the JSON parser or SHA-256 implementation. No routes, optical losses, or
  propagation delays are certified.
- Optomechanics proves normalized scalar energy/force identities, affine frequency
  shifts, and properties of prescribed damping rates and an exponential envelope.
  The physical regime of `4*g^2/kappa` is documented, not derived in Lean. Neither
  quantum cooling nor full device stability is proved.

## What the proofs establish

Each result applies to its formal definitions and hypotheses. This repository
does not prove the Collatz or Riemann conjectures, resolve the Hopf problem, or
establish end-to-end security of the named protocols. Scalar commitment identities
do not prove cryptographic hiding or binding. Scientific priority of individual
formalizations has not been established.

Every module has an English knowledge card with its result, scope, and source links.

## Build and audit

Lean **4.33.1** and Mathlib **v4.33.1** are pinned. With elan installed:

```bash
lake build --wfail
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 tools/verifier_skill.py verify-all
python3 scripts/check_knowledge.py
```

`AxiomAudit.lean` checks the selected registry theorem's transitive axiom
dependencies. `verify-all` checks all project modules and audits all project
declarations in the imported environment. CI also runs an independent axiom audit.

## Verification tooling

The [verifier CLI and Python API](docs/verifier-skill.en.md) support strict module
verification, fresh axiom audits, integration using explicit recipes with source
rollback, and draft English knowledge cards. The tool operates on trusted local
projects; it is not a sandbox for untrusted Lean or Lake code.

[Contribution guide](knowledge/CONTRIBUTING.en.md) ·
[Machine-readable catalog](knowledge/catalog.json) ·
[Validation snapshot](tools/validation_snapshot.json)

## License and releases

Licensed under [Apache License 2.0](LICENSE). This repository is an independent
English-language source distribution with its own Git history and releases.
See [publication notes](docs/publication.en.md) for Reservoir requirements.

[Operational 2PC timeouts](knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md) separates safe pre-vote abort from unsafe unilateral prepared decisions, and characterizes blocking only with both participants prepared and a stopped coordinator. Delivery of an in-flight decision remains possible; fairness and recovery are not claimed.

[Two-participant 3PC](knowledge/09_distributed_systems/DistributedThreePhaseCommit.md) proves operational safety and conditional completion using a kernel-checked finite invariant certificate. Accurate membership, unique backup appointment and atomic epoch fencing are explicit external contracts. Weak fairness is required for eventual completion; no partition tolerance or runtime implementation is claimed.
