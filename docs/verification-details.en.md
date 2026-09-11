# Mathematical Verification Components in Lean 4

[![Lean verification](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml/badge.svg)](https://github.com/solanaqubits/lean-verification-components/actions/workflows/lean_action_ci.yml)

This project develops a machine-checked Collatz verification pipeline one
component at a time. It currently proves the trajectories of the finite base
set `{1, 2, 3, 4, 5}`, a conditional reduction after a trajectory enters that
set, the absence of positive one- and two-step returns, the canonical
three-step orbit `{1, 4, 2}`, parity identities modulo two, four, and eight, branch-specific iteration
formulas, and a separate real-valued inequality proposed as
part of a Collatz drift analysis. The project is pinned to Lean 4.33.1 and
Mathlib 4.33.1 so that the verification can be reproduced with the same
toolchain and dependencies.

## Explicit logarithmic threshold model

[`Verification/RiemannBounds.lean`](../Verification/RiemannBounds.lean) defines
`mainTerm(n) = 1 - log(log(n))/log(n)` and
`kappaCrit(n) = mainTerm(n) + (-1/8)/(log(n)^2)`. For natural inputs at least
one million, it proves input positivity, `log(n) > 1`, `log(log(n)) > 0`,
positivity of the squared denominator, and the two bounds

```text
mainTerm(n) - 4.85/log(n)^2 ≤ kappaCrit(n)
kappaCrit(n) ≤ mainTerm(n) + 4.60/log(n)^2.
```

These bounds concern the explicitly defined model with a selected coefficient
`-1/8`. No mollifier, integral kernel, Rayleigh quotient, or variational extremum
is defined or identified with this function. The module does not prove the
Riemann hypothesis, zeta-zero estimates, differentiability, or the finer decimal
logarithm bounds mentioned in the proposal. Relating this model to an independently
defined analytic threshold requires additional definitions and proofs.

## Bounds for the logarithmic main term

[`Verification/RiemannMainTerm.lean`](../Verification/RiemannMainTerm.lean) proves,
for natural inputs `n ≥ 1000000`, that the ratio `log(log(n))/log(n)` is strictly
between zero and one. Consequently `0 < mainTerm(n) < 1`. The negative
calibration contribution also gives `kappaCrit(n) < 1` for the explicit model
from `RiemannBounds`. These are bounds on the defined functions, not a
variational characterization or a differentiability theorem.

## Explicit half-to-one main-term interval

[`Verification/RiemannNumericBound.lean`](../Verification/RiemannNumericBound.lean)
proves `1/2 < mainTerm(n) < 1` for all natural inputs `n ≥ 1000000`.
It derives `log(4) < 2` from the strict exponential lower bound at one and
proves `exp(4) < 1000000` using `log(2) ≥ 1/2` and `2^8 < 1000000`.
No decimal approximation of the exponential is imported for this estimate.
The logarithmic tangent bound at `log(n)/4` then gives
`log(log(n))/log(n) < 1/2`.

## Explicit threshold interval and analytic suite

[`Verification/RiemannExplicitBound.lean`](../Verification/RiemannExplicitBound.lean)
proves `(log(n))^2 > 16`, the reciprocal bound `< 1/16`, and a calibration
correction greater than `-1/128`. Combining these with the main-term estimate
proves `kappaCrit(n) > 63/128 > 0.49` and `kappaCrit(n) < 1` for all natural
inputs at least one million.

`RiemannFormalSuite : Prop` collects the domain, main-term, calibration, and
threshold bounds. `riemann_master_verification_suite` constructs this package
from the existing proofs. Its dependencies are the standard `propext`,
`Classical.choice`, and `Quot.sound`, with no custom axioms or placeholders.
The suite concerns the explicit model with `c₀ = -1/8`; it does not verify a
Selberg–Levinson–Conrey mollifier or characterize a functional extremum.

## Scalar singular-energy model

[`Verification/HopfObstruction.lean`](../Verification/HopfObstruction.lean)
defines `singularEnergy(ε) = 1/ε - 1`. It proves positivity for `0 < ε < 1`,
the lower bound `1/(2ε) ≤ singularEnergy(ε)` for `0 < ε ≤ 1/2`, and that every
positive threshold is exceeded at a cutoff in `(0,1)`. The explicit witness is
`ε = 1/(M+2)`.

The last theorem establishes unboundedness of this scalar function. The module
does not define an integral, a sphere, an almost complex structure, a Nijenhuis
tensor, a curvature tensor, or a geometric measure. It therefore does not prove
an integral identity, a tensor L² estimate, or a geometric nonexistence theorem.
Relating this model to geometric energy requires the relevant definitions and
an independently proved estimate with the appropriate measure.

## Algebraic almost complex operators

[`Verification/HopfAlmostComplex.lean`](../Verification/HopfAlmostComplex.lean)
defines a real-linear operator with square negative identity and a skew bilinear
bracket. It proves compatibility with negation and subtraction, the inverse
identity `J(-J(x)) = x`, and absence of real eigenvalues on nonzero vectors.
For the algebraic Nijenhuis expression it proves skew symmetry,
`N(JX,Y) = -J(N(X,Y))`, and `N(JX,JY) = -N(X,Y)`.

The structure named `LieBracket` does not impose Jacobi. Its fields and the
almost complex identities are explicit hypotheses on structure instances, not
custom global axioms. No manifold, tangent bundle, smooth vector field, or
integrability theorem is defined here. These identities are compatible with a
zero bracket and hence a zero Nijenhuis expression; they do not establish
nonvanishing. A geometric obstruction on the six-sphere and an estimate linking
it to the scalar singular energy require additional definitions and proofs.

## Algebraic vanishing predicate and scaled energy suite

[`Verification/HopfIntegrabilityBarrier.lean`](../Verification/HopfIntegrabilityBarrier.lean)
defines `IsIntegrable` as vanishing of the algebraic Nijenhuis expression and
`HasNijenhuisObstruction` as existence of a nonzero value. It proves the direct
implication from the latter to the negation of the former. This is a logical
consequence of the definitions, not a proof of the Newlander–Nirenberg theorem.

For the scalar model `scaledSingularEnergy(C, ε) = C * singularEnergy(ε)`, the
module proves positivity on the stated domain and unboundedness for any `C > 0`.
The existential threshold theorem is not a separately formalized filter-limit
statement. The scale is an independent real parameter: no construction from a
nonzero Nijenhuis tensor or geometric energy lower bound is provided.

`hopf_master_verification_suite : HopfFormalSuite V` bundles these statements
with the prior operator and Nijenhuis identities for a real module `V`. It does
not assert existence of the input structures or prove nonintegrability on a
sphere. All audited theorems here, including the obstruction implication, depend
on `propext`, `Classical.choice`, and `Quot.sound`; no custom axioms are introduced.

## Prescribed quadratic quotient model

[`Verification/LamzouriMollifier.lean`](../Verification/LamzouriMollifier.lean)
defines two real quadratic functions and their ratio. Completing the square
proves that the denominator is positive for every real parameter. Exact
arithmetic verifies `N(1) = 8/15`, `M(1) = 11/28`, and
`R(1) = 165/224 > 73/100 > 6725/10000`.

These theorems concern the prescribed algebraic functions. The denominator's
integral representation is now supplied by `LamzouriMeasure` below. No
Hilbert-space operator or zeta-zero counting function is defined, and no
relation between the ratio and a proportion of zeros is proved. Operator
coercivity and number-theoretic interpretation require independent proofs.

## Trial-polynomial integral and minimum

[`Verification/LamzouriMeasure.lean`](../Verification/LamzouriMeasure.lean) defines
`P_c(x) = (1-x) + c*x*(1-x)`, its square, and three polynomial antiderivatives.
It verifies their derivatives and combines them to prove the actual Lebesgue
interval-integral identity
`(∫ x in 0..1, trialPolySq c x) = normFunctional c`.
Continuity supplies interval integrability for the fundamental theorem of
calculus. This is the integral of the square (the squared L² norm), not the
L² norm itself.

The scalar quadratic satisfies `normFunctional c ≥ 1/8`, with equality
exactly when `c = -5/2`. The retained name `norm_functional_coercive` denotes
this uniform bound, not an operator-coercivity theorem. No bundled L²-space
element or operator is constructed. The new theorems are checked through the
root import and project-wide audit, and included in the extended master suite.

## Quotient comparison and interval robustness

[`Verification/LamzouriOptimization.lean`](../Verification/LamzouriOptimization.lean)
proves the equivalence `lam < R(c) ↔ lam * N(c) < M(c)` using positivity of the
denominator. It verifies `R(0) = 3/4`, `R(2) = 247/336`, and both threshold
comparisons. An additional theorem proves `R(c) > 6725/10000` throughout `[0,2]`,
rather than inferring an interval bound from its endpoints. `LamzouriFormalSuite`
collects these results with the original identities at one, and
`lamzouri_master_verification_suite` proves the package.

This completes the stated algebraic quotient checks. No maximizing parameter,
operator coercivity, spectral realization, or zeta-zero proportion is proved.
The interval theorem and suite depend only on the standard Lean axioms.

## Quartic coordinate geometry

[`Verification/FinslerPolyMetric.lean`](../Verification/FinslerPolyMetric.lean)
defines a four-coordinate real space and the polynomial `x1 * x2 * x3 * x4`.
It proves degree-four homogeneity, componentwise multiplicativity, the exact
zero-locus criterion, a nonzero isotropic example, positivity on the positive
coordinate cone, and invariance under diagonal scalings whose parameters
multiply to one.

This module defines the diagonal polynomial, not a four-argument multilinear
form or a norm. `HyperbolicBoost` permits negative parameters; preservation of
the positive cone is therefore not asserted. No group structure, identification
with a Lorentz group, or algebra-automorphism property is proved. The module is
checked by the root import, with selected guarantees included in the Finsler suite.

## Symmetric polarization and diagonal scaling group

[`Verification/FinslerMultilinear.lean`](../Verification/FinslerMultilinear.lean)
defines the normalized sum of 24 coordinate products. Its diagonal equals
`berwaldMoorForm`. The module proves symmetry under each adjacent argument
transposition and additivity and real homogeneity in all four arguments.
These are explicit identities on `Point4`; no bundled Mathlib
`MultilinearMap` is introduced.

The diagonal scalings carry a `CommGroup` instance, with coordinatewise
multiplication and inversion. Identity, composition, and simultaneous
invariance of the polarized form are verified. This is a group of
form-preserving scalings, not an asserted group of automorphisms of the
componentwise algebra. Negative scaling parameters remain allowed.
Selected invariants are included in the Finsler component of `MasterSuite`.

## Recursive certificate checker

[`Verification/ProofGraphDAG.lean`](../Verification/ProofGraphDAG.lean) defines
propositional formulas, their semantics, finite certificate trees, and a
computable conclusion checker. It supports base references, truth, modus
ponens, and conjunction introduction (`zkFold`). Conditional on `SoundBase`,
every accepted conclusion is true in the supplied model. Batch acceptance
is equivalent to every certificate matching its expected formula, and implies
semantic soundness under the same base assumption.
`proof_dag_master_verification_suite` packages both soundness results.

The inductive representation is a tree: it has no explicit node identifiers,
shared subproofs, or graph-edge validation. The checker does not establish the
truth of external base facts. Despite the retained `zkFold` name, this module
contains no ZK-STARK protocol, proof compression, or cryptographic security
theorem. Its conditional soundness suite is included in `MasterSuite`.
The suite depends on `propext` and `Quot.sound`.

## Rational SPN diffusion invariants

[`Verification/CryptoSPNInvariants.lean`](../Verification/CryptoSPNInvariants.lean)
defines four rational coordinates, their Hamming weight, and the specified
circulant diffusion. For the implemented row convention, the inverse is
`circ(-4, 3, -11, 17) / 35`; both inverse identities and bijectivity are proved.
Every weight-one input has output weight four. The global weight sum is at
least five for every nonzero input, with equality for weight-one inputs.
No coordinate axis is preserved on its nonzero vectors.

A coordinatewise substitution with a two-sided inverse yields a bijective
round after diffusion. An injective substitution that also fixes zero
preserves activity, giving full diffusion for weight-one round inputs.
The explicit zero-preservation assumption matters.

These results concern rational coordinates, not bytes in a finite field.
They do not prove cipher security, multi-round wide-trail bounds, or
classification of all invariant subspaces. The global branch bound is
proved directly; no matrix-minor theorem is declared.
`CryptoSPNFormalSuite` packages the inverse, diffusion, branch-bound, and
round-bijectivity results. This suite is included in `MasterSuite`.

## Two-mode coordinate and phase invariants

[`Verification/SpinPhotonicWaveguide.lean`](../Verification/SpinPhotonicWaveguide.lean)
defines four real mode coordinates and their sum-of-squares energy. Energy
is nonnegative, vanishes exactly at the zero state, and is preserved by the
specified mixing when `c² + s² = 1`. The prescribed phase difference equals
`2 * dk * L` and is positive for positive `dk` and `L`. The geometric profile
`psi0 * r^n` strictly decreases at each step for `psi0 > 0` and `0 < r < 1`.
`SpinPhotonicFormalSuite` packages these statements.

No complex unitary matrix or adjoint identity is defined here. The module
does not derive a material model, a symmetry-breaking mechanism, a lattice
eigenmode, or a topological invariant. The geometric profile is prescribed;
the theorem establishes stepwise decay, not a formal limit or a physical
localization result. The scalar and energy guarantees are included in `MasterSuite`.

## Seven-coordinate cross product

[`Verification/HopfOctonions.lean`](../Verification/HopfOctonions.lean) defines the
explicit Fano-triple cross product on seven real coordinates. It proves
bilinearity, skew symmetry, vanishing on equal arguments, and orthogonality
to both inputs. The identity
`cross7 p (cross7 p v) = (dot p v) • p - (dot p p) • v`
implies `J_p²(v) = -v` when `dot p p = 1` and `dot p v = 0`.
The image remains orthogonal to `p`. A concrete triple of coordinate vectors
also proves nonassociativity.

These are coordinate identities. No eight-dimensional octonion algebra,
smooth sphere, tangent bundle, or bundled almost-complex structure is
constructed. Nonassociativity alone does not prove nonvanishing of a
Nijenhuis tensor; that connection remains unformalized.
`HopfOctonionsFormalSuite` collects the selected identities. The root imports
this module for build and project-wide audit; the registry includes its suite
alongside the original Hopf component.

## Positive indicatrix and diagonal quadratic energy

[`Verification/FinslerIndicatrix.lean`](../Verification/FinslerIndicatrix.lean)
defines the positive level set `G4(x) = 1` and the quadratic expression
`sum_i v_i² / x_i²`. The expression is nonnegative everywhere and positive
for nonzero `v` when all coordinates of `x` are positive.
Coordinate AM-GM inequalities yield
`G4(a) * G4(b) ≤ G4(midpoint(a,b))²` on the positive cone, hence
`G4(midpoint(a,b)) ≥ 1` for two indicatrix points.
Positive diagonal boosts preserve the cone and the indicatrix.

No Hessian calculation or identification with a Finsler fundamental tensor
is proved. The midpoint bound is non-strict; it does not claim strict
convexity or that the level set is a convex set. A topology, hypersurface
structure, and logarithmic parametrization are not constructed here.
`FinslerIndicatrixFormalSuite` packages the four principal guarantees.
The root build and project-wide audit include the module; its guarantees
are also included in the combined Finsler registry component.

## Indexed proof DAGs and acyclicity

[`Verification/ProofGraphAcyclic.lean`](../Verification/ProofGraphAcyclic.lean)
represents proof steps as a list with numeric prerequisite references, allowing
multiple steps to reuse the same earlier result. `ValidDAG` requires every
reference at position `k` to be less than `k`. Dependency edges point from
the dependent node to its prerequisite. Indices strictly decrease along every
nonempty `DependencyPath`, ruling out self-loops and cycles of all positive lengths.

`evalStep` reads only an already computed prefix; unavailable references,
failed prerequisites, and invalid modus ponens return `none`. The sequential
`runDAG` preserves `AllDerivedSound` under `SoundBase`. This semantic
soundness result also holds for malformed input graphs, since failed steps
produce no formula. It does not assert that every step succeeds, even when
the indices satisfy `ValidDAG`: formula compatibility is a separate check.

`ProofGraphAcyclicSuite` includes single-step and whole-run soundness as well
as acyclicity. Its axioms are `propext` and `Quot.sound`. No cryptographic
aggregation is implemented, and `ValidDAG` is a specification rather than a
separate executable Boolean validator. The root imports the module; the
registry includes this expanded soundness and acyclicity suite.

## Finite three-transition numerator checks

[`Verification/CollatzBakerBound.lean`](../Verification/CollatzBakerBound.lean)
defines `2^S - 27` over the integers and the natural numerator
`9 + 3*2^a1 + 2^(a1+a2)`. The denominator is positive exactly for `S ≥ 5`.
For positive three-part partitions of five, none of the six numerator values
is divisible by five. For partitions of six, divisibility by 37 occurs
exactly at `(2,2,2)`, giving quotient one.
`CollatzBakerFormalSuite` collects these arithmetic results.

Despite the retained module name, no Baker bound or linear form in logarithms
is proved. The general cycle equation and its connection to actual Collatz
trajectories are not derived here. The cases `S ≥ 7` are not excluded.
Three odd transitions must not be confused with three iterations of the
classical map; the classical orbit `1 → 4 → 2 → 1` remains a valid cycle.
The suite is checked by the root build and project-wide audit and included
in the combined Collatz component of the master registry.

## Generic deterministic trace checker

[`Verification/CryptoZKAir.lean`](../Verification/CryptoZKAir.lean) defines valid
adjacent transitions for an arbitrary function `F : α → α` and generates
a trace of length `n+1` starting at `init`. Generated traces satisfy all
transitions. With decidable equality, the Boolean checker is equivalent to
the validity predicate and accepts every generated trace. Two valid traces
with the same optional head and length are equal, including empty traces.

`CryptoZKAirFormalSuite` packages these properties. The module has no field,
polynomial constraints, interpolation domain, commitments, or ZK-STARK
protocol. It proves deterministic trace properties, not cryptographic
completeness, soundness, or zero knowledge. It is included in the root build
and project-wide audit, and included in the combined crypto registry component.

## Prescribed two-level gap bounds

[`Verification/QuantumTransmonEngine.lean`](../Verification/QuantumTransmonEngine.lean)
defines positive parameters `EC`, `EJ` and the scalar squared gap
`(4*EC*(1-2*ng))² + EJ²`. Its square root is at least `EJ > 0` and equals
`EJ` at `ng = 1/2`. The squared-gap deviation is nonnegative, vanishes
exactly at one half, and equals `64*EC²*(ng-1/2)²`. Consequently it is at
most `64*EC²*δ²` whenever `|ng-1/2| ≤ δ`.

`QuantumTransmonFormalSuite` collects the requested scalar guarantees.
No Josephson Hamiltonian, operator spectrum, band structure, physical noise
process, or exponential suppression in `EJ/EC` is derived. The bound concerns
the squared gap of the prescribed model. The module is checked through the
root import and project-wide audit, and included in the combined quantum registry component.

## Sequential delivery-versus-payment settlement

[`Verification/AssetSettlement.lean`](../Verification/AssetSettlement.lean) models
two account slots with natural-number balances of two assets. A funded order
updates both exchange legs in one state transition; insufficient funds leave
the ledger unchanged. The module proves conservation of each asset, exact
credits and debits, and conservation during contract processing.

Processing a pending contract returns either an executed contract with the
exchanged ledger or a rejected contract with the original ledger. Executed
and rejected contracts are unchanged by processing. Reprocessing the returned
ledger and contract is idempotent. `AssetSettlementFormalSuite` includes
conservation, exact credits, the executed-status no-op, and idempotence.

This is a sequential state-machine model, not a deployed settlement protocol.
Replay protection relies on retaining the updated contract status: there is
no persistent identifier registry to reject an old pending copy, authentication,
or concurrent execution model. Atomicity is represented by one ledger
transition, not a distributed two-phase commit proof. Zero-sized orders are
permitted. The root build and project-wide audit include the module; it is
included in the finance component of the master registry.

## Exact constant-product swap algebra

[`Verification/DeFiAMMInvariants.lean`](../Verification/DeFiAMMInvariants.lean)
defines `dy = ry*(gamma*dx)/(rx+gamma*dx)` over the reals, with the full input
added to the X reserve. For positive reserves, input, and pricing multiplier,
the output is positive and less than the Y reserve. The remaining Y reserve
equals `rx*ry/(rx+gamma*dx)` and stays positive. The product is unchanged
when `gamma = 1` and nondecreasing when `0 < gamma ≤ 1`. The effective
output/input rate is strictly below the initial reserve ratio under these
assumptions, and output strictly increases with positive input.

`DeFiAMMFormalSuite` packages these exact algebraic guarantees. The model
contains no integer rounding, token transfers, deployed contract semantics,
external valuation, or arbitrage model. Conservation of market value and
absence of arbitrage are not asserted. The root build and project-wide audit
include the module; its suite is included in the finance registry component.

## Prescribed antisymmetric transport response

[`Verification/SpintronicTransport.lean`](../Verification/SpintronicTransport.lean)
takes a positive conductance scale `G0` and an integer parameter `C`.
It defines `sigma = C*G0` and the response `[[0,sigma],[-sigma,0]]`.
The longitudinal entries vanish and the power expression `J · E` is zero
for every field vector. The scalar `hallResistivity = (1/G0)/C` is reciprocal
to `sigma` when `C ≠ 0`.

For this sign convention the inverse is `[[0,-r],[r,0]]`, where
`r = hallResistivity`: the xy entry is **negative** r, and the yx entry is r.
Both compositions of the response and inverse transformations are proved
to be the identity for nonzero C and included in the suite.

These are algebraic properties of a prescribed response. No Berry curvature,
Chern-number construction, topological quantization theorem, microscopic
transport model, or experimental realization is derived. The integer C
and positive G0 are inputs. The root and project-wide audit include the
module; its suite is included in the quantum registry component.

## Two-asset portfolio variance algebra

[`Verification/PortfolioRiskEngine.lean`](../Verification/PortfolioRiskEngine.lean)
defines nonnegative normalized weights and prescribed nonnegative volatilities
with correlation in `[-1,1]`. It proves variance nonnegativity, the exact
diversification difference, and the upper bound by the squared weighted sum
of volatilities. The bound is strict when both weights and volatilities are
positive and correlation is less than one. At correlation minus one, variance
equals the squared exposure difference and vanishes exactly when
`w1*s1 = w2*s2`.

These are scalar identities and inequalities for the supplied parameters.
The module does not construct random returns, estimate covariance, prove
a matrix positive-semidefiniteness theorem for arbitrary signed vectors,
or verify a production risk system. The upper bound is not a general
subadditivity theorem for variance. The root build and project-wide audit
include the module; its suite is also included in the master registry.

## Prescribed Otto-cycle heat and efficiency formulas

[`Verification/QuantumHeatEngine.lean`](../Verification/QuantumHeatEngine.lean)
defines ordered positive frequencies and temperatures, heat flows
`Qh = wh*dp`, `Qc = wc*dp`, and work `W = Qh-Qc`.
It proves `W = (wh-wc)*dp`, positive work and heat flows for `dp > 0`,
and `W = etaOtto*Qh`. Both prescribed efficiencies lie in `(0,1)`.
The comparison `etaOtto < etaCarnot` follows under the explicit assumption
`Tc/Th < wc/wh`.

The common hbar factor is omitted. No four-stroke state evolution, thermal
population formula, reservoir interaction, or connection to the transmon
module is derived. In particular, the temperature-ratio condition is assumed,
not deduced from `dp > 0` or a physical second-law argument.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## BFT quorum cardinality conditions

[`Verification/BFTConsensusQuorum.lean`](../Verification/BFTConsensusQuorum.lean)
proves inclusion-exclusion bounds for finite quorums, an honest intersection
under `N + f < 2*Q`, and enough honest participants under `Q + f <= N`.
The supplied manifest specializes these results to `N = 3*f+1`, `Q = 2*f+1`.
With at most `f` faulty nodes, the honest count is at least `N-f`, not
necessarily equal to it.

The configuration's lower bounds alone are insufficient: `f=1,N=6,Q=3`
allows disjoint quorums, while `f=1,N=4,Q=4` allows too few honest nodes.
These are combinatorial prerequisites, not protocol safety or liveness proofs:
no voting discipline, locks, decisions, network timing, or termination is modeled.
The root build and project-wide audit include this module; its suite is also included in the master registry.

## Integer congruence bounds for accelerated Collatz steps

[`Verification/Collatz2Adic.lean`](../Verification/Collatz2Adic.lean) defines the
parity-dependent step on integers, dividing by two on both branches.
It proves parity agreement from congruence modulo `2^k` for `k >= 1`,
exact differences on the even and odd branches, and the iteration bound
`2^(k+n) | (x-y) => 2^k | (T^n(x)-T^n(y))`.

This loses at most one binary digit per step. In the usual 2-adic metric it
corresponds to a Lipschitz bound of 2 per step, not 1 or a contraction.
The module proves a counterexample to preserving the same modulus at `x=0,y=2`.
It does not construct the extension to the 2-adic integers, prove a topological
continuity theorem there, or establish convergence of Collatz trajectories.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Binary Pauli labels and three-bit-flip syndromes

[`Verification/QuantumStabilizerCodes.lean`](../Verification/QuantumStabilizerCodes.lean)
represents Pauli labels by Boolean pairs with phase omitted. It proves symmetry
of the local and list symplectic products, identity multiplication, and zero
checks for each member of a pairwise commuting generator list.
For `ZZI` and `IZZ`, the syndromes of `III`, `XII`, `IXI`, and `IIX` are
respectively `00`, `10`, `11`, and `01`, with all six pairwise inequalities proved.

Lists are not indexed by a fixed qubit count: `zipWith` truncates unequal inputs.
The predicate named `IsCommutingStabilizerGroup` asserts pairwise commutation,
not group closure; the zero-syndrome theorem covers listed generators only.
No Pauli matrices, Hilbert-space code subspace, measurement process, or recovery
map is modeled. Syndrome distinguishability here is for the specified X-error
patterns, not a proof of correction of arbitrary single-qubit errors.
The root build and project-wide audit include this module; its suite is also included in the master registry.

## Prescribed photonic discriminant and real splitting

[`Verification/NonHermitianPhotonicEP.lean`](../Verification/NonHermitianPhotonicEP.lean)
proves the sign regimes of `kappa^2-gamma^2` for positive parameters,
its zero criterion `kappa=gamma`, positivity of the prescribed real splitting
above threshold, and its squared value in the nonnegative-discriminant regime.
It also proves the arithmetic mean identity for symmetric frequency offsets.

`IsExceptionalPoint` is defined as parameter equality. There is no operator
matrix, PT action, characteristic polynomial, eigenvector coalescence, or
Jordan-form argument. Complex eigenvalues and exponential dynamics are not
modeled. In Lean, the real square root of a negative number is zero: an
additional theorem explicitly shows that the real splitting formula also
vanishes below threshold, so its vanishing alone does not characterize an EP.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Aggregate channel balances and route timelocks

[`Verification/LightningHTLCNetwork.lean`](../Verification/LightningHTLCNetwork.lean)
proves capacity preservation for funded locks, claims, and refunds, with
insufficient balances producing a no-op. Route time gaps imply strict adjacent
decrease when `minDelta >= 1`, and the cumulative bound for tail index `k`
is `T_(k+1) + (k+1)*minDelta <= T_0`. It also proves balance neutrality for
an equal funded incoming/outgoing amount and positivity of an assumed fee.

The functions operate on an aggregate locked balance. They do not check hashes,
preimages, clocks, contract identities, or authorization, and claims/refunds
are not connected to the route timelocks. No network execution, settlement
latency, atomic multi-hop payment, or protection against conflicting claims is
modeled. Thus the arithmetic time margin does not itself guarantee timely
settlement or loss-free routing in Lightning.
The root build and project-wide audit include this module; its suite is also included in the master registry.

## Coefficient folding and numerical degree bounds

[`Verification/CryptoZKFRILowDegree.lean`](../Verification/CryptoZKFRILowDegree.lean)
folds adjacent coefficients as `c_even + alpha*c_odd` and proves the exact
output length `(length+1)/2`. A separate numerical recurrence halves a natural
number degree bound, giving `d/2^k`, which reaches zero when `d < 2^k`.
A real-valued evaluation identity relates a cubic at `x` and `-x` to the
folded linear expression at `x^2`, assuming `x != 0`.

The generic list theorem requires only addition and multiplication. The
numerical recurrence is not connected to the degree of a general Polynomial
object or to repeated coefficient folds. No finite-field protocol, evaluation
domain, random challenges, commitments, proximity testing, or probabilistic
soundness is proved. The module's suite is included in the master registry.

## Phase-free Clifford label transformations

[`Verification/QuantumCliffordTableau.lean`](../Verification/QuantumCliffordTableau.lean)
proves preservation of the binary symplectic form by single-qubit H and S
and two-qubit CNOT, their involutivity on phase-free labels, the listed basis
actions, and preservation of pair commutation under CNOT.

The Pauli types here are independent of the earlier stabilizer module.
There are no complex matrices, sign/phase updates, arbitrary-size tableaux,
circuit interpreter, measurements, or simulation-complexity theorem.
In particular, S squared acts identically on these binary labels; this does
not assert that the physical S gate squares to the identity.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Real skew-matrix commutator identities

[`Verification/NonAbelianHolonomy.lean`](../Verification/NonAbelianHolonomy.lean)
uses explicit real 3-by-3 matrices. It proves skew-symmetry of the three
rotation generators, closure under commutators, their cyclic commutation
relations, a nonzero commutator, and the Jacobi identity for arbitrary matrices.

The function named `wilczekZeeCurvature` defines only the commutator term.
There are no parameter-dependent connection fields, derivative terms, paths,
parallel transport, or holonomy operators. Noncommutativity of these generators
is an algebraic result, not a proof of noncommuting loop transports or a
Wilczek-Zee geometric-phase theorem. Real skew-symmetry is modeled directly.
The root build and project-wide audit include this module; its suite is also included in the master registry.

## Fixed-rate cycle returns and fee products

[`Verification/DeFiMultiHopArbitrage.lean`](../Verification/DeFiMultiHopArbitrage.lean)
factors a three-hop return into the rate product and fee product, proves that
valid fee products are at most one, and proves strict decay when `gamma1 < 1`.
If the prescribed spot-rate product is at most one, this strict fee condition
implies a return below one and loss for any positive input. Arbitrary finite
lists of valid fee multipliers also have product at most one.

These are conditional fixed-rate arithmetic statements. Fees alone do not
exclude arbitrage for inconsistent rates. There is no changing reserve model,
composition of the earlier AMM swap functions, slippage, execution uncertainty,
or general market no-arbitrage theorem. With all fees equal to one and a unit
rate product, the defined cycle return is one, so strict loss requires the
stated additional hypothesis.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Prescribed toric-code energy and count formulas

[`Verification/QuantumToricCode.lean`](../Verification/QuantumToricCode.lean)
checks parity of a supplied overlap count, including counts zero and two.
It proves decomposition of the prescribed scalar energy and positive pair
energy differences `4*Je` and `4*Jm`. Two counter updates add two defects
by definition.

No torus lattice, edges, star/plaquette operators, Hamiltonian operator,
physical state space, or spectral minimum is constructed. Defect counts have
no lattice-size or parity constraints. The increment functions are stipulated
pair creation, not a general local Pauli action: applying either twice adds
four rather than returning to the original count. Consequently these results
do not establish topological order or a spectral gap of an operator.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Real-valued base-fee update model

[`Verification/MechanismDesignEIP1559.lean`](../Verification/MechanismDesignEIP1559.lean)
proves the empty/target/full-block multipliers `7/8`, `1`, and `9/8`,
and the inclusive multiplier bounds for gas use between zero and twice a
positive target. A positive base fee remains positive on this interval.
For positive base fee and target, the update is stationary exactly at target
usage, increases above target, and decreases below target.

This is a real-valued formula: no integer rounding, minimum increment,
block validity rules, or correspondence to an executable Ethereum update
is formalized. The configuration structure is separate from the scalar
functions. There is no demand model, iterated convergence result, or
mechanism-design incentive theorem. The root build and project-wide audit
include this module; its suite is also included in the master registry.

## Finite Syracuse fibers and numerical cylinder weights

[`Verification/Collatz2AdicErgodic.lean`](../Verification/Collatz2AdicErgodic.lean)
proves positivity and the halving identity for the scalar weight `(1/2)^k`.
It evaluates the integer even and odd branches and computes all fibers of
output residues modulo two from representatives modulo four, and modulo four
from representatives modulo eight. Every such fiber has two elements, giving
normalized counts `1/2` and `1/4` respectively.

No Haar measure, measurable cylinder sets, map on the 2-adic integers,
all-ranks measure-preservation theorem, or ergodicity statement is constructed.
The odd-branch identity `T(2*y-1)=3*y-1` is not an inverse for arbitrary integer
targets. The finite computations concern precisely the representative sets in
the definitions; they do not by themselves prove invariance on all cylinders.
The root build and project-wide audit include the module; its suite is also included in the master registry.

## Scalar polynomial-quotient and pairing identities

[`Verification/CryptoKZGCommitment.lean`](../Verification/CryptoKZGCommitment.lean)
proves explicit quadratic and cubic division identities, linearity of
quadratic evaluation, and bilinearity of `pairingMap kappa a b = a*b*kappa`.
The prescribed cubic evaluation and quotient satisfy the verification equation.
For nonzero `kappa` and `s-z`, that equation determines `pi=(C-v)/(s-z)`.

This is real scalar algebra, without cryptographic groups, a structured
reference string, hidden exponents, or a computational security assumption.
The quotient theorem does not show that an accepted value equals `P(z)`:
for arbitrary `C,v` and `s!=z`, the scalar quotient can be chosen directly.
Consequently no evaluation-binding or cryptographic soundness theorem for
KZG is established. The root build and project-wide audit include the module;
its suite is also included in the master registry.

## Symplectic Euler and a conserved quadratic energy

[`Verification/SymplecticHamiltonianDynamics.lean`](../Verification/SymplecticHamiltonianDynamics.lean)
defines the oscillator drift-then-kick step. It proves determinant one for
the prescribed update coefficients, exact preservation of the stated shadow
energy, its square completion, and nonnegativity under `h^2*k < 4*m`.

The step is symplectic Euler, not the Verlet/leapfrog scheme. The theorem named
`symplectic_form_preserved` repeats the scalar determinant identity; no matrix
2-form, derivative identification, or measure-preserving map is constructed.
The energy result concerns the modified quadratic form, not exact conservation
of the original oscillator energy. No separate positive-definiteness or
trajectory-stability theorem is included. The root build and project-wide
audit include this module; its suite is also included in the master registry.

## Prescribed PBS values and balance credits

[`Verification/MechanismDesignPBS.lean`](../Verification/MechanismDesignPBS.lean)
proves nonnegative builder profit from the assumed bid bound, the bookkeeping
identity for MEV plus burn, and a total-balance increase of exactly MEV under
the defined credits. A winning bid dominates competitors by the maximality
clause of `WinningBid`.

The balance transition has no debit for gas burn and leaves escrow unchanged.
Actor balances and standalone auction bids are unrestricted real numbers.
No winner-selection algorithm, winner-existence theorem, incentive analysis,
block validation, payment enforcement, or connection between the auction
winner and the executed block is supplied. These are conditional accounting
results rather than verification of a complete PBS protocol. The root build
and project-wide audit include the module; its suite is also included in the master registry.

## Fixed-liquidity reserve identities

[`Verification/DeFiConcentratedLiquidity.lean`](../Verification/DeFiConcentratedLiquidity.lean)
proves the virtual-reserve product `L^2`, positivity of the prescribed real
reserves strictly inside an active range, and the translated-reserve product
identity. The defined Y increment is positive for a price increase; the X
increment is positive for a decrease between positive square-root prices.

The square-root prices are supplied real parameters. There are no discrete
ticks, boundary transitions, changing liquidity, swap execution, fees, or
fixed-point rounding. The increment formulas are not linked to an executed
sequence of position updates. The root build and project-wide audit include
the module; its selected suite is now included in the master registry.

## A two-dimensional Majorana matrix representation

[`Verification/QuantumMajoranaChain.lean`](../Verification/QuantumMajoranaChain.lean)
represents two Majorana operators by complex Pauli matrices. It proves their
self-adjointness, squares and anticommutation; explicit creation/annihilation
matrices and CAR; number-operator idempotence; and the parity representation,
involution, commutation with number, and anticommutation with both Majoranas.

This is a single fermionic mode in a two-dimensional matrix representation.
No spatial chain, Hamiltonian, bulk spectrum, edge localization, nonlocality,
or ground-state degeneracy is constructed. In particular, the parity
identities alone do not establish an energy-preserving map between ground
states. The root build and project-wide audit include the module; its selected suite is now included in the master
registry.

## Majority overlap and conditional election uniqueness

[`Verification/DistributedRaftConsensus.lean`](../Verification/DistributedRaftConsensus.lean)
proves nonempty majority intersections, uniqueness of two majority-supported
candidates under a shared single-choice vote function, commit/election quorum
overlap, and transitivity of the defined nondecreasing-term relation.

`LogMatchingInvariant` is a definition only. List positions are not constrained
to equal the index fields of their entries. No Raft messages, roles, elections
across terms, log-update rules, or persistence/crash behavior are modeled.
Quorum overlap alone establishes neither an honest intersection nor Leader
Completeness. The vote function is not linked to NodeState transitions, so
this is a conditional election argument, not a full protocol safety proof.
The root build and project-wide audit include the module; its selected suite
is now included in the master registry.

## Master registry

[`Verification/MasterSuite.lean`](../Verification/MasterSuite.lean) packages the
ten top-level packages in `VerificationMasterRegistry : Prop` and proves
`MasterSuite.verification_master_registry`. The Hopf component is quantified
over real modules. These packages include the original directions and subsequent extensions: Finsler and Lamzouri combine their base and extended results,
Hopf combines barrier and coordinate-product suites; Proof-of-Logic combines
tree and indexed-DAG guarantees.
Collatz combines its structural suite, finite numerator checks, integer congruence bounds, and finite residue-fiber counts;
crypto combines rational SPN invariants, generic trace guarantees, coefficient-folding results, and scalar KZG identities;
quantum combines mode-energy, gap, prescribed Otto-cycle, signed transport-response,
photonic discriminant, binary stabilizer-syndrome, phase-free Clifford,
skew-matrix commutator models, prescribed toric energy/count formulas, and symplectic Euler shadow-energy identities;
finance combines sequential settlement, exact constant-product swaps, portfolio variance bounds,
aggregate channel/timelock invariants, conditional fixed-rate cycle losses, real-valued base-fee bounds, and conditional PBS accounting;
distributed systems collects cardinal quorum intersection and availability conditions.
The registry directly imports 41 component modules; the project-wide audit also
covers their dependencies and declarations outside the registry.
The original Finsler suite remains available. The combined Lamzouri suite
preserves all earlier quotient guarantees and additionally includes the
actual interval integral, uniform lower bound, and unique minimum.
The registry collects the selected guarantees of each suite;
it preserves all scope limitations documented below. It does not assert new
geometric or number-theoretic conclusions. The original `Generated` module
remains checked through the root import independently of these packages.

## Build-time axiom gate

[`Verification/AxiomAudit.lean`](../Verification/AxiomAudit.lean) defines
`#audit_axioms Declaration.name` using Lean's transitive `collectAxioms` API.
It accepts only `propext`, `Classical.choice`, and `Quot.sound`; any other
axiom, including `sorryAx`, causes a compilation error. The module audits
`MasterSuite.verification_master_registry` and is imported by the root,
so the normal build runs the check when this module is compiled.

This is an allowlist policy, not an absence of all axioms. The command covers
the chosen declaration's dependencies, not every declaration in imported
modules. The existing project-wide CI axiom audit remains necessary for
declarations outside the registry's dependency closure.

## Integrated verification suite

[`Verification/CollatzUnified.lean`](../Verification/CollatzUnified.lean) imports
all fourteen staged modules and proves
`CollatzUnified.collatz_master_verification_suite : CollatzFormalSuite`.
The suite is a proposition with eight proof fields collecting:

- Exclusion of positive one-step and two-step returns.
- Reachability of one for every input in `[1,12]`.
- Coverage of odd inputs by the six residue branches.
- The integer inequality `3^30 < 2^49`.
- The exact weighted remainder sum `40/81`.
- Negativity of the defined weighted expression for `n ≥ 13`.
- The nonexclusive positive-input dichotomy.

The module imports the full staged development but its fields summarize selected
results, not every declaration. The separate original numerical theorem in
`Generated.lean` remains imported by the project root. The suite introduces no
custom axioms and has exactly the standard dependencies `propext`,
`Classical.choice`, and `Quot.sound`; it is not axiom-free.

The integration theorem does not define a Markov kernel or establish that the
weighted scalar expression is a conditional drift for actual trajectories.
Such a connection needs a specified process, potential, and proved transition
and return-time hypotheses. Even an almost-sure absorption result for a random
model would not by itself establish convergence of every deterministic Collatz
trajectory. The finite-prefix reachability results are proved, not assumed.

## Finite base trajectories

[`Verification/CollatzBase.lean`](../Verification/CollatzBase.lean) defines the
classical Collatz map on natural numbers and its iterates. Direct kernel
reduction proves the following trajectories:

| Start `n` | Steps `k` with `collatzIter k n = 1` |
| ---: | ---: |
| 1 | 0 |
| 2 | 1 |
| 3 | 7 |
| 4 | 2 |
| 5 | 5 |

The theorem `CollatzBase.collatz_base_absorption` uses `interval_cases` to
exhaust the interval `1 ≤ n ≤ 5` and supplies the corresponding witness `k` in
each case. Every resulting trajectory equality closes with `rfl`; the file has
no `sorry` or custom axioms.

## Reduction after reaching the base interval

[`Verification/CollatzAttractor.lean`](../Verification/CollatzAttractor.lean)
proves the composition law

```text
collatzIter (k₁ + k₂) n = collatzIter k₂ (collatzIter k₁ n).
```

It then combines this law with `collatz_base_absorption`: if a trajectory is in
`[1, 5]` after `k` steps, there is a total step count `m` at which it reaches
`1`. The module also proves the special case where the next Collatz value is in
the base interval.

## Short periodic orbits

[`Verification/CollatzCycles.lean`](../Verification/CollatzCycles.lean) defines
`IsPeriodic k n` to mean that `k` is positive and the trajectory returns to `n`
after `k` steps. Linear integer arithmetic proves that no positive natural
number returns after one or two steps. Kernel reduction verifies the canonical
three-step orbit:

```text
1 → 4 → 2 → 1.
```

The module proves the corresponding three-step return separately for `1`, `2`,
and `4`. The theorem `period_three_iff` also classifies these as exactly the
positive natural numbers that return after three steps.

## Parity and branching modulo four

[`Verification/CollatzParity.lean`](../Verification/CollatzParity.lean) proves that
an odd input has an even next value and satisfies
`collatzIter 2 n = (3 * n + 1) / 2`. It also proves:

- If `n % 4 = 1`, then `3 * n + 1` is divisible by four and
  `collatzIter 3 n = (3 * n + 1) / 4`.
- If `n % 4 = 3`, then `(3 * n + 1) / 2` is odd.
- Every odd natural number belongs to one of these two residue classes.

These are deterministic arithmetic identities. The two-step value from an
odd input is larger than the input; the three-step formula for `n % 4 = 1`
gives strict decrease only when `n > 1`. This module does not define Haar
measure, prove densities of valuation classes, or establish independence of
successive branches. Such probabilistic statements require a specified measure
and separate proofs before they can support a stochastic drift argument.

## Branch formulas modulo eight

[`Verification/CollatzDyadicContract.lean`](../Verification/CollatzDyadicContract.lean)
proves strict three-step decrease, including the bound `collatzIter 3 n ≤ n - 1`,
when `n ≥ 5` and `n % 4 = 1`. It also proves:

- If `n % 8 = 3`, the two-step value is one modulo four, and
  `collatzIter 5 n = (9 * n + 5) / 8`.
- If `n % 8 = 7`, the two-step value is three modulo four.
- Every odd input has residue one, three, five, or seven modulo eight.

The five-step formula for residue three describes an increase over the original
input, despite the decrease from its intermediate state. For example, the
five-step value starting at `3` is `4`. The residue partition is an arithmetic
statement; this module does not assign probabilities to its branches or prove
an averaged contraction. An averaging operator and its measure must be defined
and justified separately, including how branch-dependent step counts are used.

## Residue five and rational coefficient averages

[`Verification/CollatzAverageDrift.lean`](../Verification/CollatzAverageDrift.lean)
proves `collatzIter 4 n = (3 * n + 1) / 8` for `n % 8 = 5` and strict
four-step decrease under `1 ≤ n`. It defines constrained uniform rational
weights on the four odd classes and constructs an instance with total weight
one. Unlike field defaults alone, the equality fields enforce uniformity for
every instance.

The module checks the exact coefficient averages `9/16` for two branches and
`3/4 < 1` for three branches. It also checks the rational sum `27/32 < 1`
obtained by inserting a hypothetical fourth coefficient of `9/8`. The theorem
`total_four_branch_weighted_drift_bound` is only this rational identity:
no bound of `9/8` for residue seven is proved or assumed as a custom axiom.

These finite weights are not a formal construction of Haar measure. The
averages of leading coefficients omit additive terms and use different step
counts for different branches. They do not yet bound a Markov operator or the
drift of the potential `n^(1/3)`. Those connections require additional definitions
and proofs, including justification of the unresolved fourth branch.

## Splitting residue seven modulo sixteen

[`Verification/CollatzBranchSeven.lean`](../Verification/CollatzBranchSeven.lean)
proves that residue seven modulo eight splits into residues seven and fifteen
modulo sixteen. For the first subbranch, it derives the intermediate parity
conditions and the exact formula `collatzIter 7 n = (27 * n + 19) / 16` by
composing two, two, and three steps. Its leading coefficient `27/16` is greater
than one; this formula does not assert decrease relative to the initial state.

The module also proves `collatzIter 11 7 = 5`, then uses the finite-base
reduction theorem to prove that seven eventually reaches one. Finally,
`equal_weight_split` checks `1/4 = 1/8 + 1/8` over the rationals. This is weight
arithmetic only, with no identification with Haar measure. The next module refines the subbranch fifteen modulo sixteen. The earlier
hypothetical coefficient for the full residue-seven branch is still not justified.

## Splitting residue fifteen modulo thirty-two

[`Verification/CollatzBranchFifteen.lean`](../Verification/CollatzBranchFifteen.lean)
proves the intermediate parity conditions and the exact six-step formula
`collatzIter 6 n = (27 * n + 19) / 8` for `n % 16 = 15`. It proves
`collatzIter 12 15 = 5` and then derives eventual reachability of one from fifteen.

The module splits residue fifteen modulo sixteen into residues fifteen and
thirty-one modulo thirty-two. For the former it proves
`collatzIter 9 n = (81 * n + 65) / 32`. Both displayed formulas describe growth
relative to the initial value; the latter has leading coefficient `81/32 > 1`.
The next module supplies the eight-step formula for residue thirty-one modulo thirty-two.

A complete branch tree must retain the actual moduli: residues one, five, and
three modulo eight; seven modulo sixteen; and fifteen modulo thirty-two, plus
the remaining thirty-one modulo thirty-two branch. Five individual residues
`{1, 5, 3, 7, 15}` modulo thirty-two do not cover all odd inputs. No full averaged
contraction follows from these branch formulas alone.

## Complete six-branch tree

[`Verification/CollatzDyadicTree32.lean`](../Verification/CollatzDyadicTree32.lean)
proves coverage of odd inputs by the six leaves and uniqueness of the branch
index. The last branch satisfies `collatzIter 8 n = (81 * n + 65) / 16` for
`n % 32 = 31`. All leaves now have finite-step formulas; this does not prove
that all their trajectories eventually reach the base interval.

Kernel computation gives `collatzIter 39 31 = 167` and
`collatzIter 101 31 = 5`, correcting the proposed 39-step return to five.
The finite-base theorem then proves that thirty-one reaches one.

The module constructs nonnegative rational weights with total weight one.
It does not identify them with Haar measure or a transition kernel. For the
specified coefficients and weights, Lean proves:

- The first four contributions sum to `99/128`, not `27/32`.
- Dividing that partial sum by its weight `7/8` gives `99/112`.
- The complete six-branch weighted sum is `639/512 > 1`.

Thus these leading coefficients do not establish full arithmetic-mean
contraction. Normalizing logarithms by branch step counts would define a
different quantity and would require its own proof and connection to the dynamics.

## Geometric coefficient product

[`Verification/CollatzGeometricDrift.lean`](../Verification/CollatzGeometricDrift.lean)
computes the weighted exponents `15/8` and `49/16` and proves the exact integer
comparison `3^30 < 2^49`. It links the existing tree coefficients directly to

```text
coeff_b1^4 * coeff_b5^4 * coeff_b3^4 * coeff_b7^2 * coeff_b15 * coeff_b31
  = 3^30 / 2^49,
```

and proves that this rational product lies strictly between zero and one (and
is below `37/100`). The exponents here are sixteen times the selected weights.
Thus the ratio is the sixteenth power of the weighted geometric mean, not the
geometric mean itself. Numerically the ratio is about `0.365736` and its
sixteenth root about `0.939070`; these decimal approximations are explanatory.
The Lean module proves the rational product identity and bounds, without
introducing a real logarithm or root definition.

The arithmetic mean `639/512 > 1` and the geometric-product bound are both valid
for the specified coefficients. Neither is a substitute for proving a
transition law, handling additive terms, or connecting branch-dependent time
intervals to trajectory frequencies. This module does not establish contraction
of a Markov operator or of the potential `n^(1/3)`.

## Real logarithmic leading term

[`Verification/CollatzLogPotential.lean`](../Verification/CollatzLogPotential.lean)
transfers the proved integer comparison to real powers and applies strict
monotonicity of the logarithm. Expanding the logarithms proves

```text
30 * log 3 - 49 * log 2 < 0
```

and the normalized identity and inequality

```text
(15/8) * log 3 - (49/16) * log 2
  = (1/16) * (30 * log 3 - 49 * log 2) < 0.
```

The normalization uses branch weights, not elapsed Collatz steps. This is a
negative leading term for the selected coefficients. The module does not prove
that additive corrections fit within this gap for all `n ≥ 5`; the proposed
code contained no such theorem. It also does not define a transition operator
or prove a drift inequality for actual trajectories. A return-time argument
requires those additional links and its recurrence hypotheses to be established.

## Rational remainder bounds

[`Verification/CollatzRemainderBound.lean`](../Verification/CollatzRemainderBound.lean)
defines the six relative additive coefficients `1/3, 1/3, 5/9, 19/27, 65/81,
65/81`. It proves their weighted sum is `40/81`, each coefficient is below one,
and a generic positive-input correction bound `1 + r/n < 1 + 1/n` for `r < 1`.
For natural inputs `n ≥ 5`, it proves

```text
expected_remainder * (1/n) ≤ 8/81 < 1/10.
```

Equality with `8/81` holds at five and is also checked in Lean. These are
rational arithmetic bounds. This module does not prove the factorization of
actual natural-number iterates into real multiplicative corrections or bound
logarithmic corrections using `log(1+x) ≤ x`.

The bound alone cannot establish negative effective logarithmic drift for all
`n ≥ 5`: the previously computed leading gap is approximately `-0.062865`,
whereas `8/81` is approximately `0.098765`. Their sum is positive (these decimals
are explanatory numerical checks). A sharper estimate or a different threshold
and treatment of the remaining cases would require additional proofs.

## Effective scalar bound above thirteen

[`Verification/CollatzEffectiveDrift.lean`](../Verification/CollatzEffectiveDrift.lean)
uses `Real.one_sub_inv_le_log_of_pos` to bound the logarithmic gap from below
by `1 - 3^30 / 2^49`. A strict rational comparison with `640/1053` provides the
margin needed to prove, for every natural `n ≥ 13`,

```text
(15/8) * log 3 - (49/16) * log 2 + expected_remainder / n < 0.
```

Thirteen is a sufficient threshold for this estimate; no minimality is claimed.
The module separately verifies reachability of one for all inputs in `[1,12]`.
It checks that nine reaches five after fourteen steps and eleven reaches five
after nine steps, correcting the proposed fourteen-step value for eleven.

This combines a leading term and a linear correction as a scalar inequality.
It still does not identify that expression with a bound on a specified Markov
kernel's conditional drift or with the deterministic Collatz trajectory drift.
A global return theorem requires that connection and its hypotheses. A theorem
about all natural inputs must also handle zero: the existing Collatz map fixes
zero, so eventual reachability of one can only hold for positive inputs.

## Weighted expression and positive-input dichotomy

[`Verification/CollatzMarkovOperator.lean`](../Verification/CollatzMarkovOperator.lean)
defines six candidate branchwise logarithmic bounds and their weighted sum,
`tree32_markov_drift`. It proves equality with the effective scalar expression
from the previous module and strict negativity for `n ≥ 13`. It also proves
that every positive natural input either eventually reaches one or satisfies
`13 ≤ n` and negativity of this expression. These alternatives are not asserted
to be mutually exclusive.

Despite its name, this module defines no Markov transition kernel and proves no
conditional-expectation identity for actual Collatz trajectories. For a fixed
input, branch membership is determined by its residue; the six formal weights
have not been justified as conditional transition probabilities. The dichotomy
does not establish global reachability or a return-time bound. An integration
module may collect these results, but cannot remove the missing dynamical link
merely by conjoining them.

## Numerical contraction bound

[`Verification/Generated.lean`](../Verification/Generated.lean) defines

```text
gamma_factor_test(s) = 3^s / (2^(1+s) - 1).
```

Lean proves that suitable parameters exist by providing the explicit witnesses

```text
s = 1/3,  gamma = 0.94566,  N₀ = 5
```

such that `0 < s < 1`, `gamma < 1`, and, for every natural number `n ≥ N₀`,

```text
gamma_factor_test(s) * (1 + 1/(3n))^s ≤ (1 + gamma)/2.
```

In Lean, the decimal `0.94566` denotes the exact rational number `47283/50000`;
it is not a floating-point approximation. The proof reduces the cube-root
bounds to rational polynomial inequalities and contains no `sorry`, `admit`, or
custom axioms. The `#print axioms` command reports only the standard Mathlib
dependencies `propext`, `Classical.choice`, and `Quot.sound`.

## Scope

The sixteen Collatz modules prove exactly the finite trajectories, conditional reduction,
short-period results, parity identities, branch formulas, and numerical inequality described above. `IsPeriodic`
expresses a return after `k` steps rather than defining the least period; the
cycle classification is correspondingly stated in terms of three-step returns.
The project does not yet connect the numerical inequality to the Collatz map,
define a probabilistic transition model or Lyapunov function, or prove that an
arbitrary trajectory eventually reaches the finite base set. Consequently,
these results do not prove the Collatz conjecture. The numerical theorem also
makes no claim that `s = 1/3` is optimal, that `N₀ = 5` is minimal, or that
`gamma = gamma_factor_test(s)`.

## Reproducing the verification

After installing `elan`, an authorized collaborator can clone this private
repository and run:

```bash
git clone https://github.com/solanaqubits/lean-verification-components.git
cd Lean
source "$HOME/.elan/env"
lake build --wfail
lake env lean -DwarningAsError=true Verification/CollatzBase.lean
lake env lean -DwarningAsError=true Verification/CollatzBakerBound.lean
lake env lean -DwarningAsError=true Verification/CollatzAttractor.lean
lake env lean -DwarningAsError=true Verification/CollatzCycles.lean
lake env lean -DwarningAsError=true Verification/CollatzParity.lean
lake env lean -DwarningAsError=true Verification/CollatzDyadicContract.lean
lake env lean -DwarningAsError=true Verification/CollatzAverageDrift.lean
lake env lean -DwarningAsError=true Verification/CollatzBranchSeven.lean
lake env lean -DwarningAsError=true Verification/CollatzBranchFifteen.lean
lake env lean -DwarningAsError=true Verification/CollatzDyadicTree32.lean
lake env lean -DwarningAsError=true Verification/CollatzGeometricDrift.lean
lake env lean -DwarningAsError=true Verification/CollatzLogPotential.lean
lake env lean -DwarningAsError=true Verification/CollatzRemainderBound.lean
lake env lean -DwarningAsError=true Verification/CollatzEffectiveDrift.lean
lake env lean -DwarningAsError=true Verification/CollatzMarkovOperator.lean
lake env lean -DwarningAsError=true Verification/CollatzUnified.lean
lake env lean -DwarningAsError=true Verification/Generated.lean
lake env lean -DwarningAsError=true Verification/RiemannBounds.lean
lake env lean -DwarningAsError=true Verification/RiemannMainTerm.lean
lake env lean -DwarningAsError=true Verification/RiemannNumericBound.lean
lake env lean -DwarningAsError=true Verification/RiemannExplicitBound.lean
lake env lean -DwarningAsError=true Verification/HopfObstruction.lean
lake env lean -DwarningAsError=true Verification/HopfAlmostComplex.lean
lake env lean -DwarningAsError=true Verification/HopfOctonions.lean
lake env lean -DwarningAsError=true Verification/HopfIntegrabilityBarrier.lean
lake env lean -DwarningAsError=true Verification/LamzouriMollifier.lean
lake env lean -DwarningAsError=true Verification/LamzouriMeasure.lean
lake env lean -DwarningAsError=true Verification/LamzouriOptimization.lean
lake env lean -DwarningAsError=true Verification/MasterSuite.lean
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env lean -DwarningAsError=true Verification/FinslerPolyMetric.lean
lake env lean -DwarningAsError=true Verification/FinslerMultilinear.lean
lake env lean -DwarningAsError=true Verification/FinslerIndicatrix.lean
lake env lean -DwarningAsError=true Verification/ProofGraphDAG.lean
lake env lean -DwarningAsError=true Verification/ProofGraphAcyclic.lean
lake env lean -DwarningAsError=true Verification/CryptoSPNInvariants.lean
lake env lean -DwarningAsError=true Verification/CryptoZKAir.lean
lake env lean -DwarningAsError=true Verification/SpinPhotonicWaveguide.lean
lake env lean -DwarningAsError=true Verification/SpintronicTransport.lean
lake env lean -DwarningAsError=true Verification/QuantumTransmonEngine.lean
lake env lean -DwarningAsError=true Verification/QuantumHeatEngine.lean
lake env lean -DwarningAsError=true Verification/AssetSettlement.lean
lake env lean -DwarningAsError=true Verification/DeFiAMMInvariants.lean
lake env lean -DwarningAsError=true Verification/PortfolioRiskEngine.lean
```

The module checks print:

```text
'CollatzBase.collatz_base_absorption' depends on axioms: [propext]
'CollatzAttractor.collatz_reaches_one_if_enters_compact' depends on axioms: [propext]
'CollatzCycles.no_period_two' depends on axioms: [propext, Quot.sound]
'CollatzCycles.trivial_cycle_one' does not depend on any axioms
'CollatzCycles.period_three_iff' depends on axioms: [propext, Quot.sound]
'CollatzParity.collatzIter_two_odd' depends on axioms: [propext, Quot.sound]
'CollatzParity.collatzIter_three_mod4_one' depends on axioms: [propext, Quot.sound]
'CollatzParity.odd_dyadic_partition' depends on axioms: [propext, Quot.sound]
'CollatzDyadicContract.collatzIter_three_strict_decrease' depends on axioms: [propext, Quot.sound]
'CollatzDyadicContract.collatzIter_five_mod8_three' depends on axioms: [propext, Quot.sound]
'CollatzDyadicContract.odd_mod8_partition' depends on axioms: [propext, Quot.sound]
'CollatzAverageDrift.collatzIter_four_mod8_five' depends on axioms: [propext, Quot.sound]
'CollatzAverageDrift.dyadic_measure8_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzAverageDrift.total_four_branch_weighted_drift_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzBranchSeven.collatzIter_seven_mod16_seven' depends on axioms: [propext, Quot.sound]
'CollatzBranchSeven.collatz_seven_reaches_one' depends on axioms: [propext, Quot.sound]
'CollatzBranchSeven.equal_weight_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzBranchFifteen.collatzIter_six_mod16_fifteen' depends on axioms: [propext, Quot.sound]
'CollatzBranchFifteen.collatz_fifteen_reaches_one' depends on axioms: [propext, Quot.sound]
'CollatzBranchFifteen.collatzIter_nine_mod32_fifteen' depends on axioms: [propext, Quot.sound]
'CollatzDyadicTree32.branch_unique' depends on axioms: [propext, Quot.sound]
'CollatzDyadicTree32.collatzIter_eight_mod32_thirtyone' depends on axioms: [propext, Quot.sound]
'CollatzDyadicTree32.collatz_thirtyone_reaches_one' depends on axioms: [propext, Quot.sound]
'CollatzDyadicTree32.full_weighted_sum_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzGeometricDrift.expected_pow3_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzGeometricDrift.expected_pow2_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzGeometricDrift.collatz_tree32_integer_drift_strict_contraction' depends on axioms: [propext]
'CollatzGeometricDrift.coefficient_product_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLogPotential.log_pow30_three_lt_log_pow49_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLogPotential.log_drift_gap_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzLogPotential.expected_log_drift_tree32_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzRemainderBound.expected_remainder_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzRemainderBound.remainder_uniform_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzRemainderBound.expected_perturbation_bound_at_five' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzRemainderBound.expected_perturbation_strict_upper_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'CollatzEffectiveDrift.log_drift_gap_algebraic_lower_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzEffectiveDrift.effective_drift_strictly_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzEffectiveDrift.collatz_finite_prefix_to_one' depends on axioms: [propext, Quot.sound]
'CollatzMarkovOperator.tree32_markov_drift_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzMarkovOperator.tree32_markov_drift_strictly_negative' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzMarkovOperator.collatz_positive_global_dichotomy' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzUnified.collatz_master_verification_suite' depends on axioms: [propext, Classical.choice, Quot.sound]
'CollatzDrift.foster_lyapunov_contraction_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannBounds.log_n_gt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannBounds.kappa_crit_explicit_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannMainTerm.mainTerm_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannMainTerm.mainTerm_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannMainTerm.kappa_crit_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannNumericBound.exp_four_lt_million' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannNumericBound.mainTerm_in_half_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannExplicitBound.kappa_crit_gt_sixty_three_over_128' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannExplicitBound.riemann_master_verification_suite' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfObstruction.singular_energy_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfObstruction.singular_energy_lower_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfObstruction.hopf_singular_obstruction_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfAlmostComplex.no_real_eigenvalues' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfAlmostComplex.nijenhuis_skew' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfAlmostComplex.nijenhuis_J_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfAlmostComplex.nijenhuis_J_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfIntegrabilityBarrier.obstruction_of_not_integrable' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfIntegrabilityBarrier.scaled_energy_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
'HopfIntegrabilityBarrier.hopf_master_verification_suite' depends on axioms: [propext, Classical.choice, Quot.sound]
'LamzouriMollifier.norm_functional_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'LamzouriMollifier.rayleigh_quotient_at_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'LamzouriMollifier.rayleigh_quotient_gt_threshold' depends on axioms: [propext, Classical.choice, Quot.sound]
'LamzouriMollifier.rayleigh_quotient_gt_seventy_three_percent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LamzouriOptimization.rayleigh_quotient_gt_threshold_on_interval' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'LamzouriOptimization.lamzouri_master_verification_suite' depends on axioms: [propext, Classical.choice, Quot.sound]
'MasterSuite.verification_master_registry' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The root module [`Verification.lean`](../Verification.lean) imports the complete
module chain, so `lake build --wfail` checks all sixty-two components, including the analytic and algebraic models, as part of the
normal project build. GitHub Actions runs the strict build and performs a
transitive audit of the project's axiom dependencies.

## Editors

```bash
code .
zed .
```

VS Code with the Lean 4 extension provides the full InfoView experience. Zed
provides syntax highlighting, snippets, and language-server diagnostics.

## Registry integration and verifier tooling update

DeFiConcentratedLiquidity, QuantumMajoranaChain and DistributedRaftConsensus
are now included in the registry. Their original limitations remain.
The standalone CLI and agent skill are described in
.

## Local Raft log append

`DistributedRaftLogAppend` reuses the existing Raft entry type and proves list
indexing, preservation of equal prefixes on identical append, and monotone terms
under an upper-bound assumption for the new term (or a last-entry bound for a
monotone log). This does not model AppendEntries RPC or distributed Log Matching.

## Pedersen scalar identities

`CryptoPedersenCommitment` proves linearity of `m*G + r*H`, a change of
opening for `H ≠ 0`, and a ratio identity extracted from a collision with
distinct messages. The model uses real scalars, not finite cryptographic groups.
No randomness distribution, perfect hiding, or computational binding is proved.
