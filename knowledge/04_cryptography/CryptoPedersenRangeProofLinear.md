---
id: CryptoPedersenRangeProofLinear
language: en
section: cryptography
source: Verification/CryptoPedersenRangeProofLinear.lean
source_sha256: a04a003f57ab4fd2684f683a1e97d1c71b6134cbe5997531ca6336bd1be763f6
novelty: not-assessed
status: reviewed
---

# Linear interactive Pedersen range proofs

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoPedersenRangeProofLinear.lean)

## Model and statement

The reused Pedersen setup is a finite additive commutative group of prime order q,
a module over ZMod q, with two nonzero generators g and h. They need not be distinct
or linearly independent. The scalar model over ZMod q witnesses consistency; it is
not a hard discrete-logarithm instance.

`nat_bit_decomp_iff` proves the equivalence between v < 2^m and an m-coordinate
natural vector with entries at most one and weighted sum v. `nat_bool_decomp_iff`
provides Boolean witnesses. `bitValue_cast` transfers the identity to ZMod q.
`range_cast_injective` uses 2^m < q to recover equality of bounded natural values
from equality of their residues. Algebraic completeness/extraction themselves
hold more generally; the non-wrapping range interpretation uses this bound.
Probabilistic range theorems use m = n+1, hence at least one bit.

## Protocol and extraction

Each bit commitment is b_i*g + r_i*h, with weights 2^i. The aggregate must equal
the public commitment C. For each bit, ORVerify checks e0+e1=e and
z0*h=a0+e0*C_i, z1*h=a1+e1*(C_i-g). Every bit proof uses the same total challenge e.
The honest prover simulates the false branch and answers the true branch with its
nonce. `or_first_message_independent` and `range_first_message_independent` prove
that first messages do not depend on the subsequent challenge.

`extractBit` selects a branch with a changed branch challenge and reuses Schnorr's
special-soundness theorem with generator h. `SameFirst` requires equality of all
bit commitments and both branch messages for every bit. With two accepted full
transcripts and distinct total challenges, `range_proof_extract_witness` proves
that the computed natural value is below 2^m and the computed weighted blinding
opens C. This is a constructive two-transcript extraction identity. A full
probabilistic adversary/rewinding runtime theorem is not claimed.

`range_completeness_for_opening` applies to any natural value in range and every
blinding of the original commitment. It does not change the public statement to
fit sampled bit commitments. The scalar/vector bridge reuses the one-coordinate
vector commitment definition from CryptoCommitmentVectorPedersenGroup.

## Full joint honest-verifier zero knowledge

Bit blindings are sampled uniformly subject to their weighted sum equaling the
fixed original blinding r (`OpeningFiber`). `openingTailEquiv` realizes this by
sampling n free scalars and solving the coefficient-one coordinate. It is not a
model of independent unconstrained blindings for a fixed C.

The simulator takes only setup, C and the challenge. `commitmentTailEquiv` samples
n free group elements and sets the first commitment to C minus the weighted tail.
It then samples OR branch challenges/responses. `fiberEquiv`, used only in the
proof, transports the real constrained blinding distribution to the public
commitment distribution. The simulator does not invoke its discrete-log inverse.

`range_proof_hvzk_sim_eq_dist` proves equality of the full transcript PMFs, including
bit commitments, both branch messages, challenge splits and responses. The proof
also includes conditional vector OR distributions and each single-bit OR law.
`range_hvzk_independent_challenge` covers arbitrary independently sampled challenge
PMFs and explicitly models real coins sampled before the challenge. This is perfect
special HVZK and honest-verifier interaction, not malicious-verifier zero knowledge.
Uniform finite sampling is a mathematical PMF model, not a verified RNG or runtime.

## Binding boundary and regressions

`pedersen_binding_violation_extracts_dlog` derives g=((r'-r)/(v-v'))*h from two
openings with unequal field messages. Bounded natural messages can use the cast
injectivity theorem. No unconditional equality with a previously supplied opening
is inferred. Computational binding requires a separate DLOG hardness model.
Known generator relations explicitly allow alternate openings.

Regressions cover one bit, zero and maximal range values, exclusion of 2^m,
tampered aggregates, both honest bit branches, two-challenge extraction, correlated
blinding sampling, public simulation and alternate openings. For equal challenges,
a concrete accepted transcript refutes the extraction formula's conclusion;
it does not assert that the commitment has no range opening.

## Clean Water

The suite includes natural bit ranges, completeness for fixed openings, full
transcript extraction, full joint HVZK, challenge ordering, simulator acceptance,
collision reduction and a satisfiable group model. Integration uses CryptoFullSuite
in MasterSuiteComponents. Module verify/audit, strict build, full verifier, live
tests, registry and independent axiom audits are recorded in validation_snapshot.

Fiat-Shamir/ROM, malicious verifiers, concrete elliptic curves, byte serialization,
computational DLOG hardness and extraction complexity against arbitrary provers
are outside the model. Python, JSON/SHA-256 and SimLab correspondence obligations
remain open. No scientific priority is asserted.

Reference: [Damgård, On Sigma-protocols](https://cs.au.dk/~ivan/Sigma.pdf), including
Schnorr identification, special soundness, special HVZK and OR composition.
