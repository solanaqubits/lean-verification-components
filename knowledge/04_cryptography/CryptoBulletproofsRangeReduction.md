---
id: CryptoBulletproofsRangeReduction
language: en
section: cryptography
source: Verification/CryptoBulletproofsRangeReduction.lean
source_sha256: 96c22d66df01a451bc1ad7c231b1417997441cf57cd26b2907fd297af5a81888
novelty: not-assessed
status: reviewed
---

# Bulletproofs algebraic range reduction

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsRangeReduction.lean)

## Model and exact scope

The executable protocol uses n=2^k coordinates over the prime field ZMod q and
an additive commutative group with a ZMod q module structure. Thus it specializes
to cyclic prime-order groups without an independence assumption on generators.
The suite includes the existing satisfiable cyclic model over ZMod q. This model
is an algebraic consistency witness, not a cryptographically hard group.
The actual vector commitment import is CryptoCommitmentVectorPedersenGroup.

Natural range witnesses satisfy v < 2^n. `natural_bits` directly reuses module 156.
`boolean_iff_product_zero` identifies field bits with a*(a-1)=0. Field equations
alone do not identify a natural integer with its canonical residue: the reverse
natural-range theorem requires both v < q and 2^n < q. Honest algebraic completeness
holds without those stronger injectivity bounds; it is not a binding theorem.

## Scalar and formal polynomial identities

`l_poly a s z x` is a-z+x*s and `r_poly b t y z x` is
(y^i*(b_i+z+x*t_i)+z^2*2^i)_i. `poly_inner_product_eq` proves the exact quadratic
expansion with explicit t0, t1 and t2, over any commutative ring.
`t0_spec` proves t0=z^2*v+delta_fn y z n, given b=a-1, a_i*b_i=0,
and the weighted field decomposition of v.

`formal_t0` lives in Polynomial (Polynomial F), with inner variable Y and outer Z.
`formal_residual` exposes the Z^0, Z^1 and Z^2 coefficients. Extracting the Y^i
coefficients gives a_i*b_i=0 and b_i=a_i-1; the Z^2 coefficient gives the value.
`formal_identity_iff` is an actual equivalence over every field, with no cardinality
assumption on a sample of challenges. `formal_curve` adds the independent outer
variable X. `formal_three_variable_iff` proves equivalence for the complete
three-variable polynomial identity, including arbitrary masking vectors.
Only this symbolic layer is noncomputable; the prover and verifier are executable.
`formal_identity_natural_range` lifts the recovered bits to naturals with the
explicit representative and no-wrap hypotheses.

## Public verification and the corrected IPA target

Public generators are scalar B, blinding Hblind, IPA U and vectors G,H.
V=v*B+gamma*Hblind; A and S commit to (a,a-1) and (s,t), with blindings alpha,rho.
T1=t1*B+tau1*Hblind and T2=t2*B+tau2*Hblind. The transmitted scalars are
 t_x=<l(x),r(x)>, tau_x=z^2*gamma+x*tau1+x^2*tau2, mu=alpha+x*rho.
The verifier checks
 t_x*B+tau_x*Hblind = z^2*V+delta*B+x*T1+x^2*T2.
`polynomial_commitment_equation` proves this equality for honest witnesses.

For y != 0, H'_i=(y^-1)^i*H_i. `scaled_generators_valid` proves y^i*H'_i=H_i.
The precise public IPA target is
 P = A+x*S-z*sum(G_i)+sum((z*y^i+z^2*2^i)*H'_i)-mu*Hblind+t_x*U.
The subtraction removes vector-commitment blindings and the last term supplies
the actual inner product. Replacing that last term by delta*U and omitting
-mu*Hblind, as in the initial prose formula, does not yield the IPA relation.
`range_ipa_target_invariant` proves the corrected equality directly.

`RangeReductionTranscript` contains A,S,T1,T2,t_x,tau_x,mu and module 158's IPA
transcript. Challenges y,z,x and the IPA unit challenges are external verifier
inputs. No witness or desired verification equality is stored in the transcript.
`range_prover` computes the messages and calls the existing recursive IPA prover.
`verify_range_reduction` checks y != 0, the commitment equation and the existing
IPA verifier. `range_proof_composition_completeness` and `natural_range_completeness`
prove acceptance. First A,S messages are independent of y,z,x and IPA challenges;
T1,T2 are independent of x and IPA challenges. No probabilistic generation or
network execution is formalized.

## Regressions and validation

Kernel checks and compiled executions cover n=1,2,4, values 0 and 2^n-1,
nontrivial scaling challenges, zero-y rejection, no n-bit natural representation
of 2^n, formal polynomial equivalence, and concrete corruptions of t_x,mu,T1 and IPA.
A ZMod 17 example with a=2,b=1,y=1,z=2,v=11 satisfies the evaluated t0 equation
but violates bitness and the formal identity. Thus an evaluated equality is not
silently promoted to an unconditional range certificate.
Corruption examples are specific parameters, not rejection of every alteration
under arbitrary dependent generators.

Validation evidence is recorded in tools/validation_snapshot.json and the
validation record. Allowed axioms: propext, Classical.choice, Quot.sound.
No native-decide proof shortcut or user axiom is used.

## Clean Water

Proved: quadratic expansion, constant-term identity, formal coefficient
characterization of bit and value constraints, canonical natural-range recovery,
correct public commitment/IPA target equations, and honest composition completeness.
This does not establish knowledge extraction from accepted transcripts, special
soundness, computational binding, zero knowledge/HVZK, Fiat-Shamir/ROM security,
concrete curves, serialization, or aggregation of multiple range claims.
Masks are algebraic inputs; their presence is not a proof of zero knowledge.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Scientific novelty is not assessed.

Sources: [Bünz et al., Bulletproofs](https://eprint.iacr.org/2017/1066) and
[Dalek range-proof derivation](https://doc-internal.dalek.rs/bulletproofs/notes/range_proof/index.html).

[`poly_inner_product_eq`](../../Verification/CryptoBulletproofsRangeReduction.lean#L34) · [`t0_spec`](../../Verification/CryptoBulletproofsRangeReduction.lean#L61) · [`formal_three_variable_iff`](../../Verification/CryptoBulletproofsRangeReduction.lean#L155) · [`formal_identity_natural_range`](../../Verification/CryptoBulletproofsRangeReduction.lean#L183) · [`range_ipa_target_invariant`](../../Verification/CryptoBulletproofsRangeReduction.lean#L232) · [`range_proof_composition_completeness`](../../Verification/CryptoBulletproofsRangeReduction.lean#L296) · [`verification_suite`](../../Verification/CryptoBulletproofsRangeReduction.lean#L375)
