---
id: CryptoBulletproofsAggregation
language: en
section: cryptography
source: Verification/CryptoBulletproofsAggregation.lean
source_sha256: a45f9859bae8bcd8fe9b8a8b36f599a473f61694a4e81574910913d437ea66ee
novelty: not-assessed
status: reviewed
---

# Bulletproofs aggregation of range witnesses

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsAggregation.lean)

## Dimensions and algebra

The protocol uses n=2^a bits per value, m=2^b values and N=mn=2^(a+b).
There is no padding or empty party list. `Block m n` indexes (j,i);
`global_index` is j*n+i. `block_equiv` and `flatten` connect the block vectors
to the existing executable IPA on Fin (2^(a+b)). Sum, dot-product and MSM
reindexing are proved. The scalar algebra works over commutative rings and
formal coefficient recovery over fields. The executable protocol specializes
to ZMod q for prime q and an additive commutative group with a ZMod q module
structure. No unconditional generator independence is assumed.

The block weight is w_(j,i)=z^(j+2)*2^i, with global y exponent j*n+i.
All z weights are powers of the same challenge, not independent random weights.
The two curves are l=u-z+x*s and r=y^global_index*(v+z+x*t)+w.
The exact quadratic expansion has coefficients agg_t0, agg_t1, agg_t2.
For v=u-1, u*v=0 and block_value(u,j)=values_j, the constant term is

    t0 = sum_j z^(j+2)*values_j + delta(m,n,y,z)
    delta = (z-z^2)*sum_(r<N) y^r - sum_j z^(j+3)*sum_(i<n) 2^i.

`agg_t0_residual` exposes all constraint errors. At formal Z degrees 0 and 1,
extracting the unique Y^(j*n+i) coefficients recovers bitness and v=u-1.
The remaining Z^(j+2) coefficients recover each block's value.
`agg_formal_identity_iff` proves the equivalence for formal Y,Z polynomials;
`agg_three_variable_iff` adds the independent formal curve variable X.
No finite-field sampling hypothesis replaces polynomial identity.

Natural completeness chooses each value's bits using module 156 and proves
acceptance for every values_j < 2^n. The reverse theorem
`agg_formal_natural_range` explicitly requires values_j < q and 2^n < q.
The stronger injectivity assumptions are unnecessary for honest algebraic
completeness. There is no requirement that 2^N < q.

## Commitments, composition and compatibility

`AggGenerators` contains scalar B, Hblind, U and block-indexed G,H.
V_j=values_j*B+gamma_j*Hblind. The prover constructs A,S,T1,T2 and

    t_x = <l(x),r(x)>
    tau_x = sum_j z^(j+2)*gamma_j + x*tau1 + x^2*tau2
    mu = alpha + x*rho.

`agg_polynomial_commitment_equation` proves

    t_x*B + tau_x*Hblind = sum_j z^(j+2)*V_j + delta*B + x*T1 + x^2*T2.

For y!=0, H'_r=(y^-1)^global_index(r)*H_r. The corrected public IPA target is

    P = A+x*S-z*sum G_r + sum (z*y^global_index(r)+w_r)*H'_r
        - mu*Hblind + t_x*U.

`agg_target_invariant` proves equality with the IPA relation for flattened l,r.
`agg_prover` calls module 158's actual recursive prover; `verify_aggregation`
checks y!=0, the commitment equation and that module's verifier. Witnesses are
not stored in a transcript and acceptance is not postulated.
`agg_completeness` and `agg_natural_completeness` establish honest acceptance.
A,S are independent of later challenges; T1,T2 depend on y,z but not x or IPA
challenges, as recorded by the message-order theorems.
Verifier challenges are external inputs. IPA challenges use units, excluding
zero. As in module 159, algebraic completeness permits x=0 and z=0; no soundness
claim is inferred from these degenerate evaluations. y=0 is rejected.

At m=1, delta, curves and t0 reduce to the existing single-range formulas.
`agg_verifier_m1_spec` proves equality with module 159's verifier after the
explicit generator reindexing. Existing module interfaces remain unchanged.

## Exact message counts

The inner IPA has exactly a+b rounds, 2(a+b) group elements and two scalars.
The proof body (`AggregatedRangeProof`, reusing the single-range transcript
shape) adds A,S,T1,T2 and t_x,tau_x,mu: 4+2(a+b) group elements and five scalars.
`AggregatedEnvelope` additionally includes the m public commitments V_j, for
m+4+2(a+b) group elements. Public generators and verifier challenges are counted
separately. Thus the envelope including V_j is not logarithmic in m.
A logarithmic IPA message size does not assert logarithmic verifier work or
serialized byte size. Counting the payload lists is proved in Lean.

## Regressions and Clean Water

Kernel checks and compiled executions cover m,n in {1,2,4}, zero, maximum and
mixed bit patterns, canonical natural recovery, formal equivalence, the m=1
bridge, exact payload sizes, global indexing, and rejection of y=0. Specific
nondegenerate examples reject altered T1,T2,t_x and mu. Wrong block weights
change the tested relation. A concrete nonboolean example passes a single
scalar evaluation but fails the formal identity. There is no n-bit natural
representation for 2^n.

Proved: algebraic block reduction, formal coefficient characterization, natural
range recovery under explicit bounds, correct public target/commitment equations,
honest composition and exact payload sizes. This does not prove witness extraction,
special soundness, computational binding, HVZK, Fiat-Shamir/ROM security,
or post-hoc compression of independent completed proofs without witnesses.
Masks are algebraic inputs; their presence is not a zero-knowledge proof.
The batch verifier from module 160 is imported but its independent-weight error
bound is not transferred to the correlated z powers used here. Concrete curves,
serialization, randomness generation and protocol-level MPC are outside scope.
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Allowed axioms: propext, Classical.choice and Quot.sound. Novelty is not assessed.

Source baseline: 22f869e47aa9b9d9703bee7520b3798e693f6b15.
Measured validation is recorded in the project validation snapshot.
References: [Bünz et al.](https://eprint.iacr.org/2017/1066),
[Dalek range-proof derivation](https://doc-internal.dalek.rs/bulletproofs/notes/range_proof/index.html).
