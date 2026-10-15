---
id: CryptoBulletproofsWitnessExtraction
language: en
section: cryptography
source: Verification/CryptoBulletproofsWitnessExtraction.lean
source_sha256: 62a2e84c5959ae8f60dd5f6aaae7b6e201d16547ae300e13c37ba9a9bb7e849c
novelty: not-assessed
status: reviewed
---

# Local Bulletproofs witness extraction

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsWitnessExtraction.lean)

## Exact input and result

This module establishes a local algebraic extraction dichotomy for one IPA
folding step of arbitrary depth k: original vectors have length 2^(k+1),
folded vectors have length 2^k. Scalars are ZMod q for prime q. The group is
any additive commutative ZMod q module; generator independence is never assumed.

The expected Prefix contains U,G,H,P and the two messages L,R, all fixed before
branching. Four inputs contain that same prefix, challenges and folded witness
vectors a_i,b_i. Challenges are nonzero and their squares are pairwise distinct.
Accepts checks the actual module 158 folding equation:

    u_i^2*L + P + u_i^(-2)*R
      = IPA_target(U, fold_G(u_i), fold_H(u_i), a_i, b_i).

At arbitrary k these vectors must already have been extracted from the child
arguments. They are not inferred from the Boolean acceptance of four recursive
proofs. At k=0, accepts_last_step_iff_verifier proves the bridge to module 158's
actual one-round verifier. The independently supplied expected prefix prevents
coordinated replacement of all four input prefixes from silently changing the
statement being examined. Authentic storage of that expected context is external.

The result is a typed sum, not a predicate masquerading as executable evidence:

* witness: two original-length vectors wa,wb, with P=IPA_target(U,G,H,wa,wb);
* relation: vectors cg,ch and scalar cu, not all zero, with
  MSM(cg,G)+MSM(ch,H)+cu*U=0.

Only the original generators G,H,U occur in the relation. The target P and
round messages L,R are eliminated. No discrete logarithm hardness or binding
assumption is hidden in this algebraic result. A relation result need not imply
that no original witness exists; the branches are not a mutually exclusive
classification of all possible witnesses.

## Construction and proof

The first two folded answers recover a candidate via a two-point linear solve.
For example, wa_low=(u0*a0-u1*a1)/(u0^2-u1^2), and
wa_high=u0*a0-u0^2*wa_low, coordinate by coordinate. The b halves use the
opposite folding convention. reconstruct_fold proves agreement at the first
two challenges; reconstruct_honest_join proves exact recovery on honest folds.

Let s_i=u_i^2 and let e_i be the formal coefficient difference between the
observed folded target and the candidate's folded target. The first two e_i
vanish. Multiplying a target residual by s_i gives a group-valued quadratic
Rdiff+s_i*Pdiff+s_i^2*Ldiff. Three-point Lagrange interpolation eliminates these
three shared group elements using the fourth evaluation. The returned relation is

    lagrange(s2,s0,s1,s3)*s2*e2 - s3*e3.

relation_annihilates proves its evaluation is zero. If its formal coefficient
vector is zero, the G/H low/high coordinates and s2!=s3 force both remaining
responses to equal the candidate folds. Three distinct evaluations then force
Pdiff=0. This proves zero_relation_witness and ipa_extraction_dichotomy.
The returned coefficients are computed from responses; no search over witnesses
or nonconstructive choice of a group relation is used.

extract_ipa_witness checks the prefix, nonzero challenges, distinct squares and
all four response equations, in that order. Errors are prefixMismatch,
zeroChallenge, repeatedSquare and invalidResponse. extract_ipa_witness_sound
proves every successful output satisfies ResultValid. extract_unit_transcripts
proves successful execution under those input conditions. Symmetric challenges
u,-u are rejected because their squares coincide. All arithmetic is exact.

## Quadratic interpolation

vandermonde_matrix uses rows (1,x_i,x_i^2). Its determinant is
(x1-x0)*(x2-x0)*(x2-x1); it is nonzero for three pairwise distinct challenges.
Both matrix inverse identities are proved. interpolate_quad is an executable
Lagrange formula; interpolate_quad_evaluates proves it interpolates arbitrary
three values, polynomial_interpolation_quad recovers any quadratic's coefficients,
and interpolate_eq_inverse proves agreement with inverse-matrix multiplication.
These analytical statements hold over arbitrary fields. The executable extractor
uses prime finite fields. Division by zero outside distinct-input hypotheses is
not an interpolation guarantee; the IPA wrapper checks its own nondegeneracy.

range_polynomial_interpolation recovers module 159's actual t0,t1,t2 from three
evaluations of its l/r inner product. This is not a proof of bitness, a recovery
of Pedersen openings from group elements alone, or full range knowledge soundness.
The separate formal-polynomial bit constraints remain necessary.

## Validation and Clean Water

The suite includes the generic local extraction theorem, checked-interface
soundness, determinant and interpolation results, and concrete success/relation
examples over ZMod 101 with nonzero generators. The regression file exercises
original widths 2,4,8, shared-prefix checks, repeated/symmetric/zero challenges,
changed L,R,U,G,H, corrupted responses, coefficient recovery and a singular
Vandermonde example. A nontrivial relation branch has all four group equations
accepted. Reordering a valid honest input family is also tested.

This closes the local algebraic step only. Recursive extraction of a complete
range witness, construction and availability of a transcript tree, probabilistic
forking bounds, extractor running-time bounds, computational binding/discrete-log
reductions, HVZK, Fiat-Shamir/ROM and noninteractive extraction remain open.
No post-hoc extraction from independent completed proofs is claimed. Concrete
curve implementations, serialization and random generation are outside scope.
Tendermint accountable safety still needs its observation/justification contract;
Python, JSON/SHA-256 and SimLab correspondence obligations remain open.
Allowed kernel axioms: propext, Classical.choice, Quot.sound. Novelty not assessed.

Reference baseline: 530d758583c27e9ed8ef3b6bd2f5298c28ed20d0.
Measured checks are recorded in tools/validation_snapshot.json after validation.
Reference: [Bünz et al., Bulletproofs](https://eprint.iacr.org/2017/1066).
