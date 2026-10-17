---
id: CryptoBulletproofsRangeWitnessExtraction
language: en
section: cryptography
source: Verification/CryptoBulletproofsRangeWitnessExtraction.lean
source_sha256: 189ed377a73ff305f54f63a742f8345ec548356305aa42ed81543b9eea4d74e5
novelty: not-assessed
status: reviewed
---

# Conditional Bulletproofs range extraction from certified openings

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsRangeWitnessExtraction.lean)

## Inputs and scope

For prime q and n = 2^k, OpeningCertificate supplies vectors a,b,s,t and scalars
alpha,rho,v,gamma. ValidOpenings checks the actual common commitments A,S,V.
No bit, range or cross-branch witness agreement is assumed. The abstract group
is an additive ZMod q module; no global independence of its generators is assumed.

TranscriptFamily fixes T1,T2 separately for each Y,Z pair, before the three X
responses. ValidFamily checks the value-commitment equations and accepting IPA
trees against roots computed by branch_statement using range_target. Thus the
root is tied to A,S and the actual responses, not to a supplied range witness.
Y has n distinct nonzero nodes, Z has three distinct nodes, and X has three
distinct nodes for each Y,Z pair. The IPA trees separately require nonzero
challenges with four distinct squares at each internal node. Zero Y is forbidden
here because scaled_H uses its inverse; the isolated interpolation module 176
allows zero Y. X and Z need not be nonzero merely for interpolation.

## Constructive composition

local_coeff calls extractTree from module 170. A returned tree relation is lifted
from (G,scaled_H H y,U) to the ORIGINAL (G,H,B,Hblind,U). lift_scaled_eval preserves
the group value and lift_scaled_zero_iff preserves nontriviality when y is nonzero.
For a returned vector witness, discrepancy subtracts l_poly and r_poly derived
from the common certified openings. The blinding coefficient is mu-alpha-x*rho;
the U coefficient is dot(l,r)-tx. discrepancy_annihilates proves this entire
combination is zero using equality of the commitment openings.

A nonzero coefficient tuple is an explicit relation. If it is zero,
discrepancy_zero_iff gives vector agreement, the correct blinding response and
the inner-product response. For each Y,Z pair, group_constant_zero uses the
three X points and module 169's quadratic module interpolation to eliminate
T1,T2. grid_coeff then has only B and Hblind components:

* B: t0 - z^2*v - delta_fn y z n;
* Hblind: the constant coefficient interpolated from taux, minus z^2*gamma.

If these coefficients vanish at every grid node, module 176 supplies the formal
range identity, bits, b=a-1 and the natural range. extraction_soundness proves
ResultValid for extract: either a RangeWitness opening the original V, or a
nonzero RelationCoefficients tuple whose relation_eval is zero. The successful
witness includes v.val < 2^n, exact natural reconstruction from a, and gamma.
The explicit no-wrap assumption is 2^n < q. The canonical representative is
already less than q. No computational hardness claim follows from this algebraic
alternative.

## Checked interface and regressions

checked_extract requires decidable group equality and rejects, in order, k<1,
2^n>=q, invalid openings and invalid families. checked_extract_success_iff states
its exact acceptance conditions; checked_extract_sound proves the output
contract. The lower-level theorem also permits k=0. Extraction scans a finite
list of actual tree discrepancies followed by grid discrepancies; it returns
the first nonzero tuple, or the range witness. An invalid opening is rejected,
whereas a valid family over dependent generators may return a relation.

Kernel regressions and 17 executable scenarios over ZMod 101 cover n=2,v=3,
nonzero masks, a valid non-bit certificate yielding 3*B-3*Hblind=0, and an
alternative accepting IPA witness yielding G[0]-G[1]=0. They also cover invalid
A/S/V openings, repeated Y/Z/X, zero Y, changed tx/mu, a substituted tree root,
zero IPA challenges and equal squared IPA challenges. A depth-two tree from
module 170 exercises a genuine tree relation and its nontrivial lift to the
original basis with y=2. These dependent-generator fixtures demonstrate the
algebraic branches; they are not cryptographically secure parameter generation.

## Clean Water

This is conditional algebraic composition with supplied openings of A,S,V.
Obtaining those openings from a prover remains open even before byte parsing.
There is no full protocol knowledge-extraction theorem, rewinding/forking or
expected-time bound, computational binding reduction, HVZK proof, Fiat–Shamir/ROM
security proof, or deployed-byte equivalence here. The remaining Bulletproofs
protocol obligations are not closed by the composition theorem. Tendermint
accountable safety, Python equivalence, JSON/SHA-256 and SimLab obligations
remain separate. Mathematical novelty is not assessed.

## Public gamma validation provenance

Public gamma release v0.5.76 (formerly level Z) exports private snapshot
26ae7e5b13c3e646cb7bcfc42109fbc70f421903. The previous public scoped release is
39553b505bd256279c36c38900d8dd0d19b48d9b (v0.5.75). The last fully validated PUBLIC
baseline remains b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73).
Public-tree checks are recorded in [the release report](../../docs/release-v0.5.76.en.md).
Private evidence is not substituted for public validation; no new full-project
verify-all or full unittest result is claimed. The permitted axioms remain
propext, Classical.choice and Quot.sound.

[Module 193](CryptoPedersenCommitmentOpeningExtractionContract.md) constructs opening certificates from additional accepting representation-protocol forks. Obtaining those forks from the original Bulletproofs transcript remains an open obligation.
