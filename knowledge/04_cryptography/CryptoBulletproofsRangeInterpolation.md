---
id: CryptoBulletproofsRangeInterpolation
language: en
section: cryptography
source: Verification/CryptoBulletproofsRangeInterpolation.lean
source_sha256: 7e8e0bf03238d916c1a7eda2eeefec0b217e386909a993bd660268f2d091a8ac
novelty: not-assessed
status: reviewed
---

# Bulletproofs range constraints from a finite interpolation grid

[Section](../cryptography/README.md) · [Lean](../../Verification/CryptoBulletproofsRangeInterpolation.lean)

## Contract

For prime q, n ≥ 1, FIXED a,b : Fin n → ZMod q and v : ZMod q, let
 y : Fin n → ZMod q and z : Fin 3 → ZMod q both be injective. Pointwise
 t0 a b (y i) (z j) = (z j)^2 * v + delta_fn (y i) (z j) n at every grid
 node implies formal_t0 a b = formal_rhs v n. The witness vectors do not
 vary between nodes; consistency of independently extracted vectors is not assumed
 to follow from interpolation.

The residual is exactly

F(Y,Z) = sum_i a_i*b_i*Y^i + Z*sum_i (a_i-b_i-1)*Y^i
         + Z^2*(sum_i 2^i*a_i-v).

The module reuses t0_residual and formal_residual. Cubic Z terms cancel; the
quadratic term remains. residual_poly_eval connects the nested polynomial with
its scalar evaluation. residual_poly_degree_Z bounds the outer Z degree by two;
residual_poly_degree_Y bounds the Y degree of every Z coefficient by n-1.
NatDegree treats the zero polynomial as degree zero. These bounds imply the
stated bidegree bounds for n ≥ 1.

poly_coeff_zero_of_injective_grid uses the deterministic bound on the number of
roots. quadratic_zero_of_three_points applies it to three coefficients. No
Schwartz–Zippel probability or generator assumption is used. grid_card_bounds
shows n ≤ q and 3 ≤ q from the injective grids. Zero nodes are allowed; distinct
squares are not required (unlike the separate IPA extractor).

grid_equalities_imply_formal_identity proves the main implication.
grid_equalities_imply_field_range reuses formal_coefficients_imply_range to obtain
 a_i*b_i=0, a_i-b_i=1, a_i*(a_i-1)=0 and sum_i 2^i*a_i=v.
The field has no zero divisors, so these imply each a_i is 0 or 1.
grid_equalities_imply_natural_range reuses formal_identity_natural_range:
for a natural v with v<q and 2^n<q, the result is v<2^n.
grid_reconstructed_value_eq also proves that the natural bit reconstruction is
exactly v. Field equality alone cannot distinguish v from v+q.

## Executable interface and regressions

verify_interpolation_grid checks supplied vectors, not unknown openings. It
returns Except GridError Unit, rejecting n=0, repeated Y, repeated Z, or a failed
grid equality, in that order. verify_grid_success_iff precisely characterizes
success; verify_grid_sound gives its formal identity; honest_grid_complete proves
success for honest bits and their represented field value.

Kernel and executable regressions use q=101, n=1,2,4 (values 1,3,5), exact natural
reconstruction, zero nodes, reordered grids, symmetric but distinct Z nodes,
corrupted right vectors and values, and the empty-vector rejection. The n=1
counterexample a=b=0,v=-1 has residual Z^2-Z: two distinct Z points pass, but the
formal identity fails. The n=2 example a=[2,0], b=[0,0], v=2 has residual Z*(1-Y):
all Z equations pass at repeated Y=1 although a[0] is not a bit. Repeated Z=0,1,1
also passes the bad pointwise equations and is rejected by the wrapper.
A noncanonical natural value 106 passes the field check for bits representing 5
but lies outside [0,16); this illustrates the necessity of the natural hypotheses.

## Clean Water

This is a deterministic algebraic implication for already supplied fixed
witnesses and a grid checker. It is NOT full witness extraction from transcripts.
Openings of A,S, interpolation in X, cross-branch witness consistency, and linkage
to the IPA tree extractor remain separate obligations. No independence of cyclic
group generators, security reduction, rewinding bound, HVZK or Fiat–Shamir/ROM
claim is added. Tendermint accountable safety, Python implementation equivalence,
JSON/SHA-256 bridges and SimLab applicability remain open in their stated scopes.

## Validation and provenance

Public Z release v0.5.74. The last fully validated public baseline is
b3410720b9af49c2fb70d15d65d3d012091cbf0b (v0.5.73). The private export snapshot is
f5bac6750f7d5c9b741041ac86d213d9ca1474c0. Checks run in the public tree are recorded
in [the release report](../../docs/release-v0.5.74.en.md); private-tree evidence
is not substituted for public validation. Allowed axioms remain propext,
Classical.choice and Quot.sound. Mathematical novelty is not assessed.
