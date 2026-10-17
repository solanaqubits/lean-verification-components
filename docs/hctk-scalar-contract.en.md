# HCTK scalar partition contract 1.0.0 (ε201)

Parent: quantum-physics / hctk-scalar-partition. Public release v0.7.10 refines
the formal scalar model. Numerical studies and artifacts are outside this release.

## Normative mathematical scope

Real parameters c,G,hbar,kB,tau,R are strictly positive; chi and Q are real.
The scalar functions are exp(chi)/tau, G*Q/(c^2*R),
hbar*c^3/(8*pi*G*M*kB) for M>0, and
2*pi*E*R/(hbar*c*log(2)) for E>=0. Prove positivity under the stated signs and
linear/inverse scaling identities. These define functions; they do not derive
Hawking radiation, an entropy bound or a Casimir interaction from physical laws.
Q is a scalar: G*Q/(c^2*R) is dimensionless only if Q has mass units. The user's
proposed topological-charge interpretation supplies no such unit identification.

State fields: localAmount : Real, reservoirAmount : Real, label : Int.
For prescribed total Q, fraction p and integer n, partition(Q,p,n) is
(Q*p,Q*(1-p),n). Prove the sum, endpoints, nonnegative components when Q>=0
and 0<=p<=1, and monotonicity at fixed Q. Prove preservation under the explicit
transition (l,r,n) -> (l-d,r+d,n), including finite lists of transitions.
Nonnegative states are preserved only for 0<=d<=l. The label is copied by the
transition; it is NOT computed as a Chern number of a bundle or Hamiltonian.
No theorem assumes conservation itself as a hypothesis merely to repackage it.

Define regularizedWindow(tau,eps,p)=tau/(p+eps). For tau>0,eps>0,p>=0
prove positivity and upper bound tau/eps, attained at p=0. Prove antitonicity
in p. At fixed eps the model cannot diverge. For the separate ideal expression
tau/p (p>0), show arbitrarily large values as p becomes small and positive.
Real division at zero is totalized in Lean: it is outside the ideal physical
formula's admissible domain and is never used as an infinite value.

## Numerical and physical boundaries

The Python smooth shutdown and Gaussian profile are imposed curves, not solutions
of a Hamiltonian, quantum channel or phase-transition equation. 3000 J is an
input amplitude, not derived Landauer heat. A Chern invariant would require an
appropriate geometric/spectral definition and gap-preservation hypotheses.
No transfer to a vacuum, soul, consciousness, detector capability, resonator
stability, or engineering feasibility is claimed. NumPy agreement is tested,
not a formal IEEE-754 refinement of Real arithmetic.

## Required regressions

Exact endpoints, an interior rational split, nonzero transfer and finite trace;
invalid negative transfer/range examples; label distinct from real-valued scalar;
regularized endpoint/cap and ideal positive-domain examples; positive scalar
formulas and scaling. Separate one-sided loss counterexample shows conservation
is not automatic for arbitrary transitions. Tests must apply actual definitions.

## Sources and applicability

- Bekenstein, authored review: https://www.scholarpedia.org/article/Bekenstein_bound
- Hawking radiation review: https://www.scholarpedia.org/article/Hawking_radiation
- Bérut et al., experiment: https://www.nature.com/articles/nature10872

These support the established formula contexts, not the proposed HCTK mechanism.

## Integration note

The mathematical requirements above are unchanged. The master suite packages existing
algebraic statements only; it adds no physical or topological guarantee. See
[release v0.7.10](release-v0.7.10.en.md) for public verification scope.

## Capture refinement (existing epsilon201, no new module)

The three-store explicit update is (b,c,v,n)->(b-d,c+eta*d,v+(1-eta)*d,n).
Conservation is derived algebraically for arbitrary reals. Nonnegativity requires
initial nonnegativity,0<=d<=b and0<=eta<=1 at each actual step. No premise assumes
final conservation or an arbitrary final label equality. Finite-trace induction
is packaged by capture_trace_contract. collapse_runCaptures proves exact agreement
with runTransfers after aggregating c+v. No claim of a physical carrier, decoded
information, phase-conjugation mechanism or topological Chern invariant follows.
This is a distinct explicit model from the original independently prescribed
Gaussian/tanh profiles; their previous counterexamples/results are retained.
