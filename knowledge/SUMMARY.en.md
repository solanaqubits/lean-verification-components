# Results and practical value

[Knowledge base](README.md)

This project collects reusable, machine-checked components and the tooling needed
to keep their proofs, assumptions, and documentation connected. The validated
snapshot contains 127 subject modules across ten areas, plus a registry and axiom
auditor. See the [validation record](VERIFICATION.en.md) for counts and evidence.

## What has been achieved

- Explicit definitions and theorem statements replace informal claims with checkable obligations.
- Algebraic and finite results cover coefficient bounds, matrix identities, commitment equations, reserve and balance invariants, and quorum intersections.
- A central theorem collects selected guarantees while preserving their hypotheses.
- A CLI supports strict compilation, dependency auditing, controlled integration, and draft knowledge cards.
- English cards record what each model covers and what remains unformalized.

## Why it is useful

The components can support larger proofs without repeating the same arithmetic or
algebra. They make assumptions visible, expose mistakes in proposed arguments,
and provide a reproducible way to detect regressions. Their value is the precise,
checked statements and reusable development process.

For example, the Collatz branch coefficients have arithmetic mean 639/512 > 1,
while a related geometric product is below one. Keeping those distinct prevents
an invalid global-contraction inference. The Pedersen module checks real scalar
identities while explicitly leaving probabilistic hiding and computational binding
outside its scope. The operational Raft module proves election safety from reachable message-passing
states. The network-induction module now derives global Log Matching and historical entry/message provenance from those transitions. The complete-bridge module derives Leader Completeness and retention of prefixes already held by a replica from actual commit events in the unchanged operational automaton; it does not assume abstract VoterEvolution.

## Novelty and remaining work

Formalizing a known identity is different from discovering a new theorem.
First-formalization claims also require comparison with existing libraries and
literature. No such priority claim is established here.

The next substantive steps are stronger models, links between abstractions and
implementations, documented comparisons with prior formalizations, and integration
with standard reusable Mathlib abstractions where appropriate. Compilation alone
does not close those gaps or establish production protocol security.


## Finite-field batch counting and conditional noise optimization

`CryptoSchnorrBatchVerification` proves exact accepting counts and rational
fractions for a fixed nonzero discrepancy over `ZMod q`, with prime `q`.
There are `q^(n-1)` accepting vectors out of `q^n`, giving `1/q`;
full Cartesian products give `(1/q)^k` for repeated checks. Coefficients include
zero. The interpretation as independent uniform sampling does not formalize a
sampler or an adversarial security game. EUF-CMA, CSPRNG correctness, and BIP340
coefficient derivation are not established.

`QuantumStandardQuantumLimit` proves that `A/I + B*I`, for positive parameters,
has attained minimum `2*sqrt(A*B)` and unique optimizer `sqrt(A/B)`, where the
contributions balance. SQL-shaped variance and square-root bounds require the
explicit calibration `(hbar/(2*m*omega_m))^2 ≤ A*B`. Calibration and omission of
noise correlations are external model assumptions. Quantum commutators,
spectral densities, Langevin dynamics, and physical detector performance are
not formalized.
