---
id: QuantumQutritDecoderCircuitRefinement
language: en
section: quantum-physics
source: Verification/QuantumQutritDecoderCircuitRefinement.lean
source_sha256: 3b6308519320f452952b3eefbd6d386974ec51e18f4ede39171b5e38ba63a55f
novelty: not-assessed
status: reviewed
---

# Gate implementation and refinement of the qutrit decoder

[Section](../quantum-physics/README.md) · [Lean](../../Verification/QuantumQutritDecoderCircuitRefinement.lean)

The executable finite interpreter acts on `Fin 3 × Fin 3`. Its primitives are
controlled addition to either coordinate, exchange, and a local cyclic shift.
Each gate and every finite circuit have explicit inverses. Execution is left to
right; concatenation satisfies `M(a ++ b) = M(b) * M(a)`.

The decoder executes `addSecond 2`, `addFirst 2`, then `swap`: two controlled
subtractions modulo three. Its output is exactly `(v-u, 2*v-u)`. The proof covers
all nine inputs, and the permutation matrix equals the decoder of module 190.
Both unitary identities hold for every circuit in this gate language. Three gates
are exhibited; minimality is not claimed.

The three operators `circuitKraus t = erasureOperator 3 3 t * circuitMatrix decoderCircuit`
are defined from the circuit. Their completeness gives `circuitRecovery : KrausChannel 9 3 3`.
`channel_refinement` proves equality with `explicitRecovery` on **all complex
physical matrices**, including coherences. Exact recovery for every erased share
and arbitrary reference dimension follows through modules 190, 188 and 187.
Agreement with the chosen `pairRecovery` of module 189 is asserted only on encoded
pair inputs.

## Independent expectations and negative regressions

Regressions check the nine expected outputs, the executable `--run` interpreter,
composition order, CPTP properties, complex off-diagonal inputs, all three erasures,
maximally entangled qutrit inputs and registry projections. Separate bridges compare
coordinates, matrices and Kraus operators with the unchanged normative
`Verification.Specs.QuantumQutritDecoderSpec`. The expected flat table is
`0,5,7,8,1,3,4,6,2`.

Wrong control sign, omitted exchange, exchanged controlled-gate order and a final
shift have concrete unequal output witnesses and unequal matrices. These reject
incorrect circuits; they do not establish correction of faulty gates.

## Clean Water and scope

This is a finite executable basis interpreter with an exact algebraic refinement
proof. Complex numerical simulation, circuit compilation, hardware execution,
noise robustness, active share substitution and gate-count optimization are outside
scope. Python, JSON/SHA-256 and SimLab obligations remain open. Allowed axioms are
`propext`, `Classical.choice`, `Quot.sound`; novelty is not assessed.

Change scope: epsilon module 191, delta `quantum-physics/qutrit-secret-sharing`,
gamma `quantum-physics`. Integration metadata changes trigger beta validation under
the existing conservative planner. The starting full beta release is v0.6.0,
private commit `1fb3818e9ee1d011c75cffe54ca0f8df3104b69e`.
Validation evidence records exact inputs, strict build, scoped verifier runs,
full beta checks, live tests and knowledge checks; declaration scopes overlap.
Passing checks do not certify human intent or universal independent semantic review.
