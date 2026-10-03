# Verification record

[Knowledge base](README.md)

The Lean sources are distributed with SHA-256 hashes in
[validation_snapshot.json](../tools/validation_snapshot.json). The imported proof
snapshot contains 134 Lean files under Verification/, 100 direct MasterSuite
imports, and 8,237 declarations including generated declarations.

For release v0.5.0 the public export passed strict compilation with
3,516 build jobs and 35 public regression tests without skips.
The complete module verifier and independent axiom audit passed; only the
standard axioms listed below occurred.

Reproduce the public checks with:

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -v
python3 scripts/check_knowledge.py
```

The allowed axioms are propext, Classical.choice, and Quot.sound. The single
registry audit checks the selected theorem; verify-all audits all project
modules. The CI workflow also runs an independent project-wide axiom audit.

Formal claims retain their hypotheses. Successful compilation and an allowed
axiom list do not establish end-to-end cryptographic security, the correctness
of a production implementation, or scientific novelty.

## Placement certificate and physical scope

`ChipPlacementCertificate` checks exact rational records for 256 nodes. It proves
containment in the 4000 by 4000 micrometre die, positive rectangle dimensions,
unique node identifiers, and pairwise disjoint closed rectangles. Rational
containment transfers to real coordinates without rounding. The separate
`ChipLayoutGeometry` module supplies universal translation and bounds results.

Published input bytes, SHA-256 labels, and the deterministic converter provide
external provenance evidence. The formal theorem concerns the embedded Lean
records; it is not a verified JSON parser or a proof of SHA-256 computation.
Placement certification does not certify interconnect routing, optical losses,
delays, or physical fabrication.

`CryptoFeldmanVSS` proves scalar share consistency and reconstruction, not secrecy:
`A0/G` reveals the secret in this real-valued model. `QuantumOptomechanicalCoupling`
proves prescribed scalar relations, not a quantum operator model. The regime of
the `4*g^2/kappa` approximation is documentation, not a Lean theorem; positive
damping does not by itself establish physical cooling or full coupled stability.

## Raft execution safety

`DistributedRaftNetworkInduction` proves global Log Matching for reachable states.
`DistributedRaftCompleteBridge` derives Leader Completeness from actual commit
events and proves retention for nodes already holding the whole committed prefix.
The earlier conditional abstract history premises are not assumed, and the
original operational transitions are unchanged. The whole-log replacement rule
of abstract VoterEvolution is not literally instantiated.

The static-cluster model includes partial batches and delayed, duplicated, lost,
or reordered protocol-generated messages. Dynamic membership, crash/recovery,
Byzantine injection, and liveness are not proved. Two public compiler regressions
exercise nonempty executions, message history, conflicting commands, and actual
commitment followed by election of a different leader.

## Scalar aggregation and visibility

`CryptoMuSig2Aggregation` proves scalar two-signer, two-nonce completeness,
assembly from valid partial signatures, and a restricted naive-key cancellation
barrier under distinct weights and a nonzero first key. It also proves that fixed
weights admit a chosen aggregate key and that scalar public keys reveal secrets.
This is not a cryptographic rogue-key security proof for BIP 327. Hash oracles,
secp256k1, nonce-reuse defenses, and two-round network behavior are not modeled.

`MithraicPhaseCollapse` proves visibility bounds, exact zero/unit contrast,
monotonicity at a fixed maximum, and threshold acceptance/rejection over real
scalars. Positive total intensity excludes the dark 0/0 case. Equality at the
threshold is accepted; zero contrast is rejected only by a positive threshold.
The extrema are not simultaneous MZI output-port intensities. No quantum
decoherence, physical noise mechanism, or automatic dump-port control is proved.


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


## Threshold time envelopes, elementary forking, and beam splitters

`DistributedMarzulloAlgorithm` proves that a threshold envelope contains the true
time under an explicit bound on faulty interval sources. It includes a counterexample
to truth localization by maximum overlap. No NTP sorted sweep, network-delay model,
clock drift, or PLL is verified.

`CryptoTranscriptForkingLemma` proves the finite matrix bound
`epsilon * (epsilon - 1/q)`, fork existence above the threshold, and scalar witness
extraction. Rows are uniform and nonempty, challenges are independent and uniform
with replacement, and the commitment is fixed per row. The general multi-query
Bellare–Neven theorem, adaptive ROM behavior, and security/runtime reductions are
outside scope.

`QuantumBeamSplitterTransform` proves a real orthogonal two-mode transformation,
its finite symmetric-square lift in a normalized occupation basis, preservation of
both norms, and zero coincidence amplitude exactly at balanced power. The Born
interpretation and indistinguishability are model assumptions. Complex reflection
phases, full Fock space, wave packets, and physical detectors are not formalized.

## Acyclic hundred-import registry

`MasterSuiteComponents` retains the existing component declarations and names;
`MasterHundredRegistry` assembles selected package propositions; `MasterSuite`
imports the milestone and retains the central entry point. No reverse import is
introduced. The new wrapper preserves hypotheses and adds no domain theorem.
The 100 direct imports are an externally checked repository metric, not a Lean
proof of coverage of every declaration or of open mathematical problems.
