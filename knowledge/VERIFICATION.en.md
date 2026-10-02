# Verification record

[Knowledge base](README.md)

The Lean sources are distributed with SHA-256 hashes in
[validation_snapshot.json](../tools/validation_snapshot.json). The imported proof
snapshot contains 125 Lean files under Verification/, 92 direct MasterSuite
imports, and 7,812 declarations including generated declarations.

For release v0.4.3 the public export passed strict compilation with
3,507 build jobs and 26 public regression tests without skips.
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
