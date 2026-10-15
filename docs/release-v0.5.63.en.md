# Release v0.5.63: Weighted Tendermint core safety

This release adds DistributedTendermintCoreSafety as the 165th direct MasterSuite
import. It proves weighted quorum intersection, same-round Polka/Commit uniqueness,
lock preservation across rounds and agreement of commits from reachable states.

For strict quorums 3*w(Q)>2*W, safety holds when 3*W_byz<=W, including equality.
A concrete reachable conflicting execution is exhibited above this threshold;
this does not assert that every above-threshold configuration admits a conflict.
The executable transition function is proved equivalent to the operational Step
relation. Duplicate votes cannot increase signer weight. A stale certificate for
a conflicting value is rejected; a certificate for the already locked value may
be accepted. A bare Proposal does not replace a required Polka certificate.

[Detailed contract](../knowledge/05_distributed_systems/DistributedTendermintCoreSafety.md)

## Scope and open obligations

This is a fixed-height, fixed-validator-set safety abstraction with natural-number
block identifiers and ideal authentication of vote senders. Proposal selection,
timers and application validity are overapproximated. Late validValue updates
used for progress are omitted. No refinement equivalence to full Algorithm 1 or
a production Tendermint implementation is claimed. External envelopes require
the executeAtHeight guard. Safety applies to each admitted message delivery order;
it does not assert identical executions under different schedules.

Liveness/GST, validator rotation, signatures, the network stack, economic slashing
and algorithmic extraction of attributable slashing evidence remain outside scope.
The accountability result is a contrapositive of safety, not an evidence extractor.
Bulletproofs knowledge extraction, computational binding, HVZK, Fiat-Shamir/ROM,
and external Python, JSON/SHA-256 and SimLab correspondence remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 165 |
| Lean files under Verification/ | 205 top-level + 2 auxiliary = 207 |
| Root-inclusive sources identical to the reference snapshot | 208 |
| Clean strict build | 3845 jobs; no warnings |
| Complete verifier audit | 23432 declarations; no violations |
| Pinned independent full audit | 23432 declarations; no violations |
| Public live tests | 110; no failures or skips; 331.279s |
| New kernel regression declarations / compiled scenarios | 49 / 29 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 208 proof sources match reference snapshot
19bd8e16701d694a7def70d8967d1b017ecc7a57 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

