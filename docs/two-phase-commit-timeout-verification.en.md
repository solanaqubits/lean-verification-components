# Operational two-phase commit timeout verification record

Private baseline: `6d95f3a009bcb6057997f3f28d08e331e61ad2cc`.

## Model and guarantees

One transaction has two independent participants and a separate fail-stop coordinator.
Packets inhabit an unbounded list; sends append and receives consume an actual
addressed packet. Arbitrary matching-packet delivery and drops are permitted.
The existing Decision type is reused, and the old decision-table module is unchanged.

Finite control obligations are checked by ordinary Lean kernel reduction, without
native_decide. Induction lifts them to arbitrary finite traces and unbounded queues.
The Step rules consult local control state and received packets, not a supplied
agreement invariant. Reachability derives packet provenance, terminal stability,
immutable coordinator decisions and no committed/aborted participant pair.

Pre-vote abort is permanent and excludes global commit in every continuation.
Two concrete reachable histories give P1 the same full observation list and prepared
state, while P2 is aborted in one and committed in the other. Every deterministic
policy forced to decide on this view violates agreement in one history. Waiting is
not excluded. Unsafe overrides are deliberately outside the legitimate Step relation.

When both participants are prepared and the coordinator has stopped, absence of
queued decision packets is equivalent to absence of any finite continuation reaching
a terminal participant. This structural equivalence itself does not require
reachability; safety of actual delivery follows separately from reachability.
A queued decision enables a concrete delivery step after crash. This is existential
escape, not guaranteed delivery or termination of both participants. A live-coordinator
counterexample and loss of the only decision packet exercise both boundaries.

No peer termination protocol, coordinator replacement/recovery, participant failure,
3PC, dynamic membership, disk WAL/fsync, physical clocks, Byzantine injection,
probabilistic delays or implementation-level liveness is modeled. chooseAbort is
permitted for any undecided running coordinator; nontrivial liveness is not claimed.
Python/JSON/SHA-256 and external SimLab byte binding remain separate obligations.

## Validation

- **110 unique direct imports**, **148 Lean files** under Verification/.
- Strict full build: **3530 jobs**, no warnings.
- Separate module verify and audit: **733 imported project declarations**, clean.
- Full verify-all and independent pinned audit: **10333 declarations**, only the three allowed axioms.
- **48 private live tests**, **79.908 seconds**, no errors, failures or skips.
- Strict AxiomAudit.lean hook, catalog, local links and static placement checks pass.
- Integration is idempotent; source hashes match after tests.
- Export preserves all **149 Lean sources**, including Verification.lean, byte for byte.
- Original HEAD and all **406 tracked-file hashes** are preserved.

```bash
python3 tools/verifier_skill.py verify Verification/DistributedTwoPhaseCommitTimeout.lean
python3 tools/verifier_skill.py audit Verification/DistributedTwoPhaseCommitTimeout.lean
python3 tools/verifier_skill.py integrate Verification.DistributedTwoPhaseCommitTimeout DistributedTwoPhaseCommitTimeoutSuite --apply
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
python3 scripts/generate_chip_manifest.py --check
```

The separate independent audit uses leanprover-community/axiom-audit v0.1.2,
pinned at `46024e005996495c65ef609368e11ab39c4222e3`. Only propext,
Classical.choice and Quot.sound are allowed. AxiomAudit.lean is an additional
strict registry hook. The CLI has no audit-all/test-all subcommands.

See the [scope card](../knowledge/09_distributed_systems/DistributedTwoPhaseCommitTimeout.md)
and [validation snapshot](../tools/validation_snapshot.json). The exporter includes
the proof, integration recipe, Python/Lean compiler regressions, English card and
this report. No .ru.md cards or simulations archive is exported.

## Isolation

Work uses an isolated clone. Final control checks compare original HEAD and all
406 tracked-file hashes. This task makes no writes to simulations and does not
revert concurrent SimLab activity; directory-wide immutability is not claimed.
This task publishes private main only, not a new public release.
