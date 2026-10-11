# Release v0.5.40: Coordinated attack impossibility

Private proof snapshot: `516c0748a91a7c5c222d76759b24ae3781886d1d`.
Previous public main: `4d3109aec84a241ed5a21b30dd65bcdfae6cd489`.

## Proven scope and assumptions

The model has two correct deterministic processes, private binary inputs,
arbitrary message and local-state types, and a fixed finite round horizon T.
Sends depend on pre-round states. Incoming messages can independently be lost;
there is no sender-visible delivery feedback. Self-delivery flags are ignored.

Removing one outgoing delivery preserves the sender's next local state. If no
later messages are delivered, it preserves that sender's entire remaining local
history. These facts are derived from execution, not assumed as external axioms.
Under Agreement, removal preserves the common decision. Strong induction on the
number of actual cross-process deliveries reduces any schedule to total loss.
With total loss, each local state depends only on its own input. Changing the
two private inputs one at a time therefore preserves the common decision.

For every fixed finite T, Agreement and ValidityZero force retreat for all inputs
and schedules, contradicting ReliableSuccess. The impossibility concerns these
three properties together; Agreement alone is not impossible. Regressions cover
T = 0, an always-retreat protocol, commuting removals, and a concrete two-round
request/ack exchange whose lost acknowledgement causes disagreement. A protocol
satisfying Agreement and ValidityZero must retreat on that same schedule.

This is a synchronous lossy-channel result, distinct from FLP. No theorem about
unbounded stopping times or eventual termination without a uniform finite bound
is asserted. Randomized epsilon-agreement, quantum channels and Byzantine
behavior are outside scope. Python, JSON/SHA-256 and SimLab obligations remain
open. No novelty claim is made.

## Measured public validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 142 |
| Lean files under Verification/ | 182 top-level + 2 auxiliary = 184 |
| Root-inclusive sources identical to the private snapshot | 185 |
| Clean strict build | 3732 jobs; no warnings |
| Complete verifier audit | 18279 declarations; no violations |
| Pinned independent full audit | 18279 declarations; no violations |
| Public live tests | 87; no failures or skips; 276.094s |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent
full auditor is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and
binary SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; no second independent proof kernel is asserted.

The project build directory started empty. Pinned dependency caches were copied
into this isolated tree. All public checks were rerun against this release candidate.
Declaration counts include generated declarations, not just mathematical theorems.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

All 185 Lean sources match the private snapshot byte-for-byte. Repeated English
exports agree. Integration is idempotent. Earlier subject cards and historical
public reports are preserved; Russian cards are not exported. Reservoir metadata
are retained; external indexing is not asserted.

## Publication and preservation

Publication uses sequential pushes: main first, confirm its remote SHA, then
annotated v0.5.40. Existing tags are not overwritten. A separate receipt records
the remote commit, tag object and peeled tag SHA.

Original workspace HEAD and 406 tracked-file hashes outside simulations/ are
preserved. This task makes no writes to simulations/; concurrent external activity
is not covered by a global immutability claim.

[Detailed contract](../knowledge/09_distributed_systems/DistributedCoordinatedAttackImpossibility.md)
· [Hashes and measured commands](../tools/validation_snapshot.json)
