# Release v0.5.13: Ricart–Agrawala and statement conformance

Private proof snapshot: `09507001387c0e684c981e8d1ffdf67a77f68f41`.
Previous public main: `5f5ea31603985f18bc67c8214437598640226703`.

## Proven scope

The fixed finite, crash-free Ricart–Agrawala model derives mutual exclusion by
induction on reachable transitions. Tagged requests and distinct reply senders
prevent old responses or duplicates from authorizing a new invocation.
Channels permit reordering; FIFO is not required. Request fanout is a local enqueue,
with separate receipt, response, entry and exit events.

Every Wanted request eventually reaches Held with the same timestamp under
ReliableDelivery, WeakFairness for continuously enabled response/entry actions,
and FiniteCS. These contracts do not assume eventual entry itself. New requests
may appear during the proof. Safety does not require the progress contracts.
No crash-stop, crash-recovery, Byzantine behavior, changing membership, network
partition tolerance, numerical waiting bound or production implementation is proved.

The Simon meta-audit adds two auxiliary Lean specifications, a reviewed pin manifest,
a Lean Meta probe, the Python checker and mutation tests. It compares selected
field types and definition bodies against the independent fixed contract, checks
the kernel-proved bridge and audits axiom dependencies. Concrete witnesses establish
specified satisfiable premises. It is neither a universal nonvacuity detector nor
a sandbox for hostile Lean/Lake code. Alternate proof terms preserving the contract
are accepted; the tested False, True, zero-period and rank/cardinality substitutions
are rejected. Python, parsing, JSON/SHA-256 and SimLab input-to-byte binding remain
external obligations.

## Independently measured public validation

| Check | Result |
|---|---:|
| Direct MasterSuite imports | 115 |
| Lean files under Verification/ | 155 top-level + 2 support = 157 |
| Root-inclusive proof sources matching the private snapshot | 158 |
| Clean strict build | 3540 jobs; no warnings |
| Complete local audit | 12035 declarations; no violations |
| Independent pinned audit | 12035 declarations; no violations |
| Public live tests | 60; no failures or skips; 245.329s |

The project build directory started empty. Dependency caches were copied into the
isolated clone; this is not a from-source rebuild of Mathlib. Both full audits allow
only propext, Classical.choice and Quot.sound. Counts include generated declarations.
The existing strict registry hook and catalog checks also pass.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p 'test_*.py' -v
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
python3 scripts/check_knowledge.py
```

The independent auditor is leanprover-community/axiom-audit v0.1.2, commit
`46024e005996495c65ef609368e11ab39c4222e3`, compiled with the pinned Lean toolchain.
It is invoked through `lake env`, with `--root Verification`,
`--allow propext,Classical.choice,Quot.sound` and `--json`.
The registry hook is an additional check, not a second proof kernel.

All 158 proof sources and the conformance checker/pins/probe/tests are transferred
byte-for-byte from the approved private snapshot. Previously published reports
are retained. The current English documentation distinguishes the historical
pilot metrics from this public run. No Russian cards are exported.

Publication uses an annotated v0.5.13 tag and
`git push --atomic origin main v0.5.13`; existing tags are not rewritten.
The original workspace HEAD and all 406 tracked-file hashes outside simulations/
are preserved. This task does not write to simulations/; concurrent SimLab activity
is not interpreted as immutability of the entire directory.

[Model and theorem assumptions](../knowledge/09_distributed_systems/DistributedRicartAgrawalaMutex.md)
· [Conformance pilot](statement-conformance.en.md)
· [Source hashes and measured commands](../tools/validation_snapshot.json)
