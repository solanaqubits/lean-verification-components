---
id: DistributedByzantineThreeGeneralsOralImpossibility
language: en
section: distributed
source: Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean
source_sha256: c662fb7f6396a0e4dcb5e9e3a2ff19f3f1a3c171cc0d43f9305df392cd941bd4
novelty: not-assessed
status: reviewed
---

# Three generals: oral Byzantine broadcast impossibility

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean)

## Model and statement

Three roles (commander and two lieutenants) execute arbitrary deterministic,
identity-dependent code for a fixed finite horizon T. Message and local-state
spaces are arbitrary types. Only the commander's initial state receives the
binary order. Every round computes recipient-specific sends from the previous
states, then updates all states simultaneously. Inboxes identify the immediate
sender. Self messages are ignored. Messages between honest nodes arrive faithfully;
an optional single static faulty identity may send arbitrary Option Msg values
independently to each recipient, including silence.

Agreement requires equal decisions when both lieutenants are honest.
CommanderValidity requires every honest lieutenant to decide the order of an
honest commander. Decisions occur at T; execution is held constant afterwards.
For every T, no protocol satisfies both specifications. The statement quantifies
over all message and state types, rather than only one example algorithm.

## Operational construction

A joint recursive simulation maintains four states: honest commander copies c0
and c1 initialized with orders 0 and 1, and shared lieutenants l1 and l2. Copy c0
receives l1's messages and silence from the other lieutenant; copy c1 receives
l2's messages and silence from the other. Lieutenant l1 receives c0 and l2;
lieutenant l2 receives c1 and l1. All sends use pre-round states.

In scenario 0, lieutenant 2 is faulty: it sends the simulated l2 message to
lieutenant 1 and silence to the honest commander with order 0. In scenario 1,
lieutenant 1 is faulty, symmetrically with commander order 1. In scenario 2,
the commander is faulty: it sends c0's messages to lieutenant 1 and c1's messages
to lieutenant 2. Induction derives the correspondence of the honest states to
the virtual states in each scenario. Thus each honest lieutenant's complete
state history in scenario 2 equals its history with an honest commander.
CommanderValidity forces decisions 0 and 1, contradicting Agreement.

The adversarial schedules are explicitly constructed from earlier virtual states.
Quantification over all finite schedules covers transcripts of adaptive attackers;
the proof does not assume either a transcript equality or an impossible agreement
in an auxiliary system. No signatures or trusted checks of relayed testimony are
available: the attacker can construct arbitrary message values in this OM model.

## Regressions

The theorem includes T = 0. An always-retreat protocol satisfies Agreement but
violates CommanderValidity. The explicit one-round follow-commander protocol
satisfies CommanderValidity and works when all three nodes are honest, but an
equivocating commander makes the two honest lieutenants decide 0 and 1.
Kernel regressions also check private-input isolation, faithful delivery by an
honest sender and silence by a faulty sender.

## Clean Water boundaries

This is deterministic Byzantine broadcast for exactly three nodes and at most
one static Byzantine fault, in synchronous oral messages with a common fixed
finite horizon. It does not prove the general n <= 3f lower bound, nor cover
unbounded eventual termination, signed messages (SM), randomized protocols or
quantum communication. It is distinct from the preceding omission-only
coordinated-attack theorem and from asynchronous crash-failure FLP.
Python, JSON/SHA-256 and SimLab obligations remain open. Novelty is not assessed.
Only propext, Classical.choice and Quot.sound are permitted.

Reference: Lamport, Shostak and Pease (1982),
[The Byzantine Generals Problem](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/12/The-Byzantine-Generals-Problem.pdf).

## Validation

Base snapshot: 0744cfdef0c8cc1529eab2c5006dd47ffb678d27.
All project and export checks passed; measured results follow.

## Source theorem links

- [scenario0_simulation](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L118)
- [scenario1_simulation](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L135)
- [scenario2_simulation](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L152)
- [local_state_induction_scen0_scen2](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L169)
- [local_state_induction_scen1_scen2](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L174)
- [lieutenant1_decides_zero](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L179)
- [lieutenant2_decides_one](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L185)
- [byzantine_three_generals_oral_impossibility](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L191)
- [no_correct_protocol](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L198)
- [constant_retreat_regression](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L211)
- [zero_horizon_impossibility](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L219)
- [follow_commander_validity](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L229)
- [conflicting_orders_regression](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L239)
- [naive_follow_commander_violates_agreement](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L243)
- [all_honest_follow_commander](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L251)
- [byzantine_three_generals_oral_master_suite](../../Verification/DistributedByzantineThreeGeneralsOralImpossibility.lean#L275)

## Private snapshot validation: Three-generals oral Byzantine broadcast

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 144 |
| Lean sources including root | 187 |
| Strict clean private build | 3734 jobs; no warnings |
| Both full axiom audits | 18521 declarations; no violations |
| Private live tests | 92; no failures or skips; 292.45s |
| Export live tests | 89; no failures or skips; 304.878s |
| Strict clean export build | 3734 jobs; no warnings |

Module verify and audit each covered 1010 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
Independent auditor source: 46024e005996495c65ef609368e11ab39c4222e3.
Binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain: leanprover/lean4:v4.33.1; auditor source toolchain file: leanprover/lean4:v4.32.0-rc1.
The binary is pinned separately; a second independent proof kernel is not claimed.
Counts include generated declarations. Both project .lake/build directories were absent
before the final builds. Each tree uses its own copy of the pinned dependency cache.
All 187 exported Lean files match byte-for-byte; repeated exports agree.
Integration is idempotent. Original HEAD and 406 tracked files
are preserved. No writes to simulations/. That earlier private integration did not publish a public release.

The theorem rules out Agreement and CommanderValidity together for three nodes,
at most one static Byzantine identity and any fixed finite horizon T in synchronous OM.
Local indistinguishability follows from round transitions in an explicit joint simulation.
General n <= 3f, signed messages, randomized protocols and unbounded termination
are outside scope. Python, JSON/SHA-256 and SimLab obligations remain open.

## Public release validation

The [v0.5.42 report](../../docs/release-v0.5.42.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 144 |
| Lean files under Verification/ | 184 top-level + 2 auxiliary = 186 |
| Root-inclusive sources identical to the private snapshot | 187 |
| Clean strict build | 3734 jobs; no warnings |
| Complete verifier audit | 18521 declarations; no violations |
| Pinned independent full audit | 18521 declarations; no violations |
| Public live tests | 89; no failures or skips; 288.517s |
