---
id: DistributedRaymondTreeMessageComplexity
language: en
section: distributed
source: Verification/DistributedRaymondTreeMessageComplexity.lean
source_sha256: d8ae99f1c0cd72cd4581ef57be95b008049639f19f598e3811d974d1d8a30059
novelty: not-assessed
status: reviewed
---

# Raymond message complexity on finite trees

[Section](../distributed/README.md) · [Lean](../../Verification/DistributedRaymondTreeMessageComplexity.lean)

## Contract and operational connection

This module imports DistributedRaymondTreeMutex unchanged. A completed isolated
request starts at its quiescent initial configuration: one token owner, empty
queues and no network traffic. Only the selected client may invoke a request.
The imported exact accounting theorem proves REQUEST sends = dist(u,t) and
PRIVILEGE sends = dist(u,t). The new bounds are proved about those actual counters
in an IsolatedExecution state whose requester is inCS, not about a standalone
formula substituted for a protocol.

Finite suprema define treeDiameter and treeHeight. For a connected finite tree,
M(u,t)=2 dist(u,t) ≤ 2 treeDiameter ≤ 4 treeHeight(root). The last inequality uses
the graph triangle inequality. Equality at 4h requires two depth-h vertices with
a shortest path through the root. Height alone does not imply diameter = 2h.

## Existence and tightness

[`isolated_completion_exists`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L333) separately proves existence of a finite enabled
execution reaching inCS for every requester and initial token owner with valid
holder routes. The proof uses an integer service rank, which strictly increases
on each enabled receive/deliver/assign/makeRequest step. Previously proved request
credits and isolated traffic potentials bound this rank. A still-requesting client
admits a service step: otherwise its queued request propagates along the finite
holder route to an owner whose queue must be empty, a contradiction. A maximal
attainable rank therefore supplies a completed finite execution.

This is an existential proof using classical choice, not an executable scheduler
or a bound on all schedules. No fairness or eventual-service assumption is hidden
inside the witness. Idle steps may delay a different execution indefinitely.
The separate liveness contracts of the imported module remain unchanged.

[`raymond_diameter_tightness`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L366) chooses an actual diametral pair, constructs valid
holder routes using the imported tree initialization theorem and applies finite
completion. Its conclusion includes Routes, self-pointing ownership, edge-local
holders, IsolatedExecution, inCS and the exact send counter 2 treeDiameter.

## Explicit tree families

RootedShape constructs a graph from a parent map with depth decreasing by one
away from the root. Connectivity, acyclicity and distance-to-root = depth are
proved, not supplied as tree-family assumptions.

KaryNode k h consists of words over Fin k of length at most h. The root is empty
and parent removes the final letter. A bijection with the disjoint union of
vectors of lengths 0 through h gives N = sum_{j=0}^h k^j. For k≥2 and h≥1:

- N = (k^(h+1)−1)/(k−1), and k^h ≤ N < k^(h+1).
- Height is h and diameter is 2h. Constant words starting with 0 and 1 lie in
  different root branches; a signed-depth potential proves their distance is 2h.
- Maximum messages = 4h = 4 Nat.log k N. [`kary_cost_isBigO`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L807) proves the actual
  Mathlib IsBigO statement, atTop in h for each fixed k, using the vertex count N(h).

Graph isomorphisms preserve distance and diameter. AttainedOnFin transports each
finite family to Fin(card V), and asserts an actual completed protocol execution.
[`kary_operational_attainment`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L696), line_operational_attainment and
star_operational_attainment supply these witnesses.

The chain is Fin N with parent predecessor; its diameter is N−1. The star has
parent 0 at all other nodes; for N≥3 it has height 1 and diameter 2. Regressions
include a local token (0 sends), chain (2(N−1)), star (4), binary height 3
(N=15, diameter=6, maximum=12 and not 8), plus ternary height 2 (N=13, maximum=8).
The single-node chain and height-zero count are also checked.

## Main theorems

[`raymond_bound_diameter`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L62), [`isolated_completion_exists`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L333), [`raymond_diameter_tightness`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L366),
[`raymond_bound_height`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L70), [`raymond_height_tightness`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L81), [`complete_kary_tree_metrics`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L636),
[`kary_operational_attainment`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L696), [`kary_cost_isBigO`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L807), [`reg_token_holder`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L92), [`reg_line_graph`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L726),
[`reg_star_graph`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L761) and [`reg_binary_tree_h3`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L783).
Master theorem: [`distributed_raymond_tree_message_complexity_master_suite`](../../Verification/DistributedRaymondTreeMessageComplexity.lean#L867).

## Clean Water

Only REQUEST and PRIVILEGE network sends for isolated requests are counted.
Local handler steps, delivery events and real time are different quantities.
Concurrent request costs, amortized queue costs, random traffic, network latency,
failures and recovery are outside this extension. The asymptotic statement applies
to the specified complete k-ary family, not arbitrary trees. A chain remains linear.
The graph and protocol are mathematical models; implementation refinement is not proved.
Python correctness, JSON/SHA-256 correctness and the SimLab → Lean obligation remain open.
Novelty remains not-assessed.

## Source and reproducible checks

Kerry Raymond, [A tree-based algorithm for distributed mutual exclusion](https://doi.org/10.1145/58564.59295),
ACM Transactions on Computer Systems 7(1), 61–77 (1989). This module treats the
isolated case in the existing formal transition model; it does not claim all
performance or fault-recovery properties discussed in the paper.

Run module verify/audit, lake build --wfail, verify-all, the unittest suite with
LEAN_VERIFIER_LIVE_TESTS=1, Verification/AxiomAudit.lean with warningAsError,
the pinned independent axiom auditor, and scripts/check_knowledge.py.
The measured results are appended after execution.

## Historical source-side validation

Base snapshot: `611ba17cda45a492ff45c83f698456408ea402e8`.

| Check | Measured result |
|---|---:|
| Direct MasterSuite imports | 128 |
| Lean files under Verification/ | 168 top-level + 2 support = 170 |
| Root-inclusive byte-identical export | 171 sources |
| Clean strict private build | 3619 jobs; no warnings |
| Both full axiom audits | 14727 declarations; no violations |
| Private live tests | 76; no failures or skips; 268.184s |
| Export live tests | 73; no failures or skips; 280.960s |
| Export clean strict build | 3619 jobs; no warnings |

Module verify and audit each covered 903 declarations in the imported closure.
Both full audits permit only propext, Classical.choice and Quot.sound.
The independent auditor source is pinned to 46024e005996495c65ef609368e11ab39c4222e3;
binary SHA-256: 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
Project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
The executable is pinned separately; a second independent proof kernel is not asserted.
Counts include generated declarations. Both project build directories started empty,
with isolated copies of pinned dependency caches. Integration is idempotent.
Prior subject proof sources, original HEAD and 406 tracked files outside simulations/
are preserved. This task makes no writes to simulations/ and no public release.

## Public release validation

The separate [v0.5.26 report](../../docs/release-v0.5.26.en.md) records fresh public checks.

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 128 |
| Lean files under Verification/ | 168 top-level + 2 auxiliary = 170 |
| Root-inclusive sources identical to the private snapshot | 171 |
| Clean strict build | 3619 jobs; no warnings |
| Complete verifier audit | 14727 declarations; no violations |
| Pinned independent full audit | 14727 declarations; no violations |
| Public live tests | 73; no failures or skips; 267.488s |
