# Sequential header-chain epoch authentication contract — ε202

Parent: distributed / distributed/tendermint-accountability.
Public release v0.7.9; structural chain verification under explicit trust premises.

## Required model and composition

An explicit trusted root starts a finite sequence of adjacent headers. A header
binds chain identity, height, epoch ID, current configuration commitment, next
configuration commitment and previous-header commitment. Each accepted new header
has a strict >2/3 commit under its current configuration and an abstract check of
its signers against that exact header. The previous authenticated header commits
to this current configuration through nextValidatorsHash. Headers must be adjacent
in height and belong to the same chain; epoch ordering is checked explicitly.

The actual checker must reject altered commitments, parent linkage, height/domain
and insufficient or unauthenticated signers. It must produce a history consumed
by the existing HistoryRegistry/resolveHistory API; invalid whole-chain input must
not populate a partially trusted registry. Histories contain only covered heights.

Prove local singleton/unique resolution for covered heights, cross-chain agreement
at heights covered in both chains under compatible committed headers, and rejection
of a supplied configuration whose commitment differs from its parent commitment.
Different-length prefixes need not give equal Option results beyond the shorter tip.

Compose the derived resolution with actual accepted historical blame and module200
collection/settlement/replay. Merely replacing the history field in SafetyConditions
is not sufficient: that predicate alone does not inspect the historical registry.
The unchanged safety theorem remains conditional on overlap, adoption and vote rules.
Positive collection still requires checked evidence, timely open admission, fresh keys
and positive liable holdings; complete offence-reference authenticity is separate.

## Explicit idealizations and open obligations

Abstract commitment binding/injectivity is an assumption, not a cryptographic theorem.
If the commitment covers the full existing EpochConfig, it also binds byzantine and
height-range annotations. That is stronger than a production validatorsHash encoding;
it does not establish that a committed fault annotation is true. Equal committed
configs are formal-model equality, not a theorem about canonical protobuf bytes.

Commit consistency/non-equivocation is an additional consensus assumption. Root trust,
hash links and quorum counts by themselves do not rule out two conflicting branches.
No proof may assume the desired historical-registry equality directly.

Signature checking is represented by an abstract authenticated-signing interface;
no signature algorithm, key lifecycle, corruption timeline, trusted-period expiry,
skipping/bisection light client, network delivery, wall-clock timing or liveness is
implemented. This contract discharges structural historical-lookup conditions under
its explicit premises; it is not an unconditional production light client.

Context source: https://github.com/cometbft/cometbft/blob/main/spec/light-client/verification/README.md
Consulted 2026-10-18: adjacent next/current validator commitments, current-set strict
commit quorum and the separate trusting-period condition. No compatibility claim
with every field or execution path of the production specification is made.
