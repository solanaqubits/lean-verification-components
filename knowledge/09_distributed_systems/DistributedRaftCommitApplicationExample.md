---
id: DistributedRaftCommitApplicationExample
language: en
section: distributed
source: Verification/DistributedRaftCommitApplicationExample.lean
source_sha256: fac302c4c12bf50fbdad066c0c673008bcf22c835c74f3beb90aa24dc1e0615b
novelty: not-assessed
status: reviewed
---

# Reachable old-term-majority counterexample

Forty-five original operational transitions on five nodes elect leaders in terms 1 through 4. The term-3 leader receives majority acknowledgments for a term-1 entry; all direct commit guards except current-term equality hold. A later legitimate term-4 leader overwrites a copy with a different command. The same-execution path, both reachable endpoints and hypothetical fold difference are kernel-checked. Endpoint commit indices are zero. The example follows the Figure-8 mechanism without asserting a modeled crash or an illegal application event.

See the [application contract](DistributedRaftCommitApplication.md) and [validation](../../docs/raft-commit-application-verification.en.md). No liveness, runtime or physical implementation claim is made.
