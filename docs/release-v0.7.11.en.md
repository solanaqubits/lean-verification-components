# Release v0.7.11 — Bulletproofs IPA finite forking probability

This release adds epsilon204, synchronizing 248 Lean sources and 204 direct
MasterSuite imports with private snapshot
8886170c4e32df5bb9bd0df700fdff4a029a4c91. Lake remains 0.7.1.

## Results and exact premises

Fix the prover state and common prefix. Four independent uniform draws with
replacement from nonempty C, with accepting subset A, have successful-outcome
count at least m(m−2)(m−4)(m−6), using truncated natural subtraction.
Here m=|A| and N=|C|. For m≥6 the rational probability lower bound is
m(m−2)(m−4)(m−6)/N^4; for m≥7 it is strictly positive.
The counting results permit zero. Protocol `replySet` filters zero and absent
responses before connecting a successful quadruple to the existing extractor.

For uniform prefixes, the heavy-prefix fraction is at least
(pbar−theta)/(1−theta), for theta<1. The combined average lower bound uses
6/N≤theta<1 and is strictly positive when 6/N<theta<pbar and theta<1.
An average bound does not guarantee success at every prefix.

Extraction uses the exact sampled four branches with a common statement/message
and independently checked valid completed child trees. It returns a valid witness
or a nonzero generator relation, in the existing API. This need not recover the
prover's original secret and does not introduce an external dot-product claim.

## Verification and open obligations

Public evidence is checked separately from private evidence. The planner assigns
the actual dependency scope; measured commands and counts are recorded in the
annotated tag and public-tree report. No new full beta checkpoint is claimed.
Public full beta remains 2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1);
private full beta remains 090aed141b831aee5182197e9ea205176f361c0f.
Only propext, Classical.choice and Quot.sound are allowed. Existing caches are
retained and imported audit scopes are not recounted separately.

The general Forking Lemma, adaptive rewind execution, Fiat–Shamir/ROM security,
expected polynomial extraction time, whole-tree readiness probability,
computational binding, blinding and zero knowledge remain outside scope.

SimLab, digital-brain, raw chats, simulations, Russian cards, private working
materials and private Git history are excluded. No new experiment or module
number is allocated by this publication.
