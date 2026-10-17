---
id: HCTKScalarPartition
language: en
section: quantum-physics
source: Verification/HCTKScalarPartition.lean
novelty: not-assessed
status: reviewed
source_sha256: 4489592fae779ababb2445d3593c5d0bfa0e2f3d07aeca060bd198f2d4099445
---

# HCTKScalarPartition

[Section](../quantum-physics/README.md) · [Lean](../../Verification/HCTKScalarPartition.lean)

Module ε201, parent quantum-physics / hctk-scalar-partition. Integrated after
module 200; scalar properties are registered in QuantumPhysicsFullSuite.

## Checked statements

`Parameters` gives positive Real constants/scales. `frequency_pos`,
`metricScalar_pos`, `temperature_pos`, `informationBound_nonneg` prove signs of
prescribed formulae. Scaling theorems concern exact real arithmetic, not binary64.

`State` has two Real amounts and an Int label. `partition_total` derives
Q*p+Q*(1-p)=Q; `partition_bounds` needs Q>=0 and 0<=p<=1. Endpoints and local
monotonicity are proved. `transfer_total` proves preservation for the actual
transition (l-d,r+d,n); `transfer_nonneg` needs 0<=d<=l and r>=0.
`runTransfers_invariants` proves total/label preservation by list induction.
The label is copied; it is not constructed as a Chern invariant.

`regularizedWindow_bounds` proves 0<tau/(p+eps)<=tau/eps under tau>0,eps>0,p>=0;
`regularizedWindow_stopped` reaches the cap at zero power. The function is
antitone in power. `idealWindow_unbounded` instead gives, for any positive bound,
a power in (0,1] with tau/p above it. This does not make division at zero infinite.

## Boundaries and verification

Contract: [hctk-scalar-contract](../../docs/hctk-scalar-contract.en.md).
No electromagnetic cavity, Hamiltonian, spectral gap, bundle, Chern integral,
Landauer erasure protocol, physical charge transport or resonator stability is
modeled. The Gaussian pulse belongs only to the separate illustrative simulation.
A charge interpreted as mass is an unresolved dimensional assumption.

Public release v0.7.10 synchronizes private snapshot
5779d30ff6419ee91f787d04f45f3d3b5d483e55. Lake remains 0.7.1. Public validation
is recorded separately; the full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1).
See [release notes](../../docs/release-v0.7.10.en.md).

## Three-store capture refinement

CaptureState=(b,c,v,n); capture(s,d,eta)=(b-d,c+eta*d,v+(1-eta)*d,n).
capture_total derives conservation from the update; no final conservation premise.
capture_nonnegative requires initial nonnegativity,0<=d<=b and0<=eta<=1.
AdmissibleCaptures checks each actual intermediate state; capture_trace_contract
extends total, nonnegativity and copied label to finite traces. collapse_capture
and collapse_runCaptures refine the existing transfer/runTransfers by aggregating
the two outgoing stores. capture_complete computes a full-release state;
captured_increment_bounds bounds the captured increment. The existing suite
exposes capture_trace/capture_refinement; no new module number.

These real-number theorems do not prove Python/binary64 refinement, physical
phase conjugation, a Chern invariant or preservation of brain information.
The label is copied by definition. A single eta gives eta*q; the original
numerical profile used eta twice and is a different model. Previous numerical
observations and private thematic documents are outside this public export.
