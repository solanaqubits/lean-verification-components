---
id: HCTKScalarPartition
language: en
section: quantum-physics
source: Verification/HCTKScalarPartition.lean
novelty: not-assessed
status: reviewed
source_sha256: c8851fdaa1cc8d19e4a5b52f59c76d2bedddab02ccd8a15df888d857625d9d55
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

Public release v0.7.9 exports private snapshot
831248e509744e9a7900fa0cc7f01a88ee957b2f. Lake remains 0.7.1. Public-tree verification
is recorded separately from private checks. The full public beta basis remains
2419489245019fb16e32ffac641b9f88eea94126 (v0.7.1); private full control remains
090aed141b831aee5182197e9ea205176f361c0f. See [release notes](../../docs/release-v0.7.9.en.md).

`QuantumPhysicsFullSuite.hctk_scalar` registers the scalar results. Numerical studies
and their artifacts are outside this public Leanbook release. No physical claim is added.
