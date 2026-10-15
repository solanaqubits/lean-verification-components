# Release v0.5.65: Kinked utilization rates and directed rounding

This release adds DeFiKinkedInterestRateUtilization as the 167th direct MasterSuite
import. It proves the rational utilization admission criterion, continuity and
monotonicity of a two-segment borrow curve, convexity under ordered slopes,
supply-rate monotonicity and conditional spread, and fixed-point rounding bounds.

For positive debt B and positive denominator D=Cash+B-Reserves, utilization U=B/D
is at most one exactly when Reserves<=Cash. Zero debt has its own U=0 branch.
Positive D alone is insufficient: Cash=10,B=100,Reserves=20 gives U=10/9.

With nonnegative base and slopes and 0<k<1, the borrow curve is r0+s1*u for u<=k
and r0+s1*k+s2*(u-k) otherwise. Both branches agree at k; topological continuity
over Q and monotonicity are proved without requiring s1<=s2. That additional
condition gives actual Jensen convexity. At fixed reserve factor 0<=rho<=1,
supply is rs=u*(1-rho)*rb and is nondecreasing for u>=0. On 0<=u<=1:

    rb-rs = rb*(1-u*(1-rho));
    0<=rs<=rb;
    rs<rb iff rb>0 and u*(1-rho)<1.

At u=1,rho=0 the spread is zero. A decreasing-slope regression demonstrates that
monotonicity and continuity do not imply convexity.

## Executable arithmetic and error bounds

The natural implementation uses scale W>0, floors utilization, rounds the whole
borrow numerator upward once, and floors supply once after multiplying all factors.
The checked quote requires the exact Reserves<=Cash condition or zero debt, so a
small excess U>1 hidden by utilization rounding still cannot pass admission.
Successful quotes satisfy uInt<=W and supplyInt<=borrowInt.

The rational reference uses the same encoded parameters divided by W. Utilization
error is in [0,1/W); borrow rounding at encoded utilization is in [0,1/W). Net supply
error at encoded utilization is two-sided, strictly between -1/W and 1/W, because
borrow has already been rounded upward. With L=max(s1,s2), full borrow error against
unquantized U lies in [-L/W,1/W). With S=(1-rho)*(rb(1)+L), full supply error lies
strictly between -(S/W+1/W) and 1/W on admitted unit-interval states. These bounds
include utilization quantization and cover intervals crossing the kink.

[Detailed contract](../knowledge/01_defi/DeFiKinkedInterestRateUtilization.md)

## Scope and open obligations

Rate order is an instantaneous algebraic property at fixed parameters. It does not
prove overall pool solvency, default freedom, withdrawable liquidity or absence of
liquidity crunches. Compound interest, debt indices, bad-debt writeoffs, reserve
dynamics and governance changes require separate transition models.

This is a reference rounding policy, not bit-exact refinement of deployed Compound
or Aave contracts. Natural arithmetic is unbounded; machine overflow, gas, oracle
truth, market execution and MEV are outside scope. Parameter quantization from an
arbitrary real curve is not covered by the error bounds above.

Tendermint Amnesia attribution still requires a complete observation or justification
contract. Bulletproofs knowledge extraction, computational binding, HVZK,
Fiat-Shamir/ROM and external Python, JSON/SHA-256 and SimLab correspondence remain open.

## Measured validation

| Check | Measured public result |
|---|---:|
| Direct MasterSuite imports | 167 |
| Lean files under Verification/ | 207 top-level + 2 auxiliary = 209 |
| Root-inclusive sources identical to the reference snapshot | 210 |
| Clean strict build | 3848 jobs; no warnings |
| Complete verifier audit | 23749 declarations; no violations |
| Pinned independent full audit | 23749 declarations; no violations |
| Public live tests | 112; no failures or skips; 332.383s |
| New kernel regression declarations | 46 |
| New executable scenarios | 25 |

Both full audits allow only propext, Classical.choice and Quot.sound.
The registry audit and knowledge catalog passed separately. The independent auditor
is pinned to source commit 46024e005996495c65ef609368e11ab39c4222e3 and executable
SHA-256 8a045cbabfa078df6577541d9768d5971ce573915f40e60806f32a50c3ffc254.
The project toolchain is v4.33.1; the auditor source toolchain file records v4.32.0-rc1.
This is an independent axiom auditor, not a second proof kernel.

The project build directory started empty; pinned dependency caches were copied
into this isolated checkout. All 210 proof sources match reference snapshot
4b9e1579c5decc412d4d0ec48ca90e7726f85d08 byte-for-byte.
Only English cards were exported; earlier public reports remain available.

```bash
lake build --wfail
python3 tools/verifier_skill.py verify-all
LEAN_VERIFIER_LIVE_TESTS=1 python3 -m unittest discover -s tests -p "test_*.py"
lake env lean -DwarningAsError=true Verification/AxiomAudit.lean
lake env /tmp/simon-axiom-audit-source/.lake/build/bin/axiom-audit --root Verification --allow propext,Classical.choice,Quot.sound --json
python3 scripts/check_knowledge.py
```

