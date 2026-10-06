#!/usr/bin/env python3
"""Untrusted enumerator for the finite 3PC certificate; Lean checks closure and safety.

No generated state or Python result is accepted as a theorem. --check is read-only.
"""
from collections import deque
from pathlib import Path
import argparse
# s0,s1,yes,live,member,owner,epoch,phase,k0,k1,r0,r1
# phase: vote, report, align-commit, align-abort, final-commit, final-abort
INITIAL=(0,0,0,7,3,0,0,0,0,0,0,0)
def step(s,e):
 a=list(s);x,y,yes,live,mem,owner,epoch,phase,k0,k1,r0,r1=s
 alive=lambda p: bool(live&(1<<(p+1)))
 running=bool(live&(1<<owner))
 if e==15:return s
 if 11<=e<=13:
  bit=1<<(e-11)
  if not live&bit:return None
  a[3]&=~bit;return tuple(a)
 if e==14:
  newmem=(live>>1)&3
  if not newmem or (running and mem==newmem):return None
  a[4]=newmem;a[5]=1 if newmem&1 else 2;a[6]+=1;a[7]=1;a[8:]=[0]*4
  return tuple(a)
 if e in (0,1):
  p=e
  if not running or not mem&(1<<p) or s[8+p]!=0:return None
  # deterministic sequential multicast, individual sends
  if p==1 and mem&1 and k0==0:return None
  a[8+p]=1;return tuple(a)
 if 2<=e<=5:
  p=(e-2)//2;negative=bool((e-2)%2)
  if not alive(p) or s[8+p]!=1:return None
  if negative and phase!=0:return None
  if phase==0:
   if s[p]!=0:return None
   a[p]=4 if negative else 1
   if not negative:a[2]|=1<<p
  elif phase==2:
   if s[p] not in (1,2,3):return None
   if s[p]!=3:a[p]=2
  elif phase==4:
   if s[p] not in (2,3):return None
   a[p]=3
  elif phase==5:
   if s[p]==3:return None
   a[p]=4
  a[8+p]=2;return tuple(a)
 if e in (6,7):
  p=e-6
  if not alive(p) or s[8+p]!=2:return None
  a[8+p]=3;a[10+p]=s[p];return tuple(a)
 if e in (8,9):
  p=e-8
  if not running or s[8+p]!=3:return None
  a[8+p]=4;return tuple(a)
 if e==10:
  if not running or not all(not mem&(1<<p) or s[8+p]==4 for p in (0,1)):return None
  if phase==0:a[7]=2 if r0==1 and r1==1 else 5
  elif phase==1:a[7]=2 if any(mem&(1<<p) and s[10+p] in (2,3) for p in (0,1)) else 3
  elif phase==2:a[7]=4
  elif phase==3:a[7]=5
  else:return None
  a[8:]=[0]*4;return tuple(a)
 return None
def safe(s):
 return not (3 in s[:2] and 4 in s[:2]) and (not any(x in (2,3) for x in s[:2]) or s[2]==3)


def enumerate_states():
    seen = {INITIAL}
    queue = deque([INITIAL])
    while queue:
        state = queue.popleft()
        for event in range(16):
            target = step(state, event)
            if target is not None and target not in seen:
                seen.add(target)
                queue.append(target)
    return seen


def candidate_definitions(states):
    weights = [1, 5, 25, 100, 800, 3200, 9600, 28800, 172800, 864000, 4320000, 21600000]
    codes = sorted(sum(a * b for a, b in zip(state, weights)) for state in states)
    parts = []

    def raw(values, indent=2):
        if not values:
            return ".empty"
        middle = len(values) // 2
        space = " " * indent
        return (f"(.node {values[middle]}\n{space}{raw(values[:middle], indent + 2)}"
                f"\n{space}{raw(values[middle + 1:], indent + 2)})")

    def split(values, indent=2):
        if len(values) <= 64:
            index = len(parts)
            parts.append(values)
            return f"certificatePart{index}"
        middle = len(values) // 2
        space = " " * indent
        return (f"(.node {values[middle]}\n{space}{split(values[:middle], indent + 2)}"
                f"\n{space}{split(values[middle + 1:], indent + 2)})")

    expression = split(codes)
    result = "".join(f"def certificatePart{i} : CodeTree :=\n  {raw(values)}\n\n"
                     for i, values in enumerate(parts))
    return result + f"def certificate : CodeTree :=\n  {expression}\n\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    source = (root / "Verification/DistributedThreePhaseCommitCertificate.lean").read_text()
    actual = source[source.index("def certificatePart0"):source.index("def certifiedBool")]
    states = enumerate_states()
    if actual != candidate_definitions(states):
        raise SystemExit("Candidate certificate differs; regenerate and kernel-check its proof blocks.")
    print(f"Candidate data match: {len(states)} states. This is not a formal Python verification.")


if __name__ == "__main__":
    main()
