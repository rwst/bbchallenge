#!/usr/bin/env python3
"""Detailed trace of A(α, β) for small values, to identify shift patterns."""
import resource
resource.setrlimit(resource.RLIMIT_AS, (2*1024**3, 2*1024**3))

from sim import Tape2, STATE_NAMES, STE

def pretty(t):
    lo = min(t.lo, t.hp) - 1
    hi = max(t.hi, t.hp) + 1
    s = []
    for i in range(lo, hi+1):
        c = str(t.arr[i])
        if i == t.hp:
            c = f"[{STATE_NAMES[t.state]}]{c}"
        s.append(c)
    return "".join(s)

import sys
a, b = int(sys.argv[1]), int(sys.argv[2])
n = int(sys.argv[3]) if len(sys.argv) > 3 else 60

t = Tape2()
t.set_from_A(a, b)
print(f"init A({a},{b}): {pretty(t)}")
for step in range(1, n+1):
    t.step()
    if t.halted:
        print(f"step {step}: HALT")
        break
    print(f"step {step:3d}: {pretty(t)}")
