#!/usr/bin/env python3
"""Trace from A(1,2) and see when we reach the next E-macro config."""
import resource
resource.setrlimit(resource.RLIMIT_AS, (2*1024**3, 2*1024**3))

from sim import Tape2, STATE_NAMES, STE

def pretty(t, window=None):
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
a, b = (int(sys.argv[1]), int(sys.argv[2])) if len(sys.argv) > 2 else (1, 2)
max_steps = int(sys.argv[3]) if len(sys.argv) > 3 else 200

t = Tape2()
t.set_from_A(a, b)
print(f"init A({a},{b}): {pretty(t)}")
print(f"  extract = {t.extract_A()}")
for step in range(1, max_steps):
    t.step()
    if t.halted:
        print(f"step {step}: HALT"); break
    if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
        res = t.extract_A()
        tag = f"  << A{res}" if res else ""
        print(f"step {step}: {pretty(t)}{tag}")
        if res: break
    elif step < 20 or step % 50 == 0:
        print(f"step {step}: {pretty(t)}")
