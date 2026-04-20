#!/usr/bin/env python3
"""Trace from blank, print every time state=E, head on 0, past rightmost 1."""
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

t = Tape2()
for step in range(1, 2000):
    t.step()
    if t.halted:
        print(f"step {step}: HALT"); break
    if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
        res = t.extract_A()
        print(f"step {step}: {pretty(t)}  extract={res}")
