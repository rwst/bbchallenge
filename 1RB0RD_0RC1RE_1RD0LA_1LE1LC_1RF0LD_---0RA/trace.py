#!/usr/bin/env python3
"""Trace macro steps, printing every step with compact tape representation,
identifying state-by-step structure for proof decomposition."""

from sim import setup_C, STATE_NAMES, detect_C_c1, parse_tm, TM_STR, Tape
import sys

def trace_step_by_step(a, b, max_steps=500):
    t = setup_C(a, b)
    print(f"Start C({a},{b})  lo={t.lo} hi={t.hi} hp={t.hp}")
    def show(step):
        cells = []
        lo = max(t.lo - 1, 0)
        hi = min(t.hi + 1, len(t.arr) - 1)
        hp = t.hp
        # Re-center
        window_lo = max(0, hp - 30)
        window_hi = min(len(t.arr) - 1, hp + 10)
        window_lo = max(window_lo, lo - 1)
        window_hi = min(window_hi, hi + 1)
        for i in range(window_lo, window_hi + 1):
            c = str(t.arr[i])
            if i == hp:
                c = f"[{STATE_NAMES[t.state]}]{c}"
            cells.append(c)
        print(f"  s={step:>4} {''.join(cells)}")
    show(0)
    for s in range(1, max_steps + 1):
        t.step()
        show(s)
        if t.halted:
            print("  HALT")
            return
        cfg = detect_C_c1(t)
        if cfg is not None and s > 0:
            print(f"  ** C({cfg[0]},{cfg[1]}) at step {s} **")
            return

if __name__ == "__main__":
    a = int(sys.argv[1]) if len(sys.argv) > 1 else 1
    b = int(sys.argv[2]) if len(sys.argv) > 2 else 3
    m = int(sys.argv[3]) if len(sys.argv) > 3 else 100
    trace_step_by_step(a, b, m)
