#!/usr/bin/env python3
"""Identify repeating micro-patterns in the trace."""

import sys
from sim import Tape, STATE_NAMES


def cycle_summary(n):
    """Count lengths of maximal same-state runs, and transitions between states."""
    from collections import Counter
    t = Tape()
    prev_state = None
    run_len = 0
    state_runs = Counter()   # (state) -> list of run lengths
    transitions = Counter()  # (s1, s2)
    while t.steps < n:
        if t.halted: break
        s = STATE_NAMES[t.state]
        if s == prev_state:
            run_len += 1
        else:
            if prev_state is not None:
                state_runs[(prev_state, run_len)] += 1
                transitions[(prev_state, s)] += 1
            prev_state = s
            run_len = 1
        t.step()
    if prev_state is not None:
        state_runs[(prev_state, run_len)] += 1
    return state_runs, transitions


def triples(n, limit=30):
    """Most common (state, sym-at-head-minus-1, sym-at-head, sym-at-head-plus-1) triples."""
    from collections import Counter
    c = Counter()
    t = Tape()
    while t.steps < n:
        if t.halted: break
        sl = t.arr[t.hp - 1] if t.hp > 0 else 0
        sh = t.arr[t.hp]
        sr = t.arr[t.hp + 1] if t.hp + 1 < len(t.arr) else 0
        c[(STATE_NAMES[t.state], sl, sh, sr)] += 1
        t.step()
    for k, v in sorted(c.items(), key=lambda x: -x[1])[:limit]:
        print(f"{k}: {v}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "summary"
    if cmd == "summary":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
        runs, trans = cycle_summary(n)
        print("=== State-run-length distribution (top 30) ===")
        for k, v in sorted(runs.items(), key=lambda x: -x[1])[:30]:
            print(f"  state={k[0]} len={k[1]}: {v}")
        print("=== State transitions (top 30) ===")
        for k, v in sorted(trans.items(), key=lambda x: -x[1])[:30]:
            print(f"  {k[0]}->{k[1]}: {v}")
    elif cmd == "triples":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
        triples(n)
