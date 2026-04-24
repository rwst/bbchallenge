#!/usr/bin/env python3
"""Shape-schema trace analysis for `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`.

Inspired by `Chaotic6`'s shape_summary.py.  Runs the TM for a long
trajectory and classifies each configuration by a compact "shape
schema": a tuple capturing the TM state, the head symbol, and the
immediate window around the head (left-of-head run, right-of-head run,
blank boundaries).  Prints the frequency distribution of distinct
schemata per state, which is the empirical basis for designing the
`Interm m i` intermediate macro configurations needed for a
Shifty6-style proof of `rule_even` / `rule_odd` / `rule_halt`.

Usage:
  python3 shape_trace.py [config] [steps]

  config:   "R2 k=1" (default) — A(4, 2) → A(6, 0), 282 steps.
            "R2 k=2" — A(6, 2), 654 steps.
            "R3 k=1" — A(5, 1), 374 steps.
            "R4 k=2" — A(6, 1), halts after 561 steps.

  steps:    Override the default step count.
"""

import sim
import sys
from collections import Counter


def classify_window(t, window=6):
    """Extract a compact shape around the head: state, head sym,
    run-length of the 1s and 0s on each side within the window."""
    # Left run-length of 1s
    L1 = 0
    i = t.hp - 1
    while i >= max(0, t.hp - window) and t.arr[i] == 1:
        L1 += 1
        i -= 1
    # After the 1-run, how many 0s (bounded)
    L0 = 0
    while i >= max(0, t.hp - window) and t.arr[i] == 0:
        L0 += 1
        i -= 1
    # Then either more 1s (zebra) or blank boundary
    # For the purposes of schema, summarize: L1, L0, and whether we hit blank/zebra after.
    if i < 0 or i < t.lo:
        L_boundary = "blank"
    elif t.arr[i] == 1:
        L_boundary = "zebra"
    else:
        L_boundary = "blank"

    # Same for right
    R1 = 0
    i = t.hp + 1
    while i <= min(len(t.arr) - 1, t.hp + window) and t.arr[i] == 1:
        R1 += 1
        i += 1
    R0 = 0
    while i <= min(len(t.arr) - 1, t.hp + window) and t.arr[i] == 0:
        R0 += 1
        i += 1
    if i > t.hi or i >= len(t.arr):
        R_boundary = "blank"
    elif t.arr[i] == 1:
        R_boundary = "zebra"
    else:
        R_boundary = "blank"

    head_sym = t.arr[t.hp]
    state = sim.STATE_NAMES[t.state]
    return (state, head_sym, L1, L0, L_boundary, R1, R0, R_boundary)


def run_analysis(setup_fn, dt, label):
    print(f"=== {label} ({dt} steps) ===")
    t = setup_fn()
    schema_by_state = {s: Counter() for s in sim.STATE_NAMES}
    for step in range(dt):
        if t.halted:
            break
        schema = classify_window(t)
        state = schema[0]
        rest = schema[1:]
        schema_by_state[state][rest] += 1
        t.step()
    for state in sim.STATE_NAMES:
        counter = schema_by_state[state]
        total = sum(counter.values())
        if total == 0:
            continue
        print(f"  State {state} ({total} occurrences):")
        top = counter.most_common(10)
        for schema, cnt in top:
            pct = 100.0 * cnt / total
            head_sym, L1, L0, Lb, R1, R0, Rb = schema
            print(f"    head={head_sym} left=[1^{L1},0^{L0},{Lb}] right=[1^{R1},0^{R0},{Rb}]: {cnt} ({pct:.1f}%)")
    print()


CONFIGS = {
    "R2 k=0": (lambda: sim.setup_A(2, 2), 54, "R2 k=0 (A(2,2)→A(3,0))"),
    "R2 k=1": (lambda: sim.setup_A(4, 2), 282, "R2 k=1 (A(4,2)→A(6,0))"),
    "R2 k=2": (lambda: sim.setup_A(6, 2), 654, "R2 k=2 (A(6,2)→A(9,0))"),
    "R3 k=0": (lambda: sim.setup_A(3, 1), 110, "R3 k=0 (A(3,1)→A(4,0))"),
    "R3 k=1": (lambda: sim.setup_A(5, 1), 374, "R3 k=1 (A(5,1)→A(7,0))"),
    "R4 k=1": (lambda: sim.setup_A(4, 1), 226, "R4 k=1 (A(4,1)→halt)"),
}


if __name__ == "__main__":
    key = sys.argv[1] if len(sys.argv) > 1 else "R2 k=1"
    if key == "all":
        for k, (f, dt, lbl) in CONFIGS.items():
            run_analysis(f, dt, lbl)
    elif key in CONFIGS:
        f, dt, lbl = CONFIGS[key]
        if len(sys.argv) > 2:
            dt = int(sys.argv[2])
        run_analysis(f, dt, lbl)
    else:
        print(f"Unknown config: {key}. Available: {list(CONFIGS.keys())}")
