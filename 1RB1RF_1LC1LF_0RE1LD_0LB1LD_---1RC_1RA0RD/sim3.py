#!/usr/bin/env python3
"""Extract sequence of C-at-left-edge macro configs: 0^inf [C] (01)^z 1^m 0^p."""

import re
from sim import Tape, TM


def extract_C_macro(t):
    """If tape is 0^inf [C] (01)^z 1^m 0^p with C at leftmost 1-reach, return (z, m, p)."""
    if t.state != 'C':
        return None
    # Head must be at left edge (leftmost visited, which means no 1s to the left and the cell read is the leftmost "active")
    # Check: all of left is 0 (blank)
    if any(s != 0 for s in t.left):
        return None
    # Right should start with 0101...01 followed by 1...1 0...0
    r = t.right
    # Find zebra length
    z = 0
    i = 0
    while i + 1 < len(r) and r[i] == 0 and r[i+1] == 1:
        # Could be part of zebra or start of "01" that ends zebra
        # Zebra ends when we see `11` (i.e. next pair starts with 1)
        # Actually zebra is "01010101" so at position 2i we expect 0, 2i+1 we expect 1
        if i + 2 < len(r) and r[i+2] == 1:
            # next is 11 → end of zebra
            z += 1
            i += 2
            break
        z += 1
        i += 2
    # Count ones
    m = 0
    while i < len(r) and r[i] == 1:
        m += 1
        i += 1
    # Remaining must all be 0
    if any(s != 0 for s in r[i:]):
        return None
    return (z, m)


def run_extract(max_steps=2000000):
    t = Tape()
    events = []
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            return events, step, True
        # Record when at left edge in state C
        if t.state == 'C' and t.pos == t.minpos:
            mc = extract_C_macro(t)
            if mc is not None:
                z, m = mc
                events.append((step+1, z, m, t.length()))
    return events, max_steps, False


if __name__ == '__main__':
    import sys
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 500000
    events, steps, halted = run_extract(n)
    print(f"Steps: {steps}, halted: {halted}, events: {len(events)}")
    print()
    print(f"{'step':>8}  {'z':>4}  {'m':>5}  {'len':>5}  {'(len)':>5}  delta_step  parity")
    prev = 0
    for step, z, m, L in events[:200]:
        d = step - prev
        parity = 'even' if m % 2 == 0 else 'odd'
        print(f"{step:8d}  {z:4d}  {m:5d}  {L:5d}  {2*z+m:5d}  {d:10d}  {parity}")
        prev = step
