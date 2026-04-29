#!/usr/bin/env python3
"""Audit specific config patterns for axiom-producer detection.

R1 = M([], 3, R) requires a producer M([2], 3, d::R) via sweep_and_shift.
R2 = M0(a::L, [r+3, 1, 2]) requires a producer with R = [r+3, 1, 2] structure.

This script runs the macro simulator and logs:
  - Every M([2], 3, ...) config (would produce R1 on next step)
  - Every M0(_, [_, 1, 2]) config (would be R2 directly)
  - First c=3 with single-element L = [a] for various a values
"""
import sys
sys.path.insert(0, '.')
from macro_sim import (
    Macro, INIT_MACRO, INIT_RAW, macro_step,
    AXIOM_R1, AXIOM_R2, AXIOM_R3, HALT,
    bridge_axiom, classify_axiom,
)
from collections import Counter, defaultdict
import argparse


def audit(max_macro_steps):
    m = INIT_MACRO.copy()
    raw = INIT_RAW
    macro_count = 0

    # Stats
    near_R1 = []  # M([a], 3, R) for various a, especially a=2
    L_at_c3 = Counter()  # multiset of L values when c=3
    near_R2 = []  # M0(_, [_, 1, 2])
    last_2_in_R = Counter()  # how often R ends in 2 at M0 entry

    while macro_count < max_macro_steps:
        macro_count += 1

        # Audit BEFORE applying macro_step
        if m.kind == 'M' and m.c == 3:
            L_tuple = tuple(m.L) if len(m.L) <= 3 else ('len',len(m.L))
            L_at_c3[L_tuple] += 1
            if m.L == [2]:
                near_R1.append({'macro_step': macro_count, 'raw_step': raw, 'config': str(m)})

        if m.kind == 'M0' and len(m.R) >= 3 and m.R[-1] == 2 and m.R[-2] == 1:
            near_R2.append({'macro_step': macro_count, 'raw_step': raw, 'config': str(m), 'R': list(m.R)})

        if m.kind == 'M0' and m.R and m.R[-1] == 2:
            last_2_in_R[len(m.R)] += 1

        result, steps, _ = macro_step(m)

        if result is None or result == HALT:
            break
        if result in (AXIOM_R1, AXIOM_R2, AXIOM_R3):
            m_new, k, halted = bridge_axiom(m)
            if m_new is None or halted:
                break
            raw += k
            m = m_new
            continue
        m = result
        raw += steps

    print(f"Audit over {macro_count:,} macro steps, ~{raw:,} raw")
    print()

    print(f"=== near_R1: M([2], 3, R) configs (sweep_and_shift would produce R1) ===")
    print(f"Total: {len(near_R1)}")
    for e in near_R1[:5]:
        print(f"  {e}")
    if len(near_R1) > 5:
        print(f"  ... {len(near_R1)-5} more")

    print()
    print(f"=== L distribution at M(L, 3, _) (c=3 cases) ===")
    for L, n in L_at_c3.most_common(15):
        print(f"  L={L}: {n}")

    print()
    print(f"=== near_R2: M0(_, [..., 1, 2]) configs ===")
    print(f"Total: {len(near_R2)}")
    for e in near_R2[:5]:
        print(f"  {e}")
    if len(near_R2) > 5:
        print(f"  ... {len(near_R2)-5} more")

    print()
    print(f"=== |R| distribution when R ends in 2 (M0 only) ===")
    for n, count in sorted(last_2_in_R.items()):
        print(f"  |R|={n}: {count}")


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('-n', '--macro-steps', type=int, default=100000)
    args = p.parse_args()
    audit(args.macro_steps)
