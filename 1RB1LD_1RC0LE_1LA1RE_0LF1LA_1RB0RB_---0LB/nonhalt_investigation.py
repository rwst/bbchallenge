#!/usr/bin/env python3
"""Investigate: can we prove nonhalt without schemata?

Halt condition: F reads 0.  F is reached from D,0→0LF.  So halt iff when
D fires on a 0, the cell L of D is also 0.

Sufficient conditions for nonhalt (from weakest to strongest):
  (W1) Whenever D is on 0 (about to fire), cell L of D is 1.
  (W2) Tape's non-blank region always has ≥ 2 "blocks" when D is active.
  (W3) Leftmost 1 position monotonically decreases (never moves right).
  (W4) Tape has no "00" pattern in D's sweep region.

Test each empirically over a long run to see if it holds.
"""
import os, resource, sys, time
from collections import Counter

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STATE_NAMES, NEXT, WRITE, DIR


def count_blocks(t):
    blocks = []
    cur = 0
    for i in range(t.lo, t.hi + 1):
        if t.arr[i] == 1:
            cur += 1
        else:
            if cur > 0:
                blocks.append(cur); cur = 0
    if cur > 0:
        blocks.append(cur)
    return blocks


def current_leftmost_1(t):
    """Position of leftmost 1 CURRENTLY on tape (not ever-written)."""
    for i in range(t.lo, t.hi + 1):
        if t.arr[i] == 1:
            return i
    return None


def has_double_zero_in_nonblank(t):
    """True if tape has '00' pattern in [lo, hi] (non-blank region)."""
    for i in range(t.lo, t.hi):
        if t.arr[i] == 0 and t.arr[i+1] == 0:
            return True
    return False


def investigate(max_steps=10**7, time_budget=60):
    t = FastTape()
    # Run initial 59 steps to reach first macro event
    for _ in range(59):
        if t.halted: break
        t.step_one()
    start = time.monotonic()

    min_blocks_seen = float('inf')
    max_blocks_seen = 0
    leftmost1_changes = 0
    leftmost1_moved_right = 0  # BAD: violates W3
    prev_leftmost = current_leftmost_1(t)
    D_fires = 0
    D_L_was_0 = 0  # Equivalent to "F about to halt"
    D_L_was_blank = 0  # Even worse (past blank boundary)
    double_zero_count = 0
    steps_tracked = 0

    while t.steps < max_steps:
        if t.halted:
            print(f"HALT at step {t.steps}")
            break
        steps_tracked += 1
        # Check W3: leftmost 1 monotonic non-increasing
        cur_lm = current_leftmost_1(t)
        if cur_lm is not None and prev_leftmost is not None:
            if cur_lm > prev_leftmost:
                leftmost1_moved_right += 1
            if cur_lm != prev_leftmost:
                leftmost1_changes += 1
        prev_leftmost = cur_lm

        # Check W2: block count at each E-turnaround
        if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = count_blocks(t)
            n = len(blocks)
            if n < min_blocks_seen: min_blocks_seen = n
            if n > max_blocks_seen: max_blocks_seen = n

        # Check W1: when D is about to fire (D, head=0)
        if t.state == 2 and t.arr[t.hp] == 0:  # state D on 0
            D_fires += 1
            # Cell L of D's current head
            if t.hp - 1 >= 0:
                l_cell = t.arr[t.hp - 1]
                # "blank" = outside lo/hi means never written, so value 0 but stable
                is_blank_L = (t.hp - 1 < t.lo)
                if l_cell == 0:
                    D_L_was_0 += 1
                if is_blank_L:
                    D_L_was_blank += 1

        # Check W4: double zero in non-blank region
        if has_double_zero_in_nonblank(t):
            double_zero_count += 1

        if time.monotonic() - start > time_budget:
            break
        t.step_one()

    elapsed = time.monotonic() - start
    print(f"Final step: {t.steps:,}  elapsed: {elapsed:.1f}s  steps_tracked: {steps_tracked:,}")
    print()
    print(f"W1: D fires on 0 total: {D_fires:,}")
    print(f"    Of these, cell L was 0: {D_L_was_0}  (any = would halt!)")
    print(f"    Of these, cell L was blank: {D_L_was_blank}")
    print()
    print(f"W2: At E-turnarounds: min blocks = {min_blocks_seen}, max = {max_blocks_seen}")
    print(f"    (W2 violated iff min < 2)")
    print()
    print(f"W3: Leftmost-1 changes: {leftmost1_changes:,}  moved RIGHT (violations): {leftmost1_moved_right:,}")
    print(f"    (W3 violated iff any rightward moves — means a leftmost 1 was erased)")
    print()
    print(f"W4: Steps with double-0 in non-blank region: {double_zero_count:,}")
    print(f"    Fraction: {100*double_zero_count/steps_tracked:.1f}% of tracked steps")


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 5_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    investigate(ms, tb)
