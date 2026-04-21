#!/usr/bin/env python3
"""Stress-test the sᵢ ≡ 2 (mod 3) invariant across several event types.

Check at:
  (1) E-turnarounds (state E, head on 0 past rightmost 1) — canonical events.
  (2) B-turnarounds, C-turnarounds — other states at right boundary.
  (3) Every time head leaves-and-returns-to the leftmost blank (left
      boundary events).

For each, parse blocks and check sᵢ ≡ 2 (mod 3).

Also track the rare case where the tape has an anomalous pattern.
"""

import os, resource, sys, time
from collections import Counter
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STE, STATE_NAMES, TR


def extract_blocks(t, up_to=None):
    """Parse all runs of 1s on the non-blank portion of tape (left of head).
    If up_to given, parse up to that position."""
    end = t.hp if up_to is None else up_to
    blocks = []
    cur = 0
    for i in range(t.lo, end):
        if t.arr[i] == 1:
            cur += 1
        else:
            if cur > 0:
                blocks.append(cur)
                cur = 0
    if cur > 0:
        blocks.append(cur)
    return blocks


def stress(max_steps, time_budget):
    t = FastTape()
    mod3 = [Counter() for _ in range(6)]  # one per state
    violations_by_state = [0] * 6
    max_block = 0
    events_E_turnaround = 0
    events_at_rightmost = 0  # any state, head past hi on 0
    events_at_leftmost = 0   # any state, head at lo
    start = time.monotonic()
    STATE_COUNT = [0] * 6

    while t.steps < max_steps:
        if t.halted:
            print(f"HALT at step {t.steps}")
            break
        STATE_COUNT[t.state] += 1
        # Event: head on 0 past rightmost 1
        if t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = extract_blocks(t, up_to=t.hp)
            if blocks:
                events_at_rightmost += 1
                if t.state == STE:
                    events_E_turnaround += 1
                for s in blocks:
                    r = s % 3
                    mod3[t.state][r] += 1
                    if r != 2:
                        violations_by_state[t.state] += 1
                    if s > max_block:
                        max_block = s
        # Event: head at or past lo, facing 0
        if t.arr[t.hp] == 0 and t.hp <= t.lo:
            blocks = extract_blocks(t)
            if blocks:
                events_at_leftmost += 1

        if time.monotonic() - start > time_budget:
            break
        t.step_one()

    elapsed = time.monotonic() - start
    print(f"\n=== Stress results ===")
    print(f"Steps: {t.steps:,}  elapsed: {elapsed:.1f}s")
    print(f"State counts: " + " ".join(f"{STATE_NAMES[s]}={c:,}" for s, c in enumerate(STATE_COUNT)))
    print(f"Events (head on 0 past hi): {events_at_rightmost:,}")
    print(f"  of which state-E (canonical): {events_E_turnaround:,}")
    print(f"Events (head at leftmost): {events_at_leftmost:,}")
    print(f"Max block size seen at any such event: {max_block}")
    print()
    print("Block size mod 3 distribution by state (at head-on-0-past-rightmost events):")
    for s in range(6):
        c = mod3[s]
        total = sum(c.values())
        if total > 0:
            print(f"  state {STATE_NAMES[s]}: mod0={c[0]:,} mod1={c[1]:,} mod2={c[2]:,}  "
                  f"(total {total:,}, violations {violations_by_state[s]})")
    total_v = sum(violations_by_state)
    print(f"\nTotal violations: {total_v}")


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 100_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    stress(ms, tb)
