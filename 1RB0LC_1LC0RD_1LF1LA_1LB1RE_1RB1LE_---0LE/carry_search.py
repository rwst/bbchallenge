#!/usr/bin/env python3
"""Hunt for local carry rules by running the machine from synthetic
starting configurations with different left prefixes.  If two runs
with the same right-end pattern produce the same transformation (up
to the unchanged left prefix), the rule is local."""

import sys
from sim import Tape, TR, STATE_NAMES


def make_tape(left_tape, head_sym, right_tape, state):
    """Build a Tape initialized with the given non-blank region.
    `left_tape` is reversed (head-to-far), `right_tape` is forward."""
    t = Tape(cap=1 << 16)
    mid = len(t.arr) // 2
    t.hp = int(mid)
    t.arr[t.hp] = int(head_sym)
    for i, s in enumerate(left_tape):
        t.arr[t.hp - 1 - i] = int(s)
    for i, s in enumerate(right_tape):
        t.arr[t.hp + 1 + i] = int(s)
    t.lo = t.hp - len(left_tape)
    t.hi = t.hp + len(right_tape)
    t.state = int(state)
    t.steps = 0
    t.halted = False
    return t


def find_right_blank_events(t, max_steps, max_events=40):
    """Track E-right-blank events and return (step_count, blocks)."""
    out = []
    prev = t.steps
    while t.steps - prev + (prev) < max_steps + prev and len(out) < max_events:
        if t.halted:
            out.append(('HALT', t.steps))
            break
        if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = t.blocks_between(min(t.lo, t.hp), max(t.hi, t.hp))
            out.append((t.steps, blocks))
        t.step()
    return out


def snapshot_blocks(t):
    return t.blocks_between(min(t.lo, t.hp), max(t.hi, t.hp))


def test_locality(left_pattern, head_sym, right_pattern, state, n_steps, label=""):
    """Run the machine from a constructed tape and record what happens."""
    t = make_tape(left_pattern, head_sym, right_pattern, state)
    initial_blocks = snapshot_blocks(t)
    initial_hp = t.hp
    for _ in range(n_steps):
        if t.halted:
            print(f"[{label}] halted at step {t.steps}")
            return
        t.step()
    final_blocks = snapshot_blocks(t)
    print(f"[{label}] after {n_steps} steps: blocks {initial_blocks} → {final_blocks}, "
          f"state={STATE_NAMES[t.state]} sym={t.arr[t.hp]} hp_offset={t.hp - initial_hp}")


def intermediate_events(start_step, max_steps):
    """From blank, run start_step steps (discard), then track all E-right-blank
    events in the next max_steps steps."""
    t = Tape()
    for _ in range(start_step):
        t.step()
    prev = t.steps
    print(f"Starting at step {t.steps}, tracking next {max_steps} steps")
    # Include the current state as event if it qualifies
    if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
        print(f"  step {t.steps:6d} (dt={t.steps - prev:6d}): {snapshot_blocks(t)}")
        prev = t.steps
    while t.steps < start_step + max_steps:
        t.step()
        if t.halted: break
        if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
            print(f"  step {t.steps:6d} (dt={t.steps - prev:6d}): {snapshot_blocks(t)}")
            prev = t.steps


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "help"

    if cmd == "inter":
        # Look for intermediate E-right-blank events between 190 and 752
        start = int(sys.argv[2]) if len(sys.argv) > 2 else 190
        extent = int(sys.argv[3]) if len(sys.argv) > 3 else 800
        intermediate_events(start, extent)

    elif cmd == "locality":
        # Test: does [..., 2, K, 2, 1] start transform the same regardless of "..."?
        # We'll put different left prefixes and check the post-114 step count.
        K = int(sys.argv[2]) if len(sys.argv) > 2 else 10
        n_steps = int(sys.argv[3]) if len(sys.argv) > 3 else 1000

        # R4_Config blank∞ K base: L = blank.
        # Tape L-to-R: 0* 1 1 0 1^K 0 1 1 0 1 [E=0] blank
        # left_tape (head-to-far): [1, 0, 1, 1, 0, 1^K, 0, 1, 1]
        base_left = [1, 0, 1, 1, 0] + [1]*K + [0, 1, 1]
        print(f"=== Testing R4_Config variant K={K} ===")
        # Variant A: blank L
        test_locality(base_left + [0]*5, 0, [], 4, n_steps, "blank")
        # Variant B: L = some 1s then blank
        test_locality(base_left + [0, 1, 1], 0, [], 4, n_steps, "mixed-1s")
        # Variant C: L = pure 1s
        test_locality(base_left + [1, 1, 1, 1, 1], 0, [], 4, n_steps, "ones-only")
        # Variant D: L = zebra pattern
        test_locality(base_left + [1, 0, 1, 0, 1, 0, 1], 0, [], 4, n_steps, "zebra")

    elif cmd == "scanK":
        # For each K starting from 2, build R4_Config blank K and run until
        # next E-right-blank event (or bound).  Print the dt and final blocks.
        Kmin = int(sys.argv[2]) if len(sys.argv) > 2 else 2
        Kmax = int(sys.argv[3]) if len(sys.argv) > 3 else 40
        max_steps = int(sys.argv[4]) if len(sys.argv) > 4 else 20000
        for K in range(Kmin, Kmax + 1):
            base_left = [1, 0, 1, 1, 0] + [1]*K + [0, 1, 1]
            t = make_tape(base_left, 0, [], 4)
            initial = snapshot_blocks(t)
            steps_to_next = None
            for _ in range(max_steps):
                t.step()
                if t.halted:
                    print(f"K={K:3d}: HALT at dt={t.steps}")
                    break
                if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
                    steps_to_next = t.steps
                    break
            if steps_to_next is not None:
                final = snapshot_blocks(t)
                print(f"K={K:3d}: dt={steps_to_next:6d} blocks {initial} → {final}")
            elif not t.halted:
                print(f"K={K:3d}: no event in {max_steps} steps")

    elif cmd == "help":
        print("Commands:")
        print("  inter [start] [extent]  — find E-right-blank events in window")
        print("  locality [K] [n]        — test locality of R4_Config K transformations")
        print("  scanK [Kmin] [Kmax] [max_steps] — sweep over K in R4_Config blank K")
