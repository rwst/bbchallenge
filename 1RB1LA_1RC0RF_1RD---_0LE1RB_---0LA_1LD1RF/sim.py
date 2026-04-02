#!/usr/bin/env python3
"""Simulator for TM 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF (6-state 2-symbol)."""

import argparse
from collections import defaultdict

# Transition table: (state, symbol) -> (write, move, new_state)
# States: A=0, B=1, C=2, D=3, E=4, F=5. Symbols: 0,1. Move: R=+1, L=-1.
RULES = {
    (0, 0): (1, +1, 1),  # A,0 -> 1RB
    (0, 1): (1, -1, 0),  # A,1 -> 1LA

    (1, 0): (1, +1, 2),  # B,0 -> 1RC
    (1, 1): (0, +1, 5),  # B,1 -> 0RF

    (2, 0): (1, +1, 3),  # C,0 -> 1RD
    # (2, 1): undefined    # C,1 -> ---

    (3, 0): (0, -1, 4),  # D,0 -> 0LE
    (3, 1): (1, +1, 1),  # D,1 -> 1RB

    # (4, 0): undefined    # E,0 -> ---
    (4, 1): (0, -1, 0),  # E,1 -> 0LA

    (5, 0): (1, -1, 3),  # F,0 -> 1LD
    (5, 1): (1, +1, 5),  # F,1 -> 1RF
}

STATE_NAME = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F'}


def tape_str(tape, head, width=40):
    """Render tape around head position."""
    lo = head - width
    hi = head + width
    chars = []
    for i in range(lo, hi + 1):
        s = str(tape[i])
        if i == head:
            s = f'[{s}]'
        chars.append(s)
    return ''.join(chars)


def rle_tape(tape):
    """Run-length encode the nonzero portion of tape."""
    positions = [k for k, v in tape.items() if v != 0]
    if not positions:
        return "empty"
    lo, hi = min(positions), max(positions)
    result = []
    i = lo
    while i <= hi:
        v = tape[i]
        count = 1
        while i + count <= hi and tape[i + count] == v:
            count += 1
        if count > 1:
            result.append(f"{v}^{count}")
        else:
            result.append(str(v))
        i += count
    return ' '.join(result)


def tape_summary(tape):
    """Count symbols on tape."""
    counts = defaultdict(int)
    for v in tape.values():
        if v != 0:
            counts[v] += 1
    return dict(sorted(counts.items()))


def get_tape_range(tape):
    """Return (lo, hi) of nonzero tape cells."""
    positions = [k for k, v in tape.items() if v != 0]
    if not positions:
        return 0, 0
    return min(positions), max(positions)


def simulate(max_steps, verbose=False, snapshot_interval=None, trace=False,
             head_track=False):
    tape = defaultdict(int)
    head = 0
    state = 0

    head_min, head_max = 0, 0

    for step in range(1, max_steps + 1):
        sym = tape[head]
        key = (state, sym)

        if key not in RULES:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={sym} "
                  f"(undefined transition)")
            lo, hi = get_tape_range(tape)
            print(f"Tape summary: {tape_summary(tape)}")
            print(f"Head={head}, tape range=[{lo},{hi}]")
            print(f"RLE: {rle_tape(tape)}")
            return tape, head, state, step

        write, move, new_state = RULES[key]

        if trace:
            print(f"step={step} state={STATE_NAME[state]} sym={sym} -> "
                  f"write={write} move={'R' if move > 0 else 'L'} "
                  f"new={STATE_NAME[new_state]} head={head}")

        tape[head] = write
        head += move
        state = new_state

        if head < head_min:
            head_min = head
        if head > head_max:
            head_max = head

        if snapshot_interval and step % snapshot_interval == 0:
            lo, hi = get_tape_range(tape)
            tape_len = (hi - lo + 1) if lo != hi or tape[lo] != 0 else 0
            summary = tape_summary(tape)
            print(f"step={step:>12} head={head:>8} state={STATE_NAME[state]} "
                  f"len={tape_len:>8} syms={summary}")

        if verbose and step <= 200:
            print(f"step={step:>6} {STATE_NAME[state]} head={head:>4} | "
                  f"{tape_str(tape, head, 30)}")

    print(f"\nRan {max_steps} steps without halting.")
    lo, hi = get_tape_range(tape)
    if lo != hi or tape[lo] != 0:
        tape_len = hi - lo + 1
        print(f"Tape length: {tape_len}, head={head}, state={STATE_NAME[state]}")
        print(f"Head range: [{head_min}, {head_max}]")
        print(f"Tape summary: {tape_summary(tape)}")
        print(f"RLE: {rle_tape(tape)}")

    return tape, head, state, max_steps


def macro_analyze(max_steps):
    """Track macro-level behavior: state visits, tape structure changes,
    head direction reversals, and recurring configurations."""
    tape = defaultdict(int)
    head = 0
    state = 0

    prev_tape_len = 0
    prev_head_dir = 0  # +1 right, -1 left

    # Track configurations for cycle detection
    config_history = {}  # (state, head_relative, tape_hash) -> step

    # Track when head reaches new extremes
    head_min, head_max = 0, 0
    growth_events = []

    # Track state at direction reversals (head bounces)
    reversal_events = []
    prev_head = 0

    # Track canonical tape snapshots
    canonical_snapshots = []

    for step in range(1, max_steps + 1):
        sym = tape[head]
        key = (state, sym)
        if key not in RULES:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={sym}")
            lo, hi = get_tape_range(tape)
            print(f"RLE: {rle_tape(tape)}")
            print(f"Head={head}, range=[{lo},{hi}]")
            break

        write, move, new_state = RULES[key]
        tape[head] = write
        old_head = head
        head += move
        state = new_state

        # Detect tape growth
        if head < head_min:
            head_min = head
            lo, hi = get_tape_range(tape)
            tape_len = hi - lo + 1
            growth_events.append((step, 'L', tape_len, STATE_NAME[state]))
        if head > head_max:
            head_max = head
            lo, hi = get_tape_range(tape)
            tape_len = hi - lo + 1
            growth_events.append((step, 'R', tape_len, STATE_NAME[state]))

        # Detect head direction reversals
        cur_dir = head - old_head
        if cur_dir != prev_head_dir and prev_head_dir != 0:
            direction = 'R->L' if prev_head_dir > 0 and cur_dir < 0 else 'L->R'
            reversal_events.append((step, direction, STATE_NAME[state], head))
        prev_head_dir = cur_dir

        # Periodic canonical snapshots
        if step % 1000 == 0 or step <= 100:
            lo, hi = get_tape_range(tape)
            tape_len = hi - lo + 1 if (lo != hi or tape[lo] != 0) else 0
            canonical_snapshots.append((step, STATE_NAME[state], head, tape_len,
                                        rle_tape(tape)))

    # Print growth events
    print("=== TAPE GROWTH EVENTS (first 100) ===")
    print(f"{'step':>10} {'side':>4} {'len':>5} {'state':>5}")
    for step, side, tlen, st in growth_events[:100]:
        print(f"{step:>10} {side:>4} {tlen:>5} {st:>5}")

    # Print direction reversals (sampled)
    print(f"\n=== HEAD REVERSALS (total: {len(reversal_events)}, showing first 50) ===")
    print(f"{'step':>10} {'dir':>5} {'state':>5} {'head':>6}")
    for step, direction, st, h in reversal_events[:50]:
        print(f"{step:>10} {direction:>5} {st:>5} {h:>6}")

    # Print canonical snapshots
    print(f"\n=== TAPE SNAPSHOTS ===")
    for step, st, h, tlen, rle in canonical_snapshots[:50]:
        print(f"step={step:>10} state={st} head={h:>6} len={tlen:>5} | {rle[:120]}")

    # Summary
    print(f"\n=== SUMMARY ===")
    print(f"Steps simulated: {step}")
    print(f"Head range: [{head_min}, {head_max}]")
    print(f"Growth events: {len(growth_events)}")
    print(f"Reversals: {len(reversal_events)}")


def sweep_analyze(max_steps):
    """Analyze sweep patterns: detect when head completes full left-right sweeps."""
    tape = defaultdict(int)
    head = 0
    state = 0

    # Track sweep turnaround points
    head_min_seen, head_max_seen = 0, 0
    local_min, local_max = 0, 0
    sweeps = []
    prev_dir = 0
    sweep_start_step = 0

    for step in range(1, max_steps + 1):
        sym = tape[head]
        key = (state, sym)
        if key not in RULES:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={sym}")
            lo, hi = get_tape_range(tape)
            print(f"RLE: {rle_tape(tape)}")
            break

        write, move, new_state = RULES[key]
        tape[head] = write
        old_head = head
        head += move
        state = new_state

        cur_dir = head - old_head

        if head < head_min_seen:
            head_min_seen = head
        if head > head_max_seen:
            head_max_seen = head

        # Detect turnaround
        if cur_dir != prev_dir and prev_dir != 0:
            sweep_len = step - sweep_start_step
            if prev_dir > 0:  # was going right, now left
                sweeps.append((step, 'R->L', head, sweep_len, STATE_NAME[state]))
            else:  # was going left, now right
                sweeps.append((step, 'L->R', head, sweep_len, STATE_NAME[state]))
            sweep_start_step = step
        prev_dir = cur_dir

    # Analyze sweep patterns
    print(f"=== SWEEP TURNAROUNDS (total: {len(sweeps)}) ===")
    print(f"{'step':>10} {'turn':>5} {'head':>6} {'len':>6} {'state':>5}")
    for step, turn, h, slen, st in sweeps[:80]:
        print(f"{step:>10} {turn:>5} {h:>6} {slen:>6} {st:>5}")

    if len(sweeps) > 80:
        print(f"  ... ({len(sweeps) - 80} more)")

    # Look for patterns in sweep lengths
    print(f"\n=== SWEEP LENGTH SEQUENCES ===")
    r2l_lens = [s[3] for s in sweeps if s[1] == 'R->L']
    l2r_lens = [s[3] for s in sweeps if s[1] == 'L->R']
    print(f"R->L sweep lengths (first 40): {r2l_lens[:40]}")
    print(f"L->R sweep lengths (first 40): {l2r_lens[:40]}")

    # Look for ratios
    if len(r2l_lens) > 2:
        ratios = [r2l_lens[i]/r2l_lens[i-1] for i in range(1, min(20, len(r2l_lens)))
                  if r2l_lens[i-1] > 0]
        print(f"R->L ratios: {[f'{r:.3f}' for r in ratios]}")
    if len(l2r_lens) > 2:
        ratios = [l2r_lens[i]/l2r_lens[i-1] for i in range(1, min(20, len(l2r_lens)))
                  if l2r_lens[i-1] > 0]
        print(f"L->R ratios: {[f'{r:.3f}' for r in ratios]}")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Simulate TM 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF')
    parser.add_argument('-n', '--steps', type=int, default=10000,
                        help='Max steps (default: 10000)')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Show first 200 steps tape')
    parser.add_argument('-t', '--trace', action='store_true',
                        help='Print every transition')
    parser.add_argument('-s', '--snapshot', type=int, default=None,
                        help='Print summary every N steps')
    parser.add_argument('--head-track', action='store_true',
                        help='Track head positions')
    parser.add_argument('--macro', action='store_true',
                        help='Macro-level analysis')
    parser.add_argument('--sweep', action='store_true',
                        help='Sweep pattern analysis')
    args = parser.parse_args()

    if args.macro:
        macro_analyze(args.steps)
    elif args.sweep:
        sweep_analyze(args.steps)
    else:
        simulate(args.steps, verbose=args.verbose, snapshot_interval=args.snapshot,
                 trace=args.trace, head_track=args.head_track)
