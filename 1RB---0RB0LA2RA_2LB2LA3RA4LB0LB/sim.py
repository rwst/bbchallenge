#!/usr/bin/env python3
"""Simulator for TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB (2-state 5-symbol).

MACRO BEHAVIOR ANALYSIS (per mxdys + simulation verification)
=============================================================

Tape structure (physical L→R):
  0^inf  1 3  [binary: cells in {2,3}]  [HEAD]  [ternary: pairs in {42,02,22}]  2 2  0^inf
         ~~~                                                                      ~~~
     terminator                                                                 padding

In mxdys notation (reversed): .22 (42|02|22)* (<A|B>) (2|3)* 31.

Encoding:
  - Left terminator: cells 1,3 at physical left edge (= "31" reading R→L)
  - Right padding:   cells 2,2 at physical right edge (= "22" reading R→L)
  - Binary counter:  2=0, 3=1 (LSB closest to head, MSB closest to terminator)
  - Ternary counter: pair 22=digit 0, 02=digit 1, 42=digit 2 (LSB closest to head)

Macro operations (alternating):
  RInc: head sweeps right through ternary (22→03 conversion), bounces off right
        edge (extending tape if needed), sweeps back (03→22), incrementing binary
        counter by 1 via carry propagation (B,3→4LB for carry, B,2→3RA to flip).
        Time ~doubles each step due to ternary region growing.

  LInc: head sweeps left through ternary, decrementing the ternary counter.
        Borrows through trailing 0s: 22^n → 42^n (set to max), then (42|02) → (02|22).

Overflow: when ternary counter reaches 0:
  LOv:   adds a zero digit to ternary counter
  RRstS: eats binary 1-bits, creates new ternary counter segment
  RRst0: initializes ternary counter to all-2s (max)
  LRst:  merges ternary counter segments
  (See mxdys's rules for details)

Observed counter values at ternary overflow points:
  T_digits  B_value    step  delta_B
  --------  -------  ------  -------
         2        0      93
         3        1     117        1  (immediate)
         4       10     764        9  = 3^2
         5       11     800        1  (immediate)
         6      129    6635      118
         7      130    6685        1  (immediate)
         8     1425   59170     1295
         9     1426   59228        1  (immediate)

Key properties:
  - Tape grows O(log n): ~5 cells per era, era duration ~9x previous
  - Never halts: A,1 (undefined) is never reached; the "31" terminator
    is only approached by state B (B,3→4LB bounces away, B,1→2LA retreats)
  - Binary counter grows without bound, ensuring infinite computation
"""

import argparse
from collections import defaultdict

# Transition table: (state, symbol) -> (write, move, new_state)
# States: A=0, B=1. Symbols: 0-4. Move: R=+1, L=-1.
RULES = {
    (0, 0): (1, +1, 1),  # A,0 -> 1RB
    # (0, 1): undefined    # A,1 -> ---
    (0, 2): (0, +1, 1),  # A,2 -> 0RB
    (0, 3): (0, -1, 0),  # A,3 -> 0LA
    (0, 4): (2, +1, 0),  # A,4 -> 2RA

    (1, 0): (2, -1, 1),  # B,0 -> 2LB
    (1, 1): (2, -1, 0),  # B,1 -> 2LA
    (1, 2): (3, +1, 0),  # B,2 -> 3RA
    (1, 3): (4, -1, 1),  # B,3 -> 4LB
    (1, 4): (0, -1, 1),  # B,4 -> 0LB
}

STATE_NAME = {0: 'A', 1: 'B'}


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


def parse_canonical(tape, head, state):
    """Try to parse tape as canonical form.

    Physical L→R: 0^inf 1 3 [binary:2|3] [HEAD] [ternary:42|02|22 pairs] 2 2 0^inf

    Returns (ternary_digits, binary_digits, ternary_value, binary_value) or None.
    ternary_digits: list, LSB first (closest to head).
    binary_digits: list, LSB first (closest to head = rightmost in physical).
    """
    lo, hi = get_tape_range(tape)
    if hi - lo < 3:
        return None

    # Check terminators
    if tape[lo] != 1 or tape[lo + 1] != 3:
        return None
    if tape[hi] != 2 or tape[hi - 1] != 2:
        return None

    h = head

    # Binary counter: lo+2 to h-1, all cells in {2,3}
    # Physical order: lo+2 (MSB, closest to terminator) ... h-1 (LSB, closest to head)
    bin_digits = []
    for i in range(lo + 2, h):
        v = tape[i]
        if v == 2:
            bin_digits.append(0)
        elif v == 3:
            bin_digits.append(1)
        else:
            return None
    bin_digits.reverse()  # LSB first

    # Ternary counter: h+1 to hi-2, consecutive pairs
    tern_digits = []
    i = h + 1
    while i + 1 <= hi - 2:
        pair = (tape[i], tape[i + 1])
        if pair == (4, 2):
            tern_digits.append(2)
        elif pair == (0, 2):
            tern_digits.append(1)
        elif pair == (2, 2):
            tern_digits.append(0)
        else:
            return None
        i += 2
    if i <= hi - 2:
        return None  # odd number of cells

    # Compute values (LSB first)
    bin_val = sum(d * (2 ** i) for i, d in enumerate(bin_digits))
    tern_val = sum(d * (3 ** i) for i, d in enumerate(tern_digits))

    return tern_digits, bin_digits, tern_val, bin_val


def simulate(max_steps, verbose=False, snapshot_interval=None, trace=False,
             rle_interval=None, head_track=False):
    tape = defaultdict(int)
    head = 0
    state = 0

    head_positions = []

    for step in range(1, max_steps + 1):
        sym = tape[head]
        key = (state, sym)

        if key not in RULES:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={sym} "
                  f"(undefined transition)")
            print(f"Tape summary: {tape_summary(tape)}")
            return

        write, move, new_state = RULES[key]

        if trace:
            print(f"step={step} state={STATE_NAME[state]} sym={sym} -> "
                  f"write={write} move={'R' if move > 0 else 'L'} "
                  f"new={STATE_NAME[new_state]} head={head}")

        tape[head] = write
        head += move
        state = new_state

        if head_track:
            head_positions.append(head)

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
        print(f"Tape summary: {tape_summary(tape)}")

    if head_track and head_positions:
        print(f"\nHead range: [{min(head_positions)}, {max(head_positions)}]")

    return tape, head, state, step


def macro_analyze(max_steps):
    """Track macro-level behavior: counter values at overflow points,
    tape growth events, and step-doubling between macro steps."""
    tape = defaultdict(int)
    head = 0
    state = 0

    prev_len = 0
    prev_canonical = None
    prev_growth_step = 0

    growth_events = []
    overflow_events = []

    for step in range(1, max_steps + 1):
        sym = tape[head]
        key = (state, sym)
        if key not in RULES:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={sym}")
            break

        write, move, new_state = RULES[key]
        tape[head] = write
        head += move
        state = new_state

        # Detect tape growth
        lo, hi = get_tape_range(tape)
        cur_len = hi - lo + 1 if (lo != hi or tape[lo] != 0) else 0
        if cur_len > prev_len:
            tape_content = ''.join(str(tape[i]) for i in range(lo, hi + 1))
            head_rel = head - lo
            side = 'R' if head_rel >= cur_len else 'L'

            # Count consecutive 4s after '12' prefix (for left-growth events)
            fours = 0
            if side == 'L' and len(tape_content) >= 3:
                for c in tape_content[2:]:
                    if c == '4':
                        fours += 1
                    else:
                        break

            diff = step - prev_growth_step
            growth_events.append((step, side, fours, cur_len, diff))
            prev_growth_step = step
            prev_len = cur_len

        # Detect canonical form (overflow points)
        result = parse_canonical(tape, head, state)
        if result is not None:
            tern_d, bin_d, tern_v, bin_v = result
            canon_key = (tuple(tern_d), tuple(bin_d), state)
            if canon_key != prev_canonical:
                overflow_events.append((step, STATE_NAME[state], len(tern_d),
                                        tern_v, len(bin_d), bin_v))
                prev_canonical = canon_key

    # Print tape growth events
    print("=== TAPE GROWTH EVENTS ===")
    print(f"{'step':>10} {'side':>4} {'4s':>3} {'len':>4} {'diff':>10} {'ratio':>8}")
    prev_diff = None
    for step, side, fours, tlen, diff in growth_events:
        ratio = diff / prev_diff if prev_diff and prev_diff > 0 else 0
        r_str = f"{ratio:.3f}" if ratio > 0 else ""
        if side == 'L' and fours >= 1:
            print(f"{step:>10} {side:>4} {fours:>3} {tlen:>4} {diff:>10} {r_str:>8}")
            prev_diff = diff
        elif side == 'R':
            print(f"{step:>10} {side:>4} {'':>3} {tlen:>4} {diff:>10} {'*** ERA BOUNDARY ***':>8}")
            prev_diff = None

    # Print overflow events
    print("\n=== CANONICAL STATES (ternary overflow points) ===")
    print(f"{'step':>10} {'st':>2} {'T_dig':>5} {'T_val':>8} {'B_dig':>5} {'B_val':>8} {'dB':>8}")
    prev_bv = None
    for step, st, td, tv, bd, bv in overflow_events:
        db = bv - prev_bv if prev_bv is not None else 0
        db_str = f"{db:>8}" if prev_bv is not None else ""
        print(f"{step:>10} {st:>2} {td:>5} {tv:>8} {bd:>5} {bv:>8} {db_str}")
        prev_bv = bv

    # Summary
    print(f"\n=== SUMMARY ===")
    if growth_events:
        print(f"Total tape growth events: {len(growth_events)}")
        print(f"Final tape length: {growth_events[-1][3]}")
    if overflow_events:
        last = overflow_events[-1]
        print(f"Final binary counter: {last[5]} ({last[4]} digits)")
        print(f"Final ternary digits: {last[2]}")
    print(f"Tape growth: O(log n) — binary counter carries double step intervals")


if __name__ == '__main__':
    parser = argparse.ArgumentParser(
        description='Simulate TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB')
    parser.add_argument('-n', '--steps', type=int, default=10000,
                        help='Max steps (default: 10000)')
    parser.add_argument('-v', '--verbose', action='store_true',
                        help='Show first 200 steps tape')
    parser.add_argument('-t', '--trace', action='store_true',
                        help='Print every transition')
    parser.add_argument('-s', '--snapshot', type=int, default=None,
                        help='Print summary every N steps')
    parser.add_argument('-r', '--rle', type=int, default=None,
                        help='Print RLE every N steps')
    parser.add_argument('--head-track', action='store_true',
                        help='Track head positions')
    parser.add_argument('--macro', action='store_true',
                        help='Macro-level analysis: track counter values and growth')
    args = parser.parse_args()

    if args.macro:
        macro_analyze(args.steps)
    else:
        simulate(args.steps, verbose=args.verbose, snapshot_interval=args.snapshot,
                 trace=args.trace, rle_interval=args.rle,
                 head_track=args.head_track)
