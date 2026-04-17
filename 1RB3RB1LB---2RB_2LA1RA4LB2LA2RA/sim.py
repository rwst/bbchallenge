#!/usr/bin/env python3
"""Simulator for TM 1RB3RB1LB---2RB_2LA1RA4LB2LA2RA (2-state 5-symbol).

Transition table:
       0     1     2     3     4
  A   1RB   3RB   1LB   ---   2RB
  B   2LA   1RA   4LB   2LA   2RA

Macro conjecture (dyuan01.txt):
   [x1, x2, ..., xk] := 1 <B 4^x1 1 2 4^x2 1 2 ... 1 2 4^xk
   (physical tape L->R, '<B' marks state B with head at cell immediately to its right)

Start macro config: [1, 1]

Rules (conjectured):
  (R1) [0, a, b, ...] -> [a+3, b, ...]
  (R2) [2n+1, 2a, 2b, ..., 0] -> Halt
  (R3) [2n+1, 2a, 2b, ..., 2m+2] -> [2n, 2a, 2b, ..., 2m+2, 0]
  (R4) [2n+1, 2a, 2b, ..., 2m+1] -> [2n, 2a, 2b, ..., 2m+1, 1]
  (R5) [2n+1, 2a, 2b, ..., 2m+1, x, ...tail] -> [2n, 2a, 2b, ..., 2m+1, x+1, ...tail]
  (R6) [2n+2, a, b, ...] -> [2n+1, a+1, b, ...]
"""

import argparse
from collections import defaultdict


RULES = {
    (0, 0): (1, +1, 1),  # A,0 -> 1RB
    (0, 1): (3, +1, 1),  # A,1 -> 3RB
    (0, 2): (1, -1, 1),  # A,2 -> 1LB
    # (0, 3): undefined -> HALT
    (0, 4): (2, +1, 1),  # A,4 -> 2RB
    (1, 0): (2, -1, 0),  # B,0 -> 2LA
    (1, 1): (1, +1, 0),  # B,1 -> 1RA
    (1, 2): (4, -1, 1),  # B,2 -> 4LB
    (1, 3): (2, -1, 0),  # B,3 -> 2LA
    (1, 4): (2, +1, 0),  # B,4 -> 2RA
}

STATE_NAME = {0: 'A', 1: 'B'}


def tape_str(tape, head, width=40):
    lo = head - width
    hi = head + width
    chars = []
    for i in range(lo, hi + 1):
        s = str(tape[i])
        if i == head:
            s = f'[{s}]'
        chars.append(s)
    return ''.join(chars)


def get_tape_range(tape):
    positions = [k for k, v in tape.items() if v != 0]
    if not positions:
        return 0, 0
    return min(positions), max(positions)


def step_tm(tape, head, state):
    sym = tape[head]
    key = (state, sym)
    if key not in RULES:
        return None
    write, move, new_state = RULES[key]
    tape[head] = write
    return head + move, new_state


def parse_macro(tape, head, state):
    """Attempt to parse current config as [x1, x2, ..., xk].

    Physical tape L->R: 0^inf <B=1 4^x1 1 2 4^x2 1 2 ... 1 2 4^xk 0^inf
    '<B' sits AT the head; the cell at the head is 1 (drawn as '1 <B' before
    the next block). State = B; head-cell = 1; left = blanks.
    The "4^x1 1 2 ..." is all to the right of the head.

    Returns list of digits xs, or None if config doesn't match.
    """
    if state != 1:  # must be B
        return None
    if tape[head] != 1:
        return None
    lo, hi = get_tape_range(tape)
    # Left of head must be blank
    if any(tape[j] != 0 for j in range(lo, head)):
        return None
    # Scan right starting from head+1: 4^x1 1 2 4^x2 1 2 ... 4^xk then 0s
    # (The final digit xk may be 0, meaning the tape ends right after a "1 2"
    # separator.)
    digits = []
    i = head + 1
    while True:
        # Count leading 4s
        x = 0
        while tape[i] == 4:
            x += 1
            i += 1
        # Now either 0 (end of last block) or '1 2' (separator)
        if tape[i] == 0:
            digits.append(x)
            # Bound check: everything beyond i must also be zero (auto-true
            # for defaultdict since i > hi implies zero).
            return digits
        if tape[i] == 1 and tape[i + 1] == 2:
            digits.append(x)
            i += 2
            continue
        return None


def render_macro(digits):
    return '[' + ', '.join(str(d) for d in digits) + ']'


def apply_macro_rule(digits):
    """Apply conjectured macro rule. Return (new_digits, rule_name) or ('halt', ...)."""
    if len(digits) == 0:
        return None, 'empty'
    first = digits[0]
    # Rule 1: first = 0
    if first == 0:
        if len(digits) < 2:
            return None, 'R1_stuck'  # [0] alone — rule needs at least [0, a]
        new = [digits[1] + 3] + digits[2:]
        return new, 'R1'
    # first >= 1
    if first % 2 == 0:
        # Rule 6: [2n+2, a, b, ...]
        if len(digits) < 2:
            return None, 'R6_stuck'
        new = [first - 1, digits[1] + 1] + digits[2:]
        return new, 'R6'
    # first is odd (>=1)
    if len(digits) < 2:
        return None, 'R_stuck_single_odd'
    # Find first odd digit in middle (index >= 1, < last)
    # Middle indices: 1 .. len-2 (exclusive of last if rule 3/4)
    # Rule 5: if there's an odd in middle
    odd_idx = None
    for i in range(1, len(digits) - 1):
        if digits[i] % 2 == 1:
            odd_idx = i
            break
    if odd_idx is not None:
        # Rule 5: decrement first, increment digit after odd
        new = digits.copy()
        new[0] -= 1
        new[odd_idx + 1] += 1
        return new, 'R5'
    # All middle digits even. Look at last digit.
    last = digits[-1]
    if last == 0:
        return None, 'HALT (R2)'
    if last % 2 == 1:
        # Rule 4: last odd
        new = digits.copy()
        new[0] -= 1
        new.append(1)
        return new, 'R4'
    # last even >= 2
    new = digits.copy()
    new[0] -= 1
    new.append(0)
    return new, 'R3'


def simulate_to_macro(max_steps, start_step=0, tape0=None, head0=0, state0=0,
                      verbose=False, trace_until=None):
    """Run TM, detect each time we enter a macro config [x1, ..., xk].

    Returns list of (step, macro_digits).
    """
    tape = defaultdict(int)
    if tape0 is not None:
        for k, v in tape0.items():
            tape[k] = v
    head = head0
    state = state0

    events = []
    step = start_step
    prev_digits = None

    while step < max_steps:
        step += 1
        r = step_tm(tape, head, state)
        if r is None:
            print(f"HALT at step {step}: state={STATE_NAME[state]} sym={tape[head]}")
            break
        head, state = r

        if trace_until is not None and step <= trace_until:
            print(f"step={step:5d} st={STATE_NAME[state]} head={head:3d} | "
                  f"{tape_str(tape, head, 20)}")

        digits = parse_macro(tape, head, state)
        if digits is not None and digits != prev_digits:
            events.append((step, digits))
            prev_digits = digits
            if verbose:
                print(f"step={step:8d}  {render_macro(digits)}  "
                      f"len={len(digits)}")

    return events, tape, head, state


def compare_macro_with_rules(max_steps=100000, verbose=False):
    """Simulate TM and compare transitions between macro configs with conjectured rules."""
    events, *_ = simulate_to_macro(max_steps, verbose=False)
    print(f"Observed {len(events)} macro configs in {max_steps} TM steps.")
    if not events:
        print("No macro configs reached — check parse_macro logic.")
        return

    # Find first event and verify rules
    print(f"\nFirst 30 macro configs:")
    for step, digits in events[:30]:
        print(f"  step={step:8d}  {render_macro(digits)}")

    print(f"\nVerifying conjectured rules against observed transitions:")
    mismatches = 0
    checked = 0
    for (s1, d1), (s2, d2) in zip(events, events[1:]):
        pred, rule = apply_macro_rule(d1)
        checked += 1
        if pred is None:
            print(f"  step {s1}->{s2}: {render_macro(d1)} -> {render_macro(d2)}  "
                  f"[rule returned None: {rule}]")
            mismatches += 1
            continue
        if pred != d2:
            print(f"  MISMATCH step {s1}->{s2}: {render_macro(d1)} --{rule}--> "
                  f"predicted {render_macro(pred)} but got {render_macro(d2)}")
            mismatches += 1
    print(f"\nChecked {checked} transitions, {mismatches} mismatches.")


def find_first_macro(max_steps=200):
    """Find when TM first enters a macro config, starting from blank tape."""
    events, *_ = simulate_to_macro(max_steps, verbose=True)
    if events:
        step, digits = events[0]
        print(f"\nFirst macro config reached at step {step}: {render_macro(digits)}")
    else:
        print(f"No macro config in {max_steps} steps.")


def main():
    p = argparse.ArgumentParser()
    p.add_argument('-n', '--steps', type=int, default=200000)
    p.add_argument('-v', '--verbose', action='store_true')
    p.add_argument('--find-first', action='store_true',
                   help='Only find first macro config')
    p.add_argument('--trace', type=int, default=None,
                   help='Trace first N steps')
    args = p.parse_args()

    if args.find_first:
        find_first_macro(args.steps)
    else:
        events, tape, head, state = simulate_to_macro(
            args.steps, verbose=args.verbose, trace_until=args.trace)
        print(f"\n{len(events)} macro configs in {args.steps} steps.")
        if events:
            print(f"First: step={events[0][0]} {render_macro(events[0][1])}")
            print(f"Last:  step={events[-1][0]} {render_macro(events[-1][1])}")
        # Verify
        print(f"\nRule check:")
        mismatches = 0
        for (s1, d1), (s2, d2) in zip(events, events[1:]):
            pred, rule = apply_macro_rule(d1)
            if pred is None or pred != d2:
                mismatches += 1
                if mismatches <= 10:
                    print(f"  step {s1}->{s2}: {render_macro(d1)} --{rule}--> "
                          f"predicted={pred and render_macro(pred)} got={render_macro(d2)}")
        print(f"  {mismatches} mismatches out of {len(events)-1} transitions.")


if __name__ == '__main__':
    main()
