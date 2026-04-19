#!/usr/bin/env python3
"""Extended simulator with macro-state analysis."""

from sim import Tape, TM


def tape_to_strip(t):
    """Return (left, state, right, head_sym) strings."""
    left = ''.join(str(s) for s in t.left)
    right = ''.join(str(s) for s in t.right)
    return left, t.state, right


def summary(t):
    l, st, r = tape_to_strip(t)
    # Strip leading/trailing zeros for blanks
    l_str = l.lstrip('0')
    r_str = r.rstrip('0')
    lzero = len(l) - len(l_str)
    rzero = len(r) - len(r_str)
    return f"0^{lzero} {l_str}[{st}]{r_str} 0^{rzero}"


def run_to_event(t, max_steps, pred):
    """Run until pred(t) true, return step count."""
    for k in range(max_steps):
        ok = t.step()
        if not ok:
            return k, False, True  # halted
        if pred(t):
            return k+1, True, False
    return max_steps, False, False


def is_left_edge(t):
    return t.pos == t.minpos


def is_right_edge(t):
    return t.pos == t.maxpos


def run_collect(max_steps=200000):
    """Record every time the head enters state A at the right end (start of bouncer?)."""
    t = Tape()
    events = []
    prev_len = 0
    extend_events = []  # steps when length extends

    prev_min = t.minpos
    prev_max = t.maxpos
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            return events, extend_events, step, t, True
        if t.minpos < prev_min or t.maxpos > prev_max:
            extend_events.append((step+1, t.pos, t.state, t.length(), summary(t)))
            prev_min = t.minpos
            prev_max = t.maxpos
    return events, extend_events, max_steps, t, False


if __name__ == '__main__':
    import sys
    nsteps = int(sys.argv[1]) if len(sys.argv) > 1 else 50000

    events, ext_events, steps, t, halted = run_collect(nsteps)
    print(f"Ran {steps} steps, halted={halted}, final length={t.length()}")
    print(f"Extension events: {len(ext_events)}")
    print()
    print("Last 40 extension events:")
    for step, pos, state, length, s in ext_events[-40:]:
        print(f"  step={step:8d} pos={pos:+6d} state={state} len={length:5d}  {s[:80]}")

    # Find bouncer returns: state A after doing a leftward sweep
    # Alternatively look for specific state patterns at edges
