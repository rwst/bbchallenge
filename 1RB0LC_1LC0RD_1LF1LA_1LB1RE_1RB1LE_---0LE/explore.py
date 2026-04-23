#!/usr/bin/env python3
"""Exploration: find natural macro events by tracking distinct
'state + local context' events and their dt between reappearances."""

import sys
from sim import Tape, STATE_NAMES, TR

def event_key(t):
    """A compact key for the local context.  Head position = relative to
    non-blank window."""
    # shape: state, symbol, left-side partial shape, right-side partial shape
    return (STATE_NAMES[t.state], t.arr[t.hp])

def trace_left_bdry_by_state(n, max_events=80):
    """For every state, record events where head is at left-of-lo+0 or
    right-of-hi+0 (i.e., at a blank boundary)."""
    from collections import Counter
    t = Tape()
    events = []
    while t.steps < n and len(events) < max_events * 6:
        if t.halted: break
        at_rbound = t.hp > t.hi and t.arr[t.hp] == 0
        at_lbound = t.hp < t.lo and t.arr[t.hp] == 0
        if at_rbound or at_lbound:
            side = 'R' if at_rbound else 'L'
            ts, hp = t.tape_str()
            events.append((t.steps, STATE_NAMES[t.state], side, ts))
        t.step()
    return events


def track_right_bdry_E(n, max_events=80):
    """Every time E at right-of-hi+0 appears, log it with blocks."""
    t = Tape()
    prev = 0
    out = []
    while t.steps < n and len(out) < max_events:
        if t.halted: break
        if t.state == 4 and t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = t.blocks_between(min(t.lo, t.hp), max(t.hi, t.hp))
            out.append((t.steps, t.steps - prev, blocks))
            prev = t.steps
        t.step()
    return out


def track_left_bdry(state_name, n, max_events=80):
    """Every time given state at left-of-lo+0 appears."""
    idx = STATE_NAMES.index(state_name)
    t = Tape()
    prev = 0
    out = []
    while t.steps < n and len(out) < max_events:
        if t.halted: break
        if t.state == idx and t.arr[t.hp] == 0 and t.hp < t.lo:
            blocks = t.blocks_between(min(t.lo, t.hp), max(t.hi, t.hp))
            out.append((t.steps, t.steps - prev, blocks))
            prev = t.steps
        t.step()
    return out


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "left"
    if cmd == "left":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 100000
        evs = trace_left_bdry_by_state(n)
        for ts, st, side, tape in evs[:120]:
            print(f"step {ts:7d} [{st}] {side} tape={tape}")
    elif cmd == "lbdry":
        st = sys.argv[2]
        n = int(sys.argv[3]) if len(sys.argv) > 3 else 100000
        for ts, dt, blocks in track_left_bdry(st, n):
            print(f"step {ts:7d} dt={dt:6d} blocks={blocks}")
