#!/usr/bin/env python3
"""Phase-boundary-extracting simulator.

For each DBL macro cycle encountered, identify and count the sub-phases:
  - phase1 (CE-sweep)
  - phase2 (4 boundary steps C→D→D→B→F)
  - phase3 (5-step FA-sweep)
  - [alternating] "round" and "break cycle" substructures
  - final extension (3 steps: D→D→B→C)

Records raw step counts for each sub-phase and emits a summary table.
"""

from sim import Tape
from sim3 import extract_C_macro


def run_and_extract(max_steps=5_000_000):
    """Run the TM from blank tape, find each (z, m) at C-left-edge,
    record the step indices and full state transitions."""
    t = Tape()
    events = []  # (step, z, m, len)
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            break
        if t.state == 'C' and t.pos == t.minpos:
            mc = extract_C_macro(t)
            if mc is not None:
                z, m = mc
                events.append((step + 1, z, m, t.length()))
    return events


def annotate_dbl(events):
    """Find consecutive events that form a clean DBL cycle:
    (z, m) → (2z, m+2-2z) with step delta = 6·z²."""
    dbl_cycles = []
    for i in range(len(events) - 1):
        step_i, z_i, m_i, _ = events[i]
        step_j, z_j, m_j, _ = events[i + 1]
        if z_j == 2 * z_i and m_j == m_i + 2 - 2 * z_i and step_j - step_i == 6 * z_i * z_i:
            dbl_cycles.append((step_i, step_j, z_i, m_i, z_j, m_j))
    return dbl_cycles


def trace_phases(start_step, end_step, stop_at_step=None):
    """Re-run the TM from blank tape to `start_step`, then step through
    up to `end_step`, recording every state transition. Returns the
    list of (step, pos, state, left_len, right_len)."""
    t = Tape()
    for _ in range(start_step):
        t.step()
    trace = []
    for step in range(start_step, end_step):
        trace.append((step, t.pos, t.state, len(t.left), len(t.right) - 1 if t.right else 0))
        t.step()
    trace.append((end_step, t.pos, t.state, len(t.left), len(t.right) - 1 if t.right else 0))
    return trace


def classify_transitions(trace):
    """Given a trace, identify state transitions and classify them."""
    transitions = []
    for i in range(len(trace) - 1):
        s1 = trace[i]
        s2 = trace[i + 1]
        transitions.append((s1[0], s1[2], s2[2]))  # (step, from_state, to_state)
    return transitions


def count_phase_pattern(transitions, start_idx=0):
    """Identify the phase structure within a trace starting at `start_idx`:
       - find phase1 (C/E alternating until C,1→D,1)
       - phase2 (4 steps C→D, D→D, D→B, B→F)
       - phase3 (FA-sweep up to D reading 1)
       - phase4 (alternating rounds and break cycles until C state reached)"""
    return transitions  # placeholder


def extract_rounds_and_breaks(t, end_step, start_step):
    """During phase 4+5, identify each 'round' (4 steps D,D,B,F at same
    left extent ending with F,1→0RD) and each 'break cycle' (longer
    subpattern where F reads 0 and branches to mini-FA)."""
    t_sim = Tape()
    for _ in range(start_step):
        t_sim.step()

    rounds = []
    breaks = []

    step = start_step
    # A 'round' = 4 transitions D,D,B,F ending with F,1→0RD at R direction.
    # A 'break' = starts same way but F reads 0 → F,0→1RA, then mini-FA.

    while step < end_step:
        # Look at next 4 transitions
        if t_sim.state != 'D':
            # Unexpected; record as 'other'
            step += 1
            t_sim.step()
            continue
        start_of_block = step
        start_left_len = len(t_sim.left)
        start_right_len = len(t_sim.right) - 1 if t_sim.right else 0
        # Try a round: D,1 → D,0 → B → F, then step 4 decides round vs break
        states = [t_sim.state]
        for _ in range(4):
            if step >= end_step:
                break
            t_sim.step()
            step += 1
            states.append(t_sim.state)
        # states should be [D, D, B, F, X] where X = D (clean round) or A (break)
        if len(states) == 5 and states[:4] == ['D', 'D', 'B', 'F'] and states[4] == 'D':
            # Clean round: 4 transitions, F,1→0RD at end
            rounds.append((start_of_block, start_left_len, start_right_len))
        elif len(states) == 5 and states[:4] == ['D', 'D', 'B', 'F'] and states[4] == 'A':
            # Break: F,0→1RA. Continue through mini-FA until we hit state D again.
            mini_fa_start = step
            mini_fa_len = 0
            while step < end_step and t_sim.state != 'D':
                t_sim.step()
                step += 1
                mini_fa_len += 1
            # Should now be in state D
            breaks.append((start_of_block, start_left_len, start_right_len, mini_fa_len))
        else:
            # Something else
            print(f"Warning: unexpected states {states} at step {start_of_block}")
            break
    return rounds, breaks


if __name__ == '__main__':
    import sys
    max_steps = int(sys.argv[1]) if len(sys.argv) > 1 else 1_000_000

    events = run_and_extract(max_steps)
    print(f"# C-macro events found: {len(events)}")

    dbl_cycles = annotate_dbl(events)
    print(f"# Clean DBL cycles found: {len(dbl_cycles)}")
    print()
    print(f"{'start':>8} {'end':>8} {'z':>4} {'m':>5}   {'2z':>3} {'newM':>5} steps")
    for start, end, z_i, m_i, z_j, m_j in dbl_cycles[:50]:
        steps = end - start
        print(f"{start:8d} {end:8d} {z_i:4d} {m_i:5d}   {z_j:3d} {m_j:5d} {steps:6d}")
