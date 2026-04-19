#!/usr/bin/env python3
"""Detailed phase-boundary detection within each DBL macro cycle.

For each (z, m) → (2z, m+2-2z) cycle, identify:
  - phase1 end (C/E sweep over zebra)
  - phase2 end (4 boundary steps)
  - phase3 end (FA-sweep over 1 block)
  - alternating rounds and break-cycles in phase 4+5
  - final extension
"""

from sim import Tape
from sim3 import extract_C_macro
from sim6 import run_and_extract, annotate_dbl


def trace_cycle(start_step, end_step, verbose=False):
    """Trace the TM from start_step (state at start) to end_step.
    Returns: list of (state-before, direction-taken) for each transition."""
    t = Tape()
    for _ in range(start_step):
        t.step()

    trans = []
    for _ in range(end_step - start_step):
        state_before = t.state
        pos_before = t.pos
        len_before = t.length()
        lleft = len(t.left)
        sym = t.right[0] if t.right else 0
        t.step()
        trans.append({
            'state_before': state_before,
            'sym_before': sym,
            'state_after': t.state,
            'left_len_after': len(t.left),
        })
    return trans


def partition_cycle(trans, z):
    """Given a transition trace of a full DBL cycle for value z,
    partition into phases. Returns dict of (phase_name, step_count)."""
    # Phase 1: C/E sweep for 2z steps (alternating C→E→C→…), ending with C,1→D.
    # Actually: 2z C↔E transitions, then C transitions to D (the (2z+1)-th step is C,1→D,1).
    # Hmm let me just count phase 1 as 2z transitions of C and E alternation.
    # The sim output at end of phase 1 has state D (just after the C→D step).
    # So we look for the first index where state_after = 'D'.

    # In detail: phase 1 takes 2z steps (my lemma says run 2z steps).
    # Then phase 2 takes 4 steps. Phase 3 takes 5 steps.
    # So post-phase-1 ends at step 2z.
    # Post-phase-2 ends at step 2z+4.
    # Post-phase-3 ends at step 2z+9.

    phases = {}
    phases['phase1'] = 2 * z
    phases['phase2'] = 4
    phases['phase3'] = 5
    phases['phase123'] = 2 * z + 9

    # Now characterize phase 4+5.
    # Phase 4 consists of alternating "rounds" (4-step D,D,B,F ending in state D)
    # and "break cycles" (starts D,D,B,F but F reads 0, then mini-FA, then F,1→D).
    # Final: 3-step extension D,D,B→C.

    phase4_start = 2 * z + 9
    rounds = []      # (start_idx, count)
    breaks = []      # (start_idx, mini_fa_len)
    final = None

    idx = phase4_start
    while idx < len(trans):
        # Check if final extension (D,1→D,0→B,0→C)
        if idx + 3 <= len(trans):
            t3 = [trans[idx + j] for j in range(3)]
            if (t3[0]['state_before'] == 'D' and t3[0]['sym_before'] == 1 and
                t3[1]['state_before'] == 'D' and t3[1]['sym_before'] == 0 and
                t3[2]['state_before'] == 'B' and t3[2]['sym_before'] == 0 and
                t3[2]['state_after'] == 'C'):
                final = idx
                break
        # Otherwise, try a "round" or "break"
        if idx + 4 <= len(trans):
            t4 = [trans[idx + j] for j in range(4)]
            if (t4[0]['state_before'] == 'D' and t4[0]['sym_before'] == 1 and
                t4[1]['state_before'] == 'D' and t4[1]['sym_before'] == 0 and
                t4[2]['state_before'] == 'B' and t4[2]['sym_before'] == 1 and
                t4[3]['state_before'] == 'F'):
                if t4[3]['sym_before'] == 1:
                    # Clean round
                    rounds.append(idx)
                    idx += 4
                    continue
                else:
                    # Break cycle
                    # Count steps until back in state D
                    break_start = idx
                    idx += 4  # skip the 4 D,D,B,F(0) steps
                    mini_fa_steps = 0
                    while idx < len(trans) and trans[idx - 1]['state_after'] != 'D':
                        if trans[idx]['state_before'] == 'D':
                            break
                        idx += 1
                        mini_fa_steps += 1
                    # Now trans[idx-1]['state_after'] should be D (from F,1→0RD)
                    # Or at idx we're at state D
                    breaks.append((break_start, idx - break_start))
                    continue
        print(f"Warning: unexpected pattern at idx={idx}")
        break

    phases['phase4_start'] = phase4_start
    phases['rounds'] = rounds
    phases['breaks'] = breaks
    phases['final'] = final
    phases['total'] = len(trans)
    return phases


def analyze_cycles(max_steps=2_000_000):
    events = run_and_extract(max_steps)
    dbl_cycles = annotate_dbl(events)

    # Find first cycle for each z value
    seen_z = {}
    for start, end, z_i, m_i, z_j, m_j in dbl_cycles:
        if z_i not in seen_z:
            seen_z[z_i] = (start, end, z_i, m_i, z_j, m_j)

    print(f"Unique z values found: {sorted(seen_z.keys())}")
    print()

    results = {}
    for z in sorted(seen_z.keys()):
        start, end, z_i, m_i, z_j, m_j = seen_z[z]
        trans = trace_cycle(start, end)
        phases = partition_cycle(trans, z)
        phases['start_step'] = start
        phases['end_step'] = end
        phases['m'] = m_i
        phases['m_out'] = m_j
        results[z] = phases
    return results


if __name__ == '__main__':
    import sys
    max_steps = int(sys.argv[1]) if len(sys.argv) > 1 else 2_000_000
    results = analyze_cycles(max_steps)
    for z, p in sorted(results.items()):
        print(f"=== z = {z}, m = {p['m']}, cycle [{p['start_step']}..{p['end_step']}] ({p['end_step']-p['start_step']} steps) ===")
        print(f"  phase1 (CE-sweep):  {p['phase1']} steps")
        print(f"  phase2 (boundary):  {p['phase2']} steps")
        print(f"  phase3 (FA-sweep):  {p['phase3']} steps")
        print(f"  phase 4+5:")
        rounds = p['rounds']
        breaks = p['breaks']
        # Combine rounds and breaks in order
        combined = sorted([(r, 'round', 4) for r in rounds] + [(b[0], 'break', b[1]) for b in breaks])
        # Group consecutive rounds
        print(f"    (round=4 steps, break=variable)")
        i = 0
        while i < len(combined):
            if combined[i][1] == 'round':
                # Count consecutive rounds
                j = i
                while j < len(combined) and combined[j][1] == 'round':
                    j += 1
                count = j - i
                print(f"    {count} rounds ({count*4} steps)")
                i = j
            else:
                print(f"    break ({combined[i][2]} steps)")
                i += 1
        if p['final'] is not None:
            print(f"  final (extension): 3 steps")
        total = sum(4 for _ in rounds) + sum(b[1] for b in breaks) + (3 if p['final'] is not None else 0)
        print(f"  phase 4+5 total: {total} steps (expected {6*z*z - 2*z - 9})")
        print(f"  grand total: {p['total']} steps (expected {6*z*z})")
        print()
