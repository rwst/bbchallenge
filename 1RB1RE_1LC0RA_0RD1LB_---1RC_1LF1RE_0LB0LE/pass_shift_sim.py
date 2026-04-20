#!/usr/bin/env python3
"""Extensive simulation to support `pass_shift` proof.

Studies the dynamics of the TM starting at SE(a+1, b, c+2) running for
4(b+c)+13 steps, and verifies that the ending config is SE(a, b+2, c+1).

Also:
- Verifies step-count formula over a grid of (a, b, c).
- Measures head-position extremes (for a-locality bound).
- Tracks tape state at each step (phase identification).
- Tests the 4-step c-bridge conjecture.
- Records structural invariants that can inform the Lean proof.

Writes findings to `pass_shift_findings.txt`.
"""

import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

from collections import defaultdict
import sys

TM_STR = "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

def parse_tm(s):
    trs = {}
    rows = s.split("_")
    for i, row in enumerate(rows):
        for j, trans in enumerate([row[:3], row[3:]]):
            if trans == "---":
                trs[(i, j)] = None
            else:
                w = int(trans[0])
                d = trans[1]
                ns = ord(trans[2]) - ord('A')
                trs[(i, j)] = (w, d, ns)
    return trs

TR = parse_tm(TM_STR)
STATE_NAMES = "ABCDEF"
STE = 4
STF = 5
STB = 1
STA = 0
STC = 2
STD = 3

def zebra(k):
    """[false, true, false, true, ...] of length 2k (zebra k)."""
    return [0, 1] * k

def set_SE(a, b, c, q=100):
    """Return dict-based tape for SE_Config a b c, with q blank padding."""
    # left list (reversed, closest to head first):
    # ones c + zebra b + [false] + zebra a + zeros q
    left_list = [1] * c + zebra(b) + [0] + zebra(a) + [0] * q
    # Build tape: head at pos 0, left_list[i] at pos -(i+1) = pos (-1-i)
    tape = defaultdict(int)
    for i, v in enumerate(left_list):
        tape[-1 - i] = v
    return tape, 0, STE  # tape, head_pos, state

def step(tape, hp, state):
    """One step of the TM.  Returns (tape, hp, state, halted)."""
    sym = tape[hp]
    t = TR[(state, sym)]
    if t is None:
        return tape, hp, state, True
    w, d, ns = t
    tape[hp] = w
    if d == 'R':
        hp += 1
    else:
        hp -= 1
    return tape, hp, ns, False

def run(tape, hp, state, n):
    """Run n steps, recording trace.  Returns trace[0..n] = (hp, state, tape_snapshot_mini)."""
    trace = []
    for _ in range(n):
        trace.append((hp, state))
        tape, hp, state, halted = step(tape, hp, state)
        if halted:
            break
    trace.append((hp, state))
    return tape, hp, state, trace

def read_tape_window(tape, lo, hi):
    """Read tape[lo..hi] into a tuple."""
    return tuple(tape[i] for i in range(lo, hi + 1))

def matches_SE(tape, hp, state, a, b, c, head_expected=0):
    """Check if current config matches SE_Config a b c exactly (no right content)."""
    if state != STE: return False
    if tape[hp] != head_expected: return False
    # Right of head: all 0.
    for i in range(hp + 1, hp + 50):
        if tape[i]: return False
    # Left of head: ones c, zebra b, [false], zebra a, then all 0.
    expected = [1] * c + zebra(b) + [0] + zebra(a)
    for i, v in enumerate(expected):
        if tape[hp - 1 - i] != v:
            return False
    # Further left: all 0.
    for i in range(len(expected), len(expected) + 50):
        if tape[hp - 1 - i]: return False
    return True

def verify_pass_shift(a, b, c):
    """Run pass_shift for (a, b, c), verify it reaches SE(a, b+2, c+1) in 4(b+c)+13 steps."""
    tape, hp, state = set_SE(a + 1, b, c + 2)
    n = 4 * (b + c) + 13
    tape_out, hp_out, state_out, trace = run(tape, hp, state, n)
    ok = matches_SE(tape_out, hp_out, state_out, a, b + 2, c + 1)
    return ok, trace, (tape_out, hp_out, state_out)

def head_extremes(trace):
    """Min and max head position in trace."""
    positions = [hp for hp, _ in trace]
    return min(positions), max(positions)

def state_sequence(trace):
    return [state for _, state in trace]

def summarize_phases(trace):
    """Break trace into phases based on state transitions.
    Phase boundaries typically are:
      A: starts at E, through E/F oscillation.
      B: transitions to B (after F hits 0 separator).
      C: B/A alternation.
      D: transitions back to E at right boundary.
    """
    states = [s for _, s in trace]
    phases = []
    cur_phase = "A"
    start_idx = 0
    for i, s in enumerate(states):
        # Detect transitions
        if cur_phase == "A" and s == STB:
            phases.append((cur_phase, start_idx, i))
            cur_phase = "C"
            start_idx = i
        elif cur_phase == "C" and s == STE and i > start_idx:
            phases.append((cur_phase, start_idx, i))
            cur_phase = "D"
            start_idx = i
    phases.append((cur_phase, start_idx, len(states) - 1))
    return phases

def test_cbridge(a, b, c, offset1, offset2):
    """Generic bridge test: SE(a+1, b, c+3) after offset1 steps vs
    SE(a+1, b, c+2) after offset2 steps.  Compares tapes and states,
    allowing position translation.

    Returns (match_up_to_translation, shift_amount, info).
    """
    tape1, hp1, st1 = set_SE(a + 1, b, c + 3)
    tape1, hp1, st1, _ = run(tape1, hp1, st1, offset1)

    tape2, hp2, st2 = set_SE(a + 1, b, c + 2)
    tape2, hp2, st2, _ = run(tape2, hp2, st2, offset2)

    if st1 != st2:
        return False, 0, f"states differ {STATE_NAMES[st1]} vs {STATE_NAMES[st2]}"
    # Check tape contents modulo position shift: shift = hp1 - hp2.
    shift = hp1 - hp2
    # Head symbols match?
    if tape1[hp1] != tape2[hp2]:
        return False, shift, f"head sym differs at hp1={hp1},hp2={hp2}"
    # Compare tapes: for each position p in tape2, check tape1[p + shift] == tape2[p].
    diffs = []
    for p in range(hp2 - 50, hp2 + 50):
        if tape1[p + shift] != tape2[p]:
            diffs.append((p, tape1[p + shift], tape2[p]))
    return True, shift, f"shift={shift}, diffs_vs_shifted={diffs}"

def a_independence_check(b, c, amax):
    """Check that pass_shift dynamics for (a, b, c) are the same for all a ≥ amax_thresh.
    Return max head-reach relative to separator."""
    results = []
    n = 4 * (b + c) + 13
    for a in range(amax + 1):
        tape, hp, state = set_SE(a + 1, b, c + 2)
        _, _, _, trace = run(tape, hp, state, n)
        lo, hi = head_extremes(trace)
        # Separator is at position -(c+2+2b) - 1 (leftmost 0 of the [false] middle)
        # Actually: left_list = [1]*(c+2) + zebra(b) + [0] + zebra(a+1) + [0]*q
        # Position of [false] separator: -(c+2 + 2b) - 1 = -(c+3+2b)
        sep_pos = -(c + 2 + 2 * b) - 1
        # head_reach below separator:
        reach_below_sep = sep_pos - lo  # how much further left than separator
        results.append((a, lo, hi, reach_below_sep))
    return results


def main():
    f = open('/home/ralf/math/bbchallenge/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/pass_shift_findings.txt', 'w')
    def log(*args):
        s = ' '.join(str(a) for a in args)
        print(s)
        f.write(s + '\n')

    log("# pass_shift Dynamics — Extensive Simulation Findings")
    log(f"# TM: {TM_STR}")
    log(f"# Lemma: srun SE(a+1, b, c+2) (4(b+c)+13) = SE(a, b+2, c+1)")
    log()

    # =====================================================================
    # 1. Grid verification.
    # =====================================================================
    log("## 1. Grid verification (a, b, c) ∈ [0..5] × [0..5] × [0..5]")
    log()
    mismatches = []
    for a in range(6):
        for b in range(6):
            for c in range(6):
                ok, _, _ = verify_pass_shift(a, b, c)
                if not ok:
                    mismatches.append((a, b, c))
    if mismatches:
        log(f"MISMATCHES: {mismatches}")
    else:
        log(f"All 6^3 = 216 cases verified. Step count 4(b+c)+13 is correct.")
    log()

    # =====================================================================
    # 2. Head reach: a-independence check.
    # =====================================================================
    log("## 2. Head-reach bounds (for a-locality argument)")
    log("For fixed (b, c), run pass_shift with varying a and measure leftmost head.")
    log("If head's leftmost is bounded independently of a, a-locality applies.")
    log()
    for (b, c) in [(0, 0), (1, 0), (0, 1), (2, 0), (0, 2), (1, 1), (2, 1), (1, 2), (3, 2)]:
        results = a_independence_check(b, c, 6)
        # Report: for large a, does the head-reach saturate?
        leftmosts = [lo for (_, lo, _, _) in results]
        # If leftmost is the same for a >= some threshold, that's a-independence.
        # Check: for a >= 2 (say), is leftmost constant?
        if len(set(leftmosts[2:])) == 1:
            satur = f"saturates at a=2 (leftmost={leftmosts[2]})"
        elif len(set(leftmosts[3:])) == 1:
            satur = f"saturates at a=3 (leftmost={leftmosts[3]})"
        else:
            satur = f"leftmosts per a: {leftmosts}"
        log(f"  (b={b}, c={c}): {satur}")
    log()
    log("**Interpretation**: If leftmost saturates, pass_shift for large enough a")
    log("is determined by a bounded prefix of the left tape (the zebra a deeper")
    log("cells are untouched), giving a-locality reduction.")
    log()

    # =====================================================================
    # 3. Phase decomposition.
    # =====================================================================
    log("## 3. Phase decomposition (states visited)")
    log("Format: (a,b,c): A_len, B→C transitions, C_len, final E steps.")
    log()
    for (a, b, c) in [(0, 0, 0), (1, 0, 0), (0, 0, 1), (0, 0, 2),
                      (0, 1, 0), (0, 2, 0), (1, 1, 0), (1, 0, 1),
                      (0, 1, 1), (2, 0, 2), (1, 2, 1), (3, 1, 1)]:
        ok, trace, _ = verify_pass_shift(a, b, c)
        states = state_sequence(trace)
        # Count phase lengths.
        # Phase A: from start until first B.
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        # Phase C: from first B until returning to E.
        idx_post_B = first_B
        while idx_post_B < len(states) and states[idx_post_B] != STE:
            idx_post_B += 1
        A_len = first_B
        C_len = idx_post_B - first_B
        D_len = len(states) - 1 - idx_post_B
        total = len(states) - 1
        log(f"  ({a},{b},{c}): A={A_len} (steps 0..{A_len-1}), "
            f"C={C_len} (..{idx_post_B-1}), D={D_len} "
            f"(total={total}={4*(b+c)+13})")
    log()

    # =====================================================================
    # 4. Dependence of phase lengths on (a, b, c).
    # =====================================================================
    log("## 4. Phase-length formulas (empirical)")
    log()
    log("Phase A length as a function of c, with b=0, a=0:")
    for c in range(6):
        _, trace, _ = verify_pass_shift(0, 0, c)
        states = state_sequence(trace)
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        log(f"  c={c}: Phase A = {first_B}")
    log()
    log("Phase A length as a function of b, with c=0, a=0:")
    for b in range(6):
        _, trace, _ = verify_pass_shift(0, b, 0)
        states = state_sequence(trace)
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        log(f"  b={b}: Phase A = {first_B}")
    log()
    log("Phase A length as a function of a (b=0, c=0):")
    for a in range(6):
        _, trace, _ = verify_pass_shift(a, 0, 0)
        states = state_sequence(trace)
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        log(f"  a={a}: Phase A = {first_B}")
    log()
    log("Phase C length (and full decomposition) for (a, b=0, c=0):")
    for a in range(6):
        _, trace, _ = verify_pass_shift(a, 0, 0)
        states = state_sequence(trace)
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        idx_post_B = first_B
        while idx_post_B < len(states) and states[idx_post_B] != STE:
            idx_post_B += 1
        log(f"  a={a}: A={first_B}, C={idx_post_B - first_B}, D={len(states)-1-idx_post_B}")
    log()

    # =====================================================================
    # 5. c-bridge conjecture (various step offsets).
    # =====================================================================
    log("## 5. c-bridge conjecture (finding right offset pair)")
    log("Conjecture: SE(a+1, b, c+3) after K1 steps ≡ SE(a+1, b, c+2) after K2 steps")
    log("          modulo position translation AND one extra `true` elsewhere on tape.")
    log()
    log("Testing offsets (K1, K2) = (3, 0): SE(a+1, b, c+3) 3 steps vs SE(a+1, b, c+2) initial")
    for (a, b, c) in [(0, 0, 0), (0, 0, 1), (0, 0, 2), (1, 0, 0), (0, 1, 0),
                      (1, 1, 0), (1, 0, 1), (2, 0, 2), (2, 1, 1), (0, 2, 1)]:
        ok, shift, info = test_cbridge(a, b, c, 3, 0)
        log(f"  (a={a}, b={b}, c={c}): {info}")
    log()
    log("Testing offsets (K1, K2) = (4, 1): SE(a+1, b, c+3) 4 steps vs SE(a+1, b, c+2) 1 step")
    for (a, b, c) in [(0, 0, 0), (0, 0, 1), (0, 0, 2), (1, 0, 0), (0, 1, 0),
                      (1, 1, 0), (1, 0, 1), (2, 0, 2)]:
        ok, shift, info = test_cbridge(a, b, c, 4, 1)
        log(f"  (a={a}, b={b}, c={c}): {info}")
    log()
    log("## 5b. Full-bridge verification")
    log("Claim: `SE(a+1, b, c+3)` after 3 steps has the same SConfig as")
    log("     `{SE(a+1, b, c+2) initial with right=[true]}`.")
    log("Then from that intermediate, running 4(b+c)+13 steps (pass_shift c steps)")
    log("and 1 more step gives `SE(a, b+2, c+2)` (pass_shift c+1 output).")
    log()
    def run_with_right_extra(a1, b, c2, extra_right, n):
        """Run pass_shift input SE(a1, b, c2) modified with extra cells in right."""
        tape, hp, state = set_SE(a1, b, c2)
        # Write extra_right to positions hp+1, hp+2, ...
        for i, v in enumerate(extra_right):
            tape[hp + 1 + i] = v
        tape, hp, state, trace = run(tape, hp, state, n)
        return tape, hp, state

    log("Verify: run SE(a+1,b,c+2) with extra right=[true] for 4(b+c)+13 steps,")
    log("then 1 more step. Should equal SE(a, b+2, c+2).")
    log()
    for (a, b, c) in [(0,0,0), (0,0,1), (1,0,0), (0,1,0), (0,0,2), (1,1,0), (0,2,1), (2,1,1)]:
        tape, hp, state = run_with_right_extra(a+1, b, c+2, [1], 4*(b+c)+13 + 1)
        ok = matches_SE(tape, hp, state, a, b+2, c+2)
        log(f"  (a={a},b={b},c={c}): pass_shift(c+1) via bridge = {'OK' if ok else 'FAIL'}")
    log()
    log("If all OK, then `pass_shift(c+1)` = 3 prefix steps + pass_shift(c)-like run")
    log("of 4(b+c)+13 + 1 = 4(b+c)+14 steps on modified right tape = 4(b+c)+17 total.")
    log()

    # =====================================================================
    # 6. Examining phase A dynamics for pattern extraction.
    # =====================================================================
    log("## 6. Phase A micro-dynamics (state sequence per config)")
    log()
    for (a, b, c) in [(0, 0, 0), (0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 1, 0), (0, 2, 0)]:
        _, trace, _ = verify_pass_shift(a, b, c)
        states = state_sequence(trace)
        try:
            first_B = states.index(STB)
        except ValueError:
            first_B = len(states)
        phaseA_states = [STATE_NAMES[s] for s in states[:first_B + 2]]
        log(f"  (a={a}, b={b}, c={c}): {''.join(phaseA_states)}")
    log()

    # =====================================================================
    # 7. Head-motion trajectory for a specific case.
    # =====================================================================
    log("## 7. Head trajectory for (a=1, b=0, c=1): 17 steps")
    log()
    _, trace, _ = verify_pass_shift(1, 0, 1)
    log(f"  step  hp   state")
    for i, (hp, st) in enumerate(trace):
        log(f"  {i:4d}  {hp:4d}  {STATE_NAMES[st]}")
    log()

    # =====================================================================
    # 8. Step-count breakdown for all (a, b, c) in a smaller grid.
    # =====================================================================
    log("## 8. Phase-length table for (a, b, c) ∈ [0..3]^3")
    log()
    log("  a b c | A len  C len  D len  Total  4(b+c)+13")
    log("  ----- | ------ ------ ------ -----  ---------")
    for a in range(4):
        for b in range(4):
            for c in range(4):
                _, trace, _ = verify_pass_shift(a, b, c)
                states = state_sequence(trace)
                try:
                    first_B = states.index(STB)
                except ValueError:
                    first_B = len(states)
                idx_post_B = first_B
                while idx_post_B < len(states) and states[idx_post_B] != STE:
                    idx_post_B += 1
                A_len = first_B
                C_len = idx_post_B - first_B
                D_len = len(states) - 1 - idx_post_B
                total = len(states) - 1
                expected = 4 * (b + c) + 13
                log(f"  {a} {b} {c} | {A_len:>6d} {C_len:>6d} {D_len:>6d} {total:>5d}  {expected}")
    log()

    # =====================================================================
    # 9. Right-tape behavior during the run (for run_right_append feasibility).
    # =====================================================================
    log("## 9. Right-tape occupancy during pass_shift (a=0, b=0, c=0)")
    log()
    log("The 'right tape' in the BusyLean Config (everything to the right of head,")
    log("as seen by listHead/listTail) starts empty for SE configs.  During the run,")
    log("it grows when head moves L and shrinks when head moves R.")
    log()
    tape, hp, state = set_SE(1, 0, 2)
    # Track right-tape non-zero extent throughout.
    log("  step  hp  state  rightmost_nonzero_in_run")
    for i in range(14):
        # Rightmost non-zero position to the right of head
        rightmost = hp
        for pos in range(hp, hp + 100):
            if tape[pos] != 0:
                rightmost = pos
        log(f"  {i:>4d}  {hp:>3d}  {STATE_NAMES[state]}     {rightmost}")
        if i < 13:
            tape, hp, state, halted = step(tape, hp, state)
            if halted: break
    log()

    f.close()

if __name__ == "__main__":
    main()
