#!/usr/bin/env python3
"""Hunt for a 'zebra cycle' in the TM dynamics.

Searches for step counts N and intermediate states X such that running N steps
from X with `zebra (b+1) *> rest` on the left yields an analogous state with
`zebra b *> rest` on the left, where `rest` is left untouched (i.e., head does
not visit cells past the zebra boundary).

The ones_cycle3 pattern (3 steps shifting ones(c+2)→ones(c+1)) gives us the
c-induction.  We want an analogous clean cycle for zebra.

Findings are written to `zebra_cycle_findings.txt`.
"""

import resource
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

from collections import defaultdict

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
    return [0, 1] * k

def step_once(tape, hp, state):
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

def run_n(tape, hp, state, n):
    """Run n steps.  Track min/max head positions visited."""
    hp_min = hp
    hp_max = hp
    for _ in range(n):
        tape, hp, state, halted = step_once(tape, hp, state)
        if halted:
            return tape, hp, state, True, hp_min, hp_max
        hp_min = min(hp_min, hp)
        hp_max = max(hp_max, hp)
    return tape, hp, state, False, hp_min, hp_max

def build_tape(left_content, head_val, right_content, head_pos=0):
    """Build tape dict: left_content is list at positions head_pos-1, head_pos-2, ...
    right_content is at positions head_pos+1, head_pos+2, ..."""
    tape = defaultdict(int)
    for i, v in enumerate(left_content):
        tape[head_pos - 1 - i] = v
    tape[head_pos] = head_val
    for i, v in enumerate(right_content):
        tape[head_pos + 1 + i] = v
    return tape

def extract_tape(tape, hp_min, hp_max, hp):
    """Get tape content from hp_min to hp_max, and left/right of head."""
    left = [tape[hp - 1 - i] for i in range(hp - hp_min + 1)]  # from hp-1 going left
    # Truncate to last nonzero
    while left and left[-1] == 0:
        left.pop()
    right = [tape[hp + 1 + i] for i in range(hp_max - hp + 1)]
    while right and right[-1] == 0:
        right.pop()
    return tape[hp], left, right

def test_cycle(b_start, b_end, N, init_state, init_left_prefix, init_head_val, init_right, rest_cell=0, a_depth=10):
    """Test: run N steps starting from init config with zebra(b_start) at some depth.
    Check if end config has zebra(b_end) at same depth with same state/head.

    init_left_prefix: fixed prefix before the zebra (closer to head), e.g., [true, true] for ones 2.
    init_right: fixed right (e.g. R).

    Returns (matches, details).
    """
    # Build left content (from head going left): init_left_prefix, then zebra(b_start), then (rest_cell)*>
    # rest_cell default 0 means "all zeros beyond".  We use a_depth padding.
    left_content_start = init_left_prefix + zebra(b_start) + [0] * a_depth
    left_content_end   = init_left_prefix + zebra(b_end)   + [0] * a_depth

    tape_start = build_tape(left_content_start, init_head_val, init_right[:])
    tape_start_hp = 0
    tape, hp, state, halted, hp_min, hp_max = run_n(tape_start, 0, init_state, N)
    if halted:
        return False, f"halted in {N} steps"

    # Check end: does tape match expected?
    expected_tape = build_tape(left_content_end, init_head_val, [])  # right may differ, don't compare
    # Compare head and left.
    if state != init_state:
        return False, f"state differs: {STATE_NAMES[init_state]} vs {STATE_NAMES[state]}"
    if tape[hp] != init_head_val:
        return False, f"head value differs: {init_head_val} vs {tape[hp]}"

    # Compare left tape (of end config) with expected_tape's left.
    max_left_depth = len(left_content_end) + 5
    mismatches = []
    for i in range(1, max_left_depth):
        actual = tape[hp - i]
        expected = expected_tape[-i]
        if actual != expected:
            mismatches.append((i, actual, expected))
    if mismatches:
        return False, f"left tape differs at: {mismatches[:5]}"

    # Get the right side content (for f(R) computation).
    head_val, left_readback, right_readback = extract_tape(tape, hp_min, hp_max, hp)
    return True, f"state={STATE_NAMES[state]}, head={head_val}, right={right_readback}, hp_min={hp_min}, hp_max={hp_max}"


def hunt_cycle(max_N=30, max_b=4):
    """Search for a clean b-cycle across many starting configs."""
    results = []

    # Candidate starting states.
    candidates = []

    # 1. State E, head=false, left prefix = ones 2 before zebra
    candidates.append(("E0-ones2", STE, 0, [1, 1], []))
    candidates.append(("E0-ones2-R[t]", STE, 0, [1, 1], [1]))

    # 2. State E, head=false, left prefix = ones 1 before zebra
    candidates.append(("E0-ones1", STE, 0, [1], []))

    # 3. State E, head=false, no prefix
    candidates.append(("E0-noprefix", STE, 0, [], []))

    # 4. State F, head=true, various prefixes
    candidates.append(("F1-noprefix", STF, 1, [], []))
    candidates.append(("F1-ones2", STF, 1, [1, 1], []))

    # 5. State B, head=true, various prefixes (for AB-walk phase)
    candidates.append(("B1-noprefix", STB, 1, [], []))
    candidates.append(("B1-ones2", STB, 1, [1, 1], []))

    # 6. State A, head=false, various
    candidates.append(("A0-noprefix", STA, 0, [], []))
    candidates.append(("A0-ones2", STA, 0, [1, 1], []))

    for name, state, head_val, prefix, right_init in candidates:
        for N in range(2, max_N + 1):
            ok, details = test_cycle(2, 1, N, state, prefix, head_val, right_init)
            if ok:
                # Also verify for b=3→2 (to rule out coincidental match at b=1).
                ok2, _ = test_cycle(3, 2, N, state, prefix, head_val, right_init)
                ok3, _ = test_cycle(4, 3, N, state, prefix, head_val, right_init)
                if ok2 and ok3:
                    results.append((name, state, prefix, head_val, right_init, N, details))

    return results


def trace_initial_phase(b, c, a, n_steps=30):
    """Trace the full initial phase of pass_shift for debugging."""
    # Build initial: state E, left = ones(c+2) *> zebra(b) *> [false] *> zebra(a+1) *> blank
    left = [1]*(c+2) + zebra(b) + [0] + zebra(a+1)
    tape = build_tape(left, 0, [])
    trace = []
    hp = 0
    state = STE
    for i in range(n_steps):
        if i > 0:
            tape, hp, state, halted = step_once(tape, hp, state)
            if halted: break
        # Collect info
        left_show = [tape[hp - 1 - j] for j in range(min(hp - (-(c+2)-len(zebra(b))-1-len(zebra(a+1))-5), 15))]
        right_show = [tape[hp + 1 + j] for j in range(min(5, 5))]
        trace.append((i, state, hp, tape[hp], left_show, right_show))
    return trace


def main():
    f = open('/home/ralf/math/bbchallenge/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE/zebra_cycle_findings.txt', 'w')
    def log(*args):
        s = ' '.join(str(a) for a in args)
        print(s)
        f.write(s + '\n')

    log("# Zebra Cycle Search — Findings")
    log(f"# TM: {TM_STR}")
    log()
    log("## Goal")
    log()
    log("Find starting state X, step count N, and auxiliary right suffix pattern")
    log("such that running N steps from X with zebra(b+1) on left (at some depth)")
    log("yields an analogous state with zebra(b) on left, WITH the head position")
    log("at the same relative depth and state unchanged.")
    log()
    log("If found, this gives a simp-provable 'zebra cycle' that closes the")
    log("b-induction for pass_shift.")
    log()

    # =====================================================================
    # 1. Exhaustive cycle search.
    # =====================================================================
    log("## 1. Exhaustive cycle search")
    log("Testing many (state, head, prefix, right_init) starting configs for")
    log("step counts N = 2 to 30.  Success = consistent cycle for b=2→1, 3→2, 4→3.")
    log()
    results = hunt_cycle(max_N=30)
    if not results:
        log("NO CLEAN CYCLE FOUND in the tested starting configurations.")
    else:
        for name, state, prefix, head_val, right_init, N, details in results:
            log(f"  Candidate: {name}, state={STATE_NAMES[state]}, prefix={prefix}, "
                f"head={head_val}, right_init={right_init}, N={N}")
            log(f"    details: {details}")
    log()

    # =====================================================================
    # 2. Trace pass_shift for (a=0, b=2, c=0) and identify mid-run states.
    # =====================================================================
    log("## 2. Full pass_shift trace for (a=0, b=2, c=0), 21 steps")
    log()
    # Build SE_Config (a+1)=1, b=2, c+2=2.
    # Total steps: 4*(2+0)+13 = 21.
    left = [1, 1] + zebra(2) + [0] + zebra(1) + [0] * 10
    tape = build_tape(left, 0, [])
    hp = 0
    state = STE
    log(f"  step  state  hp   head  left(r→l, to 15)                    right(l→r, to 10)")
    for i in range(22):
        left_show = [tape[hp - 1 - j] for j in range(15)]
        right_show = [tape[hp + 1 + j] for j in range(10)]
        log(f"  {i:>4d}   {STATE_NAMES[state]}    {hp:>3d}   {tape[hp]}    "
            f"{left_show}  {right_show}")
        if i < 21:
            tape, hp, state, halted = step_once(tape, hp, state)
            if halted: break
    log()

    # =====================================================================
    # 3. For each step, identify if left/right matches a known pattern.
    # =====================================================================
    log("## 3. State sequence patterns for pass_shift(a, b, c)")
    log()
    # For small a, b, c values, list the state sequence.
    for (a, b, c) in [(0,0,0), (0,1,0), (0,2,0), (0,3,0), (0,4,0),
                      (0,0,1), (0,1,1), (0,2,1),
                      (1,1,1), (2,2,2)]:
        left = [1]*(c+2) + zebra(b) + [0] + zebra(a+1) + [0] * 20
        tape = build_tape(left, 0, [])
        hp = 0
        state = STE
        n = 4*(b+c)+13
        seq = []
        for _ in range(n):
            seq.append(STATE_NAMES[state])
            tape, hp, state, halted = step_once(tape, hp, state)
            if halted: break
        seq.append(STATE_NAMES[state])
        log(f"  (a={a}, b={b}, c={c}): {''.join(seq)} ({n} steps)")
    log()

    # =====================================================================
    # 4. Identify "matching" state sequences at different b values.
    # =====================================================================
    log("## 4. State sequence for (b=0, 1, 2, 3) with fixed a=0, c=0")
    log("Look for repeating patterns that might indicate the b-cycle.")
    log()
    for b in range(5):
        left = [1, 1] + zebra(b) + [0] + zebra(1) + [0] * 20
        tape = build_tape(left, 0, [])
        hp = 0
        state = STE
        n = 4*b+13
        seq = []
        hp_seq = []
        for _ in range(n):
            seq.append(STATE_NAMES[state])
            hp_seq.append(hp)
            tape, hp, state, halted = step_once(tape, hp, state)
            if halted: break
        seq.append(STATE_NAMES[state])
        log(f"  b={b}: {''.join(seq)} ({n} steps, hp in [{min(hp_seq)},{max(hp_seq)}])")
    log()

    # Differences between consecutive b's — look for prefix/suffix.
    log("## 4b. Alignment of state sequences (b+1 vs b)")
    log()
    for b in range(5):
        left = [1, 1] + zebra(b) + [0] + zebra(1) + [0] * 20
        tape = build_tape(left, 0, [])
        hp = 0; state = STE
        n = 4*b+13
        seq_b = []
        for _ in range(n):
            seq_b.append(STATE_NAMES[state])
            tape, hp, state, halted = step_once(tape, hp, state)
            if halted: break
        seq_b.append(STATE_NAMES[state])

        left2 = [1, 1] + zebra(b+1) + [0] + zebra(1) + [0] * 20
        tape2 = build_tape(left2, 0, [])
        hp2 = 0; state2 = STE
        n2 = 4*(b+1)+13
        seq_b1 = []
        for _ in range(n2):
            seq_b1.append(STATE_NAMES[state2])
            tape2, hp2, state2, halted = step_once(tape2, hp2, state2)
            if halted: break
        seq_b1.append(STATE_NAMES[state2])

        # Compare: find longest common prefix and longest common suffix.
        pfx = 0
        while pfx < len(seq_b) and pfx < len(seq_b1) and seq_b[pfx] == seq_b1[pfx]:
            pfx += 1
        sfx = 0
        while sfx < len(seq_b) - pfx and sfx < len(seq_b1) - pfx and seq_b[-1-sfx] == seq_b1[-1-sfx]:
            sfx += 1
        middle_b  = seq_b[pfx:len(seq_b)-sfx]
        middle_b1 = seq_b1[pfx:len(seq_b1)-sfx]
        log(f"  b={b}: pfx_len={pfx}, sfx_len={sfx}, extra_middle={len(middle_b1) - len(middle_b)}")
        log(f"    b  middle: {''.join(middle_b)}")
        log(f"    b+1 middle: {''.join(middle_b1)}")
    log()

    # =====================================================================
    # 5. Head-trajectory comparison (b vs b+1).
    # =====================================================================
    log("## 5. Head trajectories for b=2 vs b=3 (both a=0, c=0)")
    log()
    for b in [2, 3]:
        left = [1, 1] + zebra(b) + [0] + zebra(1) + [0] * 20
        tape = build_tape(left, 0, [])
        hp = 0; state = STE
        n = 4*b+13
        traj = [(0, STATE_NAMES[state], hp, tape[hp])]
        for step in range(1, n+1):
            tape, hp, state, halted = step_once(tape, hp, state)
            traj.append((step, STATE_NAMES[state], hp, tape[hp]))
            if halted: break
        log(f"  b={b}: {traj}")
    log()

    # =====================================================================
    # 6. Test potential "double-cycle" pattern: maybe pairs of b take 8 steps.
    # =====================================================================
    log("## 6. Test '8-step doubled cycle' hypothesis")
    log("Maybe: consuming 2 zebra pairs at once takes 8 steps.")
    log()
    # Try: from state E head=false, left = ones 2 *> zebra (b+2) *> rest (b generic),
    # after N steps reach state E head=false with left = ones 2 *> zebra b *> rest
    # (dropping 2 zebras at once).
    for N in range(4, 25):
        # Test b_start=3, b_end=1 (diff 2): consistent for various b?
        ok1, _ = test_cycle(3, 1, N, STE, [1, 1], 0, [])
        ok2, _ = test_cycle(4, 2, N, STE, [1, 1], 0, [])
        ok3, _ = test_cycle(5, 3, N, STE, [1, 1], 0, [])
        if ok1 and ok2 and ok3:
            log(f"  Cycle (drop 2 zebras) works with N={N} steps! (state=E, prefix=[1,1])")
    log()

    # =====================================================================
    # 7. Test: maybe the "cycle" requires specific right pattern to start.
    # =====================================================================
    log("## 7. Test with right containing known pattern")
    log("After phase A's EF pings, right accumulates [0,1]*k.  Maybe cycle needs this.")
    log()
    for rpat_name, rpat in [("empty", []), ("[1]", [1]), ("[0,1]", [0, 1]),
                             ("[1,1]", [1, 1]), ("[0,1,0,1]", [0, 1, 0, 1])]:
        for N in range(2, 20):
            ok1, _ = test_cycle(2, 1, N, STE, [1, 1], 0, rpat)
            ok2, _ = test_cycle(3, 2, N, STE, [1, 1], 0, rpat)
            if ok1 and ok2:
                log(f"  right_init={rpat_name}, N={N}: CYCLE FOUND")
    log()

    # =====================================================================
    # 8. Head-position extremes during zebra cycle.
    # =====================================================================
    log("## 8. Head-depth reach for (b_start=3, N variable)")
    log()
    left = [1, 1] + zebra(3) + [0] + zebra(1) + [0] * 20
    tape = build_tape(left, 0, [])
    hp = 0; state = STE
    hp_min_list = [hp]
    for step in range(1, 26):
        tape, hp, state, halted = step_once(tape, hp, state)
        hp_min_list.append(min(hp_min_list[-1], hp))
        if halted: break
    log(f"  leftmost_head per step: {hp_min_list}")
    log(f"  Step where head reaches -3 (start of zebra 3): {hp_min_list.index(-3) if -3 in hp_min_list else 'never'}")
    log(f"  Step where head reaches -5 (mid-zebra): {hp_min_list.index(-5) if -5 in hp_min_list else 'never'}")
    log(f"  Step where head reaches -7 (end-zebra): {hp_min_list.index(-7) if -7 in hp_min_list else 'never'}")
    log(f"  Step where head reaches -9 (beyond zebra): {hp_min_list.index(-9) if -9 in hp_min_list else 'never'}")
    log()

    f.close()


if __name__ == "__main__":
    main()
