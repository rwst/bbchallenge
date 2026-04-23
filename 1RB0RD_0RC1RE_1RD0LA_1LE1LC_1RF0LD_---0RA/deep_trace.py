#!/usr/bin/env python3
"""Deep trace of R2 (and R1 for comparison): parse each step's tape into a
structured (prefix, head_cell, suffix) representation so we can SEE which
shift-lemma pattern matches at every point.

Output columns:
  s       step index
  state   A..F
  h       head symbol under the head
  dir     direction/instruction applied this step (from prev step)
  pos     head absolute position (for drift analysis)
  left    compact view of left tape (everything < hp), blank-trimmed
  right   compact view of right tape (everything > hp), blank-trimmed

Then a post-pass recognizes patterns:
  - ones^n  (maximal run of 1s)
  - zebra^n = (10)^n or (01)^n
  - aBlocks^n = (1011)^n
  - tzebra = [T] followed by zebra (the 'true-zebra' shape)
and prints matched segments.

Usage:
  ./deep_trace.py R2 1      # R2 at k=1, full
  ./deep_trace.py R2 2
  ./deep_trace.py R1 1
"""

from sim import setup_C, STATE_NAMES, detect_C_c1, TR, Tape
import sys

# Step budget formulas from the wiki
def dt_R1(k): return 12*k*k + 53*k + 28
def dt_R2(k): return 12*k*k + 77*k + 103
def dt_R3(k): return 12*k*k + 101*k + 184


def compact_run(cells):
    """Turn a list of 0/1s into a compact textual form with structural parsing.

    Try maximal greedy parses of:
      - (1011)^n   = aBlocks  -> "A{n}"
      - (10)^n     = zebra    -> "Z{n}"     (right-zebra; 1 at low index)
      - (01)^n                -> "z{n}"     (left-zebra; 0 at low index)
      - 1^n                   -> "1{n}"
      - 0^n                   -> "0{n}"
    Return space-separated pieces.
    """
    n = len(cells)
    pieces = []
    i = 0
    while i < n:
        # Try (1011)^k (aBlocks) — highest structural priority at multiples of 4
        if i + 4 <= n and cells[i:i+4] == [1, 0, 1, 1]:
            k = 1
            while i + 4 * (k + 1) <= n and cells[i + 4*k : i + 4*(k+1)] == [1, 0, 1, 1]:
                k += 1
            # But this can also be (10)(11) — don't collapse if just k=1 and
            # the next 4 wouldn't extend; we still emit A1 for clarity.
            pieces.append(f"A{k}" if k > 1 else "A1")
            i += 4 * k
            continue
        # Try (10)^k
        if i + 2 <= n and cells[i:i+2] == [1, 0]:
            k = 1
            while i + 2 * (k + 1) <= n and cells[i + 2*k : i + 2*(k+1)] == [1, 0]:
                k += 1
            if k >= 1:
                pieces.append(f"Z{k}" if k > 1 else "(10)")
                i += 2 * k
                continue
        # Try (01)^k
        if i + 2 <= n and cells[i:i+2] == [0, 1]:
            k = 1
            while i + 2 * (k + 1) <= n and cells[i + 2*k : i + 2*(k+1)] == [0, 1]:
                k += 1
            if k >= 1:
                pieces.append(f"z{k}" if k > 1 else "(01)")
                i += 2 * k
                continue
        # Try 1^k
        if cells[i] == 1:
            k = 1
            while i + k < n and cells[i+k] == 1:
                k += 1
            pieces.append(f"1^{k}" if k > 1 else "1")
            i += k
            continue
        # 0-runs (should be rare in trimmed views)
        k = 1
        while i + k < n and cells[i+k] == 0:
            k += 1
        pieces.append(f"0^{k}" if k > 1 else "0")
        i += k
    return " ".join(pieces)


def trim_cells(arr, lo, hi):
    """Return cells[lo..hi] trimming leading/trailing zeros."""
    while lo <= hi and arr[lo] == 0:
        lo += 1
    while hi >= lo and arr[hi] == 0:
        hi -= 1
    return [arr[i] for i in range(lo, hi + 1)], lo, hi


def snapshot(t):
    """Return a dict describing the tape right now: state, head, left compact,
    right compact, raw cells trimmed."""
    # Left cells: indices 0..hp-1
    n = len(t.arr)
    # Find leftmost nonblank on the left side
    l_lo = t.lo
    # But we also want to include any cells beyond lo (though there shouldn't be)
    # Head cell:
    head = int(t.arr[t.hp])
    # Left: [l_lo .. hp-1]
    if t.hp - 1 >= l_lo:
        left_cells = [int(t.arr[i]) for i in range(l_lo, t.hp)]
    else:
        left_cells = []
    # Right: [hp+1 .. t.hi]
    if t.hi >= t.hp + 1:
        right_cells = [int(t.arr[i]) for i in range(t.hp + 1, t.hi + 1)]
    else:
        right_cells = []
    # Strip leading/trailing blanks in left/right for display clarity.
    # Left: trim leading zeros (nearest to the edge); keep trailing (adjacent to head)
    while left_cells and left_cells[0] == 0:
        left_cells.pop(0)
    while right_cells and right_cells[-1] == 0:
        right_cells.pop()
    return {
        "state": STATE_NAMES[t.state],
        "head": head,
        "hp": t.hp,
        "left": left_cells,
        "right": right_cells,
        "left_cmp": compact_run(left_cells),
        "right_cmp": compact_run(right_cells),
    }


def format_snap(s, snap):
    lc = snap["left_cmp"] or "."
    rc = snap["right_cmp"] or "."
    # Replace spaces in left/right with a readable spacer
    return (f"s={s:>4}  {snap['state']},{snap['head']}  "
            f"hp={snap['hp']:>4}  "
            f"L=[{lc}]  R=[{rc}]")


def run_rule(name, k, full_steps=None):
    """Run a rule's macro step and print a full structured trace.
    R1(k) = C(1, 3k) -> C(0, 8k+6) in dt_R1(k) steps
    R2(k) = C(2, 3k+1) -> C(0, 8k+16) in dt_R2(k) steps
    R3(k) = C(2, 3k+2) -> C(0, 8k+22) in dt_R3(k) steps
    """
    if name == "R1":
        a0, b0 = 1, 3 * k
        total = dt_R1(k)
    elif name == "R2":
        a0, b0 = 2, 3 * k + 1
        total = dt_R2(k)
    elif name == "R3":
        a0, b0 = 2, 3 * k + 2
        total = dt_R3(k)
    else:
        raise SystemExit(f"unknown rule: {name}")

    if full_steps is None:
        full_steps = total

    print(f"# {name} at k={k}: C({a0},{b0}) → [target C] in {total} steps")
    print(f"# Dumping {full_steps} steps")
    print()

    t = setup_C(a0, b0)
    snaps = []
    snap0 = snapshot(t)
    snaps.append((0, snap0, None))  # (step, snap, transition_applied_to_reach_it)

    # The first snapshot is step 0. Then we step and take snapshots.
    for s in range(1, full_steps + 1):
        prev_state = t.state
        prev_sym = int(t.arr[t.hp])
        tr = TR[(prev_state, prev_sym)]  # (w, direction, ns) or None
        t.step()
        snap = snapshot(t)
        snaps.append((s, snap, (STATE_NAMES[prev_state], prev_sym, tr)))
        if t.halted:
            print(f"  HALT at step {s}")
            break

    # Print raw trace
    for (s, snap, tr) in snaps:
        line = format_snap(s, snap)
        if tr is not None:
            pstate, psym, (w, d, ns) = tr
            line += f"  (via {pstate},{psym} -> {w}{d}{STATE_NAMES[ns]})"
        print(line)

    # Post-pass analysis: find all indices where (state == A, head == T)
    # These are the iteration boundary candidates.
    print()
    print("# Iteration boundary candidates (state=A,head=1):")
    at_true_steps = [s for (s, snap, tr) in snaps if snap["state"] == "A" and snap["head"] == 1]
    print(f"  at_1_steps = {at_true_steps}")
    print(f"  count = {len(at_true_steps)}")
    if len(at_true_steps) > 1:
        print(f"  gaps   = {[at_true_steps[i+1]-at_true_steps[i] for i in range(len(at_true_steps)-1)]}")

    # State-C, head=F events (potential transitions):
    print()
    print("# State C, head=0 events:")
    cf_steps = [s for (s, snap, tr) in snaps if snap["state"] == "C" and snap["head"] == 0]
    print(f"  C_0_steps = {cf_steps}")

    # State D, head=F events:
    print()
    print("# State D, head=0 events:")
    df_steps = [s for (s, snap, tr) in snaps if snap["state"] == "D" and snap["head"] == 0]
    print(f"  D_0_steps = {df_steps}")

    # Every transition to state C or D (non-rightward into target)
    print()
    print("# All state-entry events into each state (first time after each last):")
    for st in "ABCDEF":
        entries = []
        last = None
        for (s, snap, tr) in snaps:
            if snap["state"] == st and last != st:
                entries.append(s)
            last = snap["state"]
        if entries:
            print(f"  enter-{st}: {entries}  (count={len(entries)})")


if __name__ == "__main__":
    import sys
    if len(sys.argv) < 2:
        print("Usage: deep_trace.py R1|R2|R3 [k] [steps]")
        sys.exit(1)
    name = sys.argv[1]
    k = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else None
    run_rule(name, k, steps)
