#!/usr/bin/env python3
"""Trace TM and enumerate the distinct "shape schemata" seen in each state.

For each TM step, compute a symbolic tape "shape" by:
  1. Scanning outward from the head.
  2. Recording the sequence of block sizes (runs of 1s) with their mod-3 value.
  3. Classifying the head's *offset inside a block* (if on a 1) or
     *context at separator* (if on a 0).

Then count distinct shape signatures per state, and for each common one,
record its "arithmetic pattern" (free parameters).

Output: a report of shape families per state, suitable for designing
a ClosedSet-style predicate P(c).

Memory-capped at 2 GB.
"""
import os, resource, sys, time
from collections import Counter, defaultdict

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STATE_NAMES


def blocks_and_seps_from_head(t, direction, max_items=8):
    """Starting adjacent to head (but not including it), walk outward in
    `direction` (-1 for left, +1 for right).  Return a list of items
    alternating "run(size)" and "sep(count)" where run is 1s and sep is 0s.
    Stop after max_items items or when blank is reached.
    """
    items = []
    if direction == -1:
        p = t.hp - 1
        bound_ok = lambda pp: pp >= t.lo - 50  # allow some blank padding
    else:
        p = t.hp + 1
        bound_ok = lambda pp: pp <= t.hi + 50
    # Stop collecting when past all non-blank cells
    stop_p = (t.lo if direction == -1 else t.hi)
    # Past the non-blank region, everything is 0
    # Walk outward
    cur_sym = None
    cur_len = 0
    while len(items) < max_items:
        # Check if we've gone past the non-blank region
        if direction == -1:
            if p < t.lo:
                break
        else:
            if p > t.hi:
                break
        sym = t.arr[p]
        if cur_sym is None:
            cur_sym = sym
            cur_len = 1
        elif sym == cur_sym:
            cur_len += 1
        else:
            items.append((cur_sym, cur_len))
            cur_sym = sym
            cur_len = 1
        p += direction
    if cur_sym is not None and cur_len > 0:
        items.append((cur_sym, cur_len))
    return items


def shape_signature(t):
    """Compute a symbolic signature of the tape shape around the head.

    Signature includes:
      - state
      - head_value
      - "L_pattern": tuple of ("1", mod3_class) or ("0", "1plus" or "multi")
        for the first few items walking left from head.
      - "R_pattern": same walking right.
      - head_context: if head on 1, offset mod 3 within the current block
        (in both directions).  If on 0, context tag like
        "between_blocks"/"trailing_blank"/"leading_blank".

    Uses coarse binning:
      - Block sizes: classify by size mod 3.  Since TM preserves mod-3 at
        macros, most will be mod-3-value 2.  Other values indicate
        "inside a carry" or transient states.
    """
    items_l = blocks_and_seps_from_head(t, -1, max_items=6)
    items_r = blocks_and_seps_from_head(t, +1, max_items=6)

    def classify(sym, length):
        if sym == 1:
            return ("1", length % 3)
        else:
            # classify 0-separator
            if length == 1:
                return ("0", 1)
            else:
                return ("0", "many" if length >= 2 else length)

    L = tuple(classify(s, n) for s, n in items_l)
    R = tuple(classify(s, n) for s, n in items_r)

    # Head-in-block offset (if head on 1)
    head_val = t.arr[t.hp]
    extra = None
    if head_val == 1:
        # Find the block containing the head: count 1s to the left contiguously
        l_ones = 0
        p = t.hp - 1
        while p >= t.lo and t.arr[p] == 1:
            l_ones += 1
            p -= 1
        r_ones = 0
        p = t.hp + 1
        while p <= t.hi and t.arr[p] == 1:
            r_ones += 1
            p += 1
        block_len = l_ones + 1 + r_ones
        # Position in block (L offset)
        extra = ("block_len_mod3", block_len % 3, "pos_L_mod3", l_ones % 3)
    else:
        # head_val == 0: what's around?
        # count consecutive 0s around head
        l0 = 0
        p = t.hp - 1
        while p >= t.lo and t.arr[p] == 0:
            l0 += 1; p -= 1
        r0 = 0
        p = t.hp + 1
        while p <= t.hi and t.arr[p] == 0:
            r0 += 1; p += 1
        # boundary check
        past_left = (t.hp - l0 - 1 < t.lo)
        past_right = (t.hp + r0 + 1 > t.hi)
        extra = ("L0", l0, "R0", r0, "past_L", past_left, "past_R", past_right)

    return (STATE_NAMES[t.state], head_val, L, R, extra)


def trace(max_steps=5 * 10**7, time_budget=60, warmup=200):
    """Run sim, collect shape signatures per state, report top ones."""
    t = FastTape()
    # Warm-up: skip the initial transient (first ~60 steps) so we count
    # "steady-state" shape families.
    for _ in range(warmup):
        if t.halted: break
        t.step_one()

    shapes = defaultdict(Counter)  # shapes[state] -> Counter[signature]
    start = time.monotonic()
    count = 0
    while t.steps < max_steps:
        if t.halted: break
        sig = shape_signature(t)
        shapes[sig[0]][sig] += 1
        count += 1
        if time.monotonic() - start > time_budget:
            break
        t.step_one()

    elapsed = time.monotonic() - start
    print(f"Warmup {warmup} steps; then traced {count:,} configs in {elapsed:.1f}s")
    print(f"Final step: {t.steps:,}")
    print()

    # Report per state
    for st in "ABCDEF":
        sigs = shapes[st]
        print(f"=== State {st} ({sum(sigs.values()):,} configs, "
              f"{len(sigs)} distinct shapes) ===")
        for sig, c in sigs.most_common(10):
            print(f"  {c:8d}×  {fmt_signature(sig)}")
        if len(sigs) > 10:
            print(f"  ... ({len(sigs) - 10} more)")
        print()


def fmt_signature(sig):
    st, hv, L, R, extra = sig
    # Format L, R as short strings
    def fmt_items(items):
        parts = []
        for (sym, info) in items:
            if sym == "1":
                parts.append(f"1^(≡{info}mod3)")
            else:
                parts.append(f"0^{info}" if isinstance(info, int) else f"0^{info}")
        return " | ".join(parts) if parts else "blank"

    L_s = fmt_items(L)
    R_s = fmt_items(R)
    extra_s = str(extra)
    return f"[{st}]h={hv}  L={L_s:<40}  R={R_s:<30}  {extra_s}"


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 10_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    trace(ms, tb)
