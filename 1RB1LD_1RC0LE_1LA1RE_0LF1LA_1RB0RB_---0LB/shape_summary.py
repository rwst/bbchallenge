#!/usr/bin/env python3
"""Concise shape summary: per state, enumerate the "active region" shape
schemata, ignoring far-left context.

For each state, report:
  - Head value (0 or 1)
  - "Active region" pattern: cells in a narrow window around the head,
    parameterized by:
      * mod-3 class of the current block the head is in (if on 1)
      * head position within that block (mod 3)
      * structure of one-step neighbors
  - The TM transition applied at this config and its effect.

Dominant schemata per state should total ~10–15 (useful for ClosedSet).
"""
import os, resource, sys, time
from collections import Counter, defaultdict

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STATE_NAMES


def active_shape(t):
    """Symbolic description of the head's immediate neighborhood.

    Returns (state_name, head_val, context_tag) where context_tag captures:
      - If head on 1: (block_len_mod3, pos_in_block_mod3, l_neighbor, r_neighbor)
      - If head on 0: (l_context, r_context) where each is a tag like
        'block-start', 'block-mid', 'blank'.
    """
    st = STATE_NAMES[t.state]
    hv = t.arr[t.hp]
    # L/R immediate neighbors
    def cell_at(p):
        if p < t.lo - 10 or p > t.hi + 10:
            return 0  # blank
        return t.arr[p]
    l1 = cell_at(t.hp - 1)
    r1 = cell_at(t.hp + 1)

    if hv == 1:
        # Measure current block
        l_ones = 0
        p = t.hp - 1
        while p >= t.lo and t.arr[p] == 1:
            l_ones += 1; p -= 1
        r_ones = 0
        p = t.hp + 1
        while p <= t.hi and t.arr[p] == 1:
            r_ones += 1; p += 1
        block_len = l_ones + 1 + r_ones
        tag = (block_len % 3, l_ones % 3, l1, r1)
    else:
        # head on 0
        # Are we adjacent to 1-block on left? right?
        # And how many 0s around
        l0 = 0
        p = t.hp - 1
        while p >= t.lo - 5 and t.arr[p] == 0:
            l0 += 1; p -= 1
        r0 = 0
        p = t.hp + 1
        while p <= t.hi + 5 and t.arr[p] == 0:
            r0 += 1; p += 1
        past_L = (t.hp - l0 - 1 < t.lo)  # only blanks to left of run of 0s
        past_R = (t.hp + r0 + 1 > t.hi)  # only blanks to right
        tag = ("0s_L", l0, "0s_R", r0, "blank_L", past_L, "blank_R", past_R)

    return (st, hv, tag)


def trace(max_steps=5 * 10**7, time_budget=60, warmup=200):
    t = FastTape()
    for _ in range(warmup):
        if t.halted: break
        t.step_one()
    shapes = defaultdict(Counter)
    start = time.monotonic()
    count = 0
    while t.steps < max_steps:
        if t.halted: break
        s = active_shape(t)
        shapes[s[0]][s] += 1
        count += 1
        if time.monotonic() - start > time_budget:
            break
        t.step_one()
    elapsed = time.monotonic() - start
    print(f"Traced {count:,} configs in {elapsed:.1f}s (steps {t.steps:,})\n")
    for st in "ABCDEF":
        sigs = shapes[st]
        total = sum(sigs.values())
        print(f"=== State {st} ({total:,} configs, {len(sigs)} distinct active shapes) ===")
        cumulative = 0
        for sig, c in sigs.most_common():
            cumulative += c
            pct = 100 * c / total if total else 0
            cum_pct = 100 * cumulative / total if total else 0
            state, hv, tag = sig
            print(f"  {c:8d} ({pct:5.2f}%)  h={hv}  {fmt_tag(hv, tag)}  cum={cum_pct:.1f}%")
            if cum_pct >= 99.9:
                print(f"  (remaining {len(sigs) - sigs.most_common().index((sig, c)) - 1} "
                      f"shapes account for <0.1%)")
                break
        print()


def fmt_tag(hv, tag):
    if hv == 1:
        block_mod3, pos_mod3, l, r = tag
        return (f"on-1 inside block(len≡{block_mod3} mod 3) at pos≡{pos_mod3} mod 3  "
                f"L-nbr={l} R-nbr={r}")
    else:
        _, l0, _, r0, _, bl, _, br = tag
        l_str = "blank" if bl else f"0^{l0} then 1"
        r_str = "blank" if br else f"0^{r0} then 1"
        return f"on-0  L={l_str:<12}  R={r_str}"


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 20_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    trace(ms, tb)
