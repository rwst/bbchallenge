#!/usr/bin/env python3
"""Classify macro rules by their (input_suffix, output_suffix) deltas.

For each pair of consecutive E-turnaround events, find the minimal suffix
of the left tape that changes, and record the rule as a dictionary entry
input_suffix -> output_suffix.  Also records the step delta.

Helps discover how many distinct "local" macro rules govern the chaotic
counter.  Also independently verifies the sᵢ ≡ 2 (mod 3) invariant.
"""

import os
import resource
import sys
import time
from collections import Counter, defaultdict

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

# Reuse FastTape from deep_sim
sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STE, STATE_NAMES


def blocks_from_tape(t):
    """Extract L-to-R block sizes from the non-blank portion of tape."""
    blocks = []
    cur = 0
    for i in range(t.lo, t.hp):
        if t.arr[i] == 1:
            cur += 1
        else:
            if cur > 0:
                blocks.append(cur)
                cur = 0
    if cur > 0:
        blocks.append(cur)
    return blocks


def common_prefix_len(a, b):
    n = min(len(a), len(b))
    for i in range(n):
        if a[i] != b[i]:
            return i
    return n


def classify(max_steps=5 * 10**8, time_budget=120, max_events=None):
    t = FastTape()
    events = []
    rules = defaultdict(list)  # (in_suffix, out_suffix) -> [dt, ...]
    mod3_counts = Counter()
    max_block = 0
    last_blocks = None
    last_step = 0
    start = time.monotonic()

    while t.steps < max_steps:
        if t.halted:
            break
        if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = blocks_from_tape(t)
            if blocks:
                for s in blocks:
                    mod3_counts[s % 3] += 1
                    if s > max_block:
                        max_block = s
                if last_blocks is not None:
                    # Find shared prefix
                    pre = common_prefix_len(last_blocks, blocks)
                    in_suf = tuple(last_blocks[pre:])
                    out_suf = tuple(blocks[pre:])
                    dt = t.steps - last_step
                    rules[(in_suf, out_suf)].append(dt)
                last_blocks = blocks
                last_step = t.steps
                if max_events and len(rules) and sum(len(v) for v in rules.values()) >= max_events:
                    break
        if time.monotonic() - start > time_budget:
            print(f"  (time budget {time_budget}s hit at step {t.steps:,})")
            break
        t.step_one()

    print(f"\n=== Classify results ===")
    print(f"Steps: {t.steps:,}  elapsed: {time.monotonic() - start:.1f}s")
    print(f"mod 3 counts: {dict(mod3_counts)}")
    print(f"Max block: {max_block}")
    print(f"Distinct rules: {len(rules)}")
    print(f"Total transitions: {sum(len(v) for v in rules.values())}")
    print()

    # Group rules by input suffix structure
    print("Rules by input-suffix length:")
    by_in_len = defaultdict(list)
    for (i, o), dts in rules.items():
        by_in_len[len(i)].append((i, o, len(dts), sorted(set(dts))[:3]))
    for n in sorted(by_in_len.keys()):
        print(f"  |in|={n}: {len(by_in_len[n])} rules")

    print("\nTop 30 most frequent rules:")
    sorted_rules = sorted(rules.items(), key=lambda kv: -len(kv[1]))[:30]
    for (i, o), dts in sorted_rules:
        ds = Counter(dts)
        dts_str = ", ".join(f"dt={d}×{c}" for d, c in sorted(ds.items())[:3])
        i_str = str(list(i))
        o_str = str(list(o))
        print(f"  in={i_str:>25}  out={o_str:>25}  count={len(dts):6d}  {dts_str}")

    # Check all rules preserve invariant
    bad = []
    for (i, o), _ in rules.items():
        for s in i + o:
            if s % 3 != 2:
                bad.append(((i, o), s))
    print(f"\nRules violating s≡2(mod 3) invariant: {len(bad)}")
    if bad:
        for (pair, s) in bad[:5]:
            print(f"  {pair}: block {s} has mod3={s%3}")

    # Analyze |in|=1 rules (simple bumps): group by k value
    print("\n|in|=1 rules (simple bumps): (k_in, k_out, dt) occurrences")
    in1 = [(i[0], o[0], dts[0], len(dts))
           for (i, o), dts in rules.items()
           if len(i) == 1 and len(o) == 1 and len(set(dts)) == 1]
    in1.sort()
    # Verify they match 16j+17 formula for k=6j+2
    violates_bump = 0
    consistent = 0
    for k_in, k_out, dt, cnt in in1:
        if k_out == k_in + 3:
            j = (k_in - 2) // 6
            if k_in == 6 * j + 2 and dt == 16 * j + 17:
                consistent += 1
                continue
        violates_bump += 1
    print(f"  {consistent} rules match simple_bump(k=6j+2, dt=16j+17, k+3)")
    print(f"  {violates_bump} rules DO NOT match simple_bump form")
    if violates_bump > 0:
        print("  First few non-matching:")
        for k_in, k_out, dt, cnt in in1[:10]:
            if not (k_out == k_in + 3 and k_in % 6 == 2 and dt == 16 * ((k_in - 2) // 6) + 17):
                print(f"    {k_in} → {k_out}  dt={dt}  cnt={cnt}")

    # Analyze |in|=3 rules (carry_22_5 like)
    print("\n|in|=3 rules: input triples (first 30 distinct)")
    in3_types = Counter()
    for (i, o), dts in rules.items():
        if len(i) == 3:
            in3_types[(i, o)] += len(dts)
    # Show shape-patterns
    for (i, o), cnt in in3_types.most_common(30):
        print(f"  {list(i)} → {list(o)}   seen {cnt}x")
    return rules


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 500_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 120
    classify(max_steps=ms, time_budget=tb)
