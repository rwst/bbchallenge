#!/usr/bin/env python3
"""Analyze restructure rules to find families & closed forms for dt.

Groups rules by (in_prefix, out_prefix) pattern where the rightmost block
is a variable k.  For each family, fits dt vs k to derive a formula.
"""

import os, resource, sys, time
from collections import Counter, defaultdict

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STE


def extract_blocks(t):
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


def run_sim(max_steps, time_budget):
    t = FastTape()
    rules = defaultdict(list)
    last_blocks, last_step = None, 0
    start = time.monotonic()
    while t.steps < max_steps:
        if t.halted:
            break
        if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
            blocks = extract_blocks(t)
            if blocks:
                if last_blocks is not None:
                    pre = common_prefix_len(last_blocks, blocks)
                    in_suf = tuple(last_blocks[pre:])
                    out_suf = tuple(blocks[pre:])
                    dt = t.steps - last_step
                    rules[(in_suf, out_suf)].append(dt)
                last_blocks = blocks
                last_step = t.steps
        if time.monotonic() - start > time_budget:
            break
        t.step_one()
    return rules, t.steps


def rule_family_key(in_suf, out_suf):
    """Replace the rightmost block (assumed large/variable) with a '*'
    and return a canonical pattern.  Also return the varied k."""
    if not in_suf or not out_suf:
        return None, None
    # Last block of in = k (variable); last of out = k + Δ (known delta).
    k = in_suf[-1]
    # Pattern: prefix_in (all but last) → prefix_out (all but last)
    #          with last_in=k, last_out = k + delta
    # We'll use prefix as the family, and record (k, delta, dt).
    prefix_in = in_suf[:-1]
    prefix_out = out_suf[:-1]
    k_out = out_suf[-1]
    delta = k_out - k
    return (prefix_in, prefix_out, delta), (k, delta)


def fit_linear(xs_ys):
    """Fit dt = a + b*k for (k, dt) pairs.  Returns (a, b, r²)."""
    if len(xs_ys) < 2:
        return None
    xs = [x for x, _ in xs_ys]
    ys = [y for _, y in xs_ys]
    n = len(xs)
    sx = sum(xs); sy = sum(ys)
    sxx = sum(x*x for x in xs); sxy = sum(x*y for x, y in zip(xs, ys))
    denom = n*sxx - sx*sx
    if denom == 0:
        return None
    b = (n*sxy - sx*sy) / denom
    a = (sy - b*sx) / n
    # R²
    mean_y = sy / n
    ss_tot = sum((y - mean_y)**2 for y in ys)
    ss_res = sum((y - (a + b*x))**2 for x, y in zip(xs, ys))
    r2 = 1 - ss_res/ss_tot if ss_tot > 0 else 1.0
    return a, b, r2


def analyze(rules):
    # Group by family
    families = defaultdict(list)  # (prefix_in, prefix_out, delta) -> [(k, dt), ...]
    for (i, o), dts in rules.items():
        fam, kd = rule_family_key(i, o)
        if fam is None:
            continue
        k, delta = kd
        for dt in dts:
            families[fam].append((k, dt))

    # Report families, sorted by count
    families_sorted = sorted(families.items(), key=lambda kv: -len(kv[1]))
    print(f"\n=== Families ({len(families)} total) ===\n")

    print("{:>28} {:>28} {:>6} {:>5} {:>8}".format(
        "prefix_in", "prefix_out", "Δk", "count", "formula"))
    print("-" * 95)
    for fam, kdts in families_sorted[:30]:
        prefix_in, prefix_out, delta = fam
        # Collapse duplicate k's
        unique_k = sorted(set(kdts), key=lambda kd: kd[0])
        count = len(kdts)
        fit = fit_linear(unique_k) if len(unique_k) >= 2 else None
        if fit and fit[2] > 0.999:
            a, b, r2 = fit
            # Prefer integer coefficients for nice forms
            a_i = round(a)
            b_i = round(b)
            if abs(a - a_i) < 0.01 and abs(b - b_i) < 0.01:
                formula = f"{b_i}k+{a_i}" if a_i >= 0 else f"{b_i}k{a_i}"
            else:
                formula = f"{b:.3f}k+{a:.1f}"
        else:
            if len(unique_k) == 1:
                formula = f"dt={unique_k[0][1]} (k={unique_k[0][0]})"
            else:
                formula = "(nonlinear)"
        print("{:>28} {:>28} {:>6} {:>5} {:>8}".format(
            str(list(prefix_in)), str(list(prefix_out)), delta, count, formula))

    # Focus on |prefix_in|=2 families (the simple 3-block restructures)
    print("\n=== |prefix_in|=2 families (input = [a, b, k]) ===")
    for fam, kdts in families_sorted:
        prefix_in, prefix_out, delta = fam
        if len(prefix_in) == 2:
            unique_k = sorted(set(kdts))
            count = len(kdts)
            fit = fit_linear(unique_k) if len(unique_k) >= 2 else None
            formula = "nonlinear"
            if fit and fit[2] > 0.999:
                a, b, r2 = fit
                a_i = round(a); b_i = round(b)
                if abs(a - a_i) < 0.01 and abs(b - b_i) < 0.01:
                    formula = f"dt = {b_i}k + {a_i}"
            k_range = (min(k for k, _ in unique_k), max(k for k, _ in unique_k))
            print(f"  [a={prefix_in[0]}, b={prefix_in[1]}, k] → "
                  f"{list(prefix_out) + ['k+' + str(delta)]}   "
                  f"count={count}  k∈[{k_range[0]},{k_range[1]}]  {formula}")

    # |prefix_in|=0 families (just rightmost changes)
    print("\n=== |prefix_in|=0 families (simple_bump type) ===")
    for fam, kdts in families_sorted:
        prefix_in, prefix_out, delta = fam
        if len(prefix_in) == 0 and len(prefix_out) == 0 and delta == 3:
            unique_k = sorted(set(kdts))
            count = len(kdts)
            fit = fit_linear(unique_k) if len(unique_k) >= 2 else None
            formula = "?"
            if fit and fit[2] > 0.999:
                a, b, r2 = fit
                a_i = round(a); b_i = round(b)
                if abs(a - a_i) < 0.01 and abs(b - b_i) < 0.01:
                    formula = f"dt = {b_i}k + {a_i}"
                    # simple_bump predicts dt = (8(k-2))/3 + 17 = 8k/3 + 35/3. For k=6j+2.
                    # In terms of j: dt = 16j+17, k = 6j+2, so dt = (16/6)*(k-2)+17 = (8/3)*k - (16/3)+17 = (8k+35)/3.
                    # So dt = 8k/3 + 35/3. With b=8/3≈2.667 and a=35/3≈11.67.
                    # Integer formula: 3·dt = 8k+35.
            print(f"  [k] → [k+3]   count={count}  k_range=[{min(unique_k)[0]},{max(unique_k)[0]}]  {formula}")
            break  # just one such family


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 500_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 180
    print(f"Running sim for max_steps={ms:,} time={tb}s")
    rules, final_step = run_sim(ms, tb)
    print(f"Completed at step {final_step:,}")
    analyze(rules)
