#!/usr/bin/env python3
"""Regularity / Presburger investigation for the mod-3 invariant.

Mod-3-safe language L_safe ⊆ {0,1}* = {strings where every maximal 1-run
has length ≡ 2 (mod 3)}.  This IS a regular language (4-state DFA).

Key question: is reachable(TM) ⊆ L_safe?

We check L_safe membership at every TM step (not just E-turnarounds) and
classify each step as safe→safe, safe→unsafe, unsafe→safe, unsafe→unsafe.
This identifies which TM transitions preserve L_safe step-wise and which
temporarily violate it.
"""
import os, resource, sys, time
from collections import Counter, defaultdict

resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))
sys.path.insert(0, os.path.dirname(__file__))
from deep_sim import FastTape, STATE_NAMES


def is_mod3_safe(t):
    """Check: every maximal 1-run in tape is length ≡ 2 (mod 3).
    Walk from t.lo to t.hi, count runs."""
    run_len = 0
    for i in range(t.lo, t.hi + 1):
        if t.arr[i] == 1:
            run_len += 1
        else:
            if run_len > 0:
                if run_len % 3 != 2:
                    return False, run_len
                run_len = 0
    if run_len > 0:
        if run_len % 3 != 2:
            return False, run_len
    return True, None


def investigate(max_steps=10**6, time_budget=30):
    t = FastTape()
    # Transitions for classification
    transitions = Counter()  # (state, sym, dir, next_state) -> count
    safety_transitions = Counter()  # (transition, before_safe, after_safe) -> count
    bad_run_lengths = Counter()  # when unsafe, the violating length
    steps_unsafe = 0
    steps_safe = 0
    start = time.monotonic()

    while t.steps < max_steps:
        if t.halted: break
        before_safe, _ = is_mod3_safe(t)
        state_before = t.state
        sym_before = t.arr[t.hp]
        t.step_one()
        if t.halted: break
        after_safe, bad_len = is_mod3_safe(t)
        transition_key = (STATE_NAMES[state_before], sym_before,
                          'R' if t.hp > 0 else 'L',  # not quite right; just use transition label
                          STATE_NAMES[t.state])
        # simpler: record (pre-state, pre-sym) → (post-state)
        key = (STATE_NAMES[state_before], sym_before, STATE_NAMES[t.state])
        safety_transitions[(key, before_safe, after_safe)] += 1
        if before_safe:
            steps_safe += 1
        else:
            steps_unsafe += 1
        if not after_safe and bad_len is not None:
            bad_run_lengths[bad_len % 6] += 1  # mod 6 for finer analysis
        if time.monotonic() - start > time_budget:
            break

    elapsed = time.monotonic() - start
    print(f"Steps: {t.steps:,}  elapsed: {elapsed:.1f}s")
    print(f"Safe steps: {steps_safe:,}  Unsafe: {steps_unsafe:,}  "
          f"(safe frac: {100*steps_safe/(steps_safe+steps_unsafe):.1f}%)")
    print(f"Unsafe run-length (mod 6): {dict(bad_run_lengths.most_common())}")
    print()
    print("Transitions by (state, sym, next_state, safety_change):")
    transitions_by_key = defaultdict(Counter)
    for (key, before, after), cnt in safety_transitions.items():
        transitions_by_key[key][(before, after)] = cnt
    # Print each (key) with breakdown
    print("  Transition     |  safe→safe  |  safe→unsafe | unsafe→safe | unsafe→unsafe")
    print("  " + "-" * 85)
    for key in sorted(transitions_by_key.keys()):
        cnts = transitions_by_key[key]
        ss = cnts[(True, True)]
        su = cnts[(True, False)]
        us = cnts[(False, True)]
        uu = cnts[(False, False)]
        total = ss + su + us + uu
        print(f"  {key[0]},{key[1]}→{key[2]:<4}    |  {ss:>9,}  |  {su:>10,}  |  "
              f"{us:>9,}  |  {uu:>12,}")
    # Summary: which transitions are L_safe-preserving (no su and no transitions unsafe→unsafe after safe)?
    print()
    preserving = []
    breaking = []
    for key, cnts in transitions_by_key.items():
        if cnts[(True, False)] > 0:
            breaking.append((key, cnts[(True, False)]))
        else:
            if cnts[(True, True)] > 0:
                preserving.append(key)
    print(f"Transitions that NEVER break L_safe (safe→safe only): {len(preserving)}")
    for k in sorted(preserving):
        print(f"  {k[0]},{k[1]}→{k[2]}")
    print(f"\nTransitions that sometimes break L_safe (safe→unsafe count): {len(breaking)}")
    for k, c in sorted(breaking, key=lambda x: -x[1]):
        print(f"  {k[0]},{k[1]}→{k[2]}: {c:,} breakings")


if __name__ == "__main__":
    ms = int(sys.argv[1]) if len(sys.argv) > 1 else 5_000_000
    tb = int(sys.argv[2]) if len(sys.argv) > 2 else 30
    investigate(ms, tb)
