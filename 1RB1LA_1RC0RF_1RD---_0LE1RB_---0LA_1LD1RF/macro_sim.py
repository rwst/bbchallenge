#!/usr/bin/env python3
"""F1+F2: Macro-step simulator with axiom logging.

Mirrors the macroStep dispatch from machine.lean using RLE-encoded macro
configurations (Macro = 'M' or 'M0' with run lists L, R and cursor c). Every
proven compound rule from machine.lean is dispatched directly. When one of the
3 reachability axiom shapes (R1, R2, R3) is encountered, the simulator:

  1. Renders the macro config to a raw TM tape
  2. Runs raw TM steps until a fresh valid macro config is detected (the
     "bridge")
  3. Logs the input shape, parameters, raw bridge step count, output config
  4. Returns to macro-level simulation

This generates the data for closed-form chain analysis (LOG.md path A).

Usage:
    python3 macro_sim.py -n 100000              # 100K macro steps
    python3 macro_sim.py -n 10000000 -l ax.json # log axioms to JSON Lines
"""

import argparse
import json
import sys
from collections import defaultdict, Counter
from dataclasses import dataclass


# Raw TM transition table (state, sym) -> (write, move, new_state)
# State encoding: A=0, B=1, C=2, D=3, E=4, F=5
RULES = {
    (0, 0): (1, +1, 1),  # A,0 -> 1RB
    (0, 1): (1, -1, 0),  # A,1 -> 1LA
    (1, 0): (1, +1, 2),  # B,0 -> 1RC
    (1, 1): (0, +1, 5),  # B,1 -> 0RF
    (2, 0): (1, +1, 3),  # C,0 -> 1RD
    # (2, 1): undefined  # C,1 -> halt
    (3, 0): (0, -1, 4),  # D,0 -> 0LE
    (3, 1): (1, +1, 1),  # D,1 -> 1RB
    # (4, 0): undefined  # E,0 -> halt
    (4, 1): (0, -1, 0),  # E,1 -> 0LA
    (5, 0): (1, -1, 3),  # F,0 -> 1LD
    (5, 1): (1, +1, 5),  # F,1 -> 1RF
}
STATE_NAME = {0: 'A', 1: 'B', 2: 'C', 3: 'D', 4: 'E', 5: 'F'}


@dataclass
class Macro:
    """Macro configuration. kind='M': cursor c at rightmost 1 of cursor run,
    head=1. kind='M0': cursor at 0 between L and 00 gap, head=0."""
    kind: str
    L: list
    c: int
    R: list

    def __repr__(self):
        if self.kind == 'M':
            return f"M({self.L},{self.c},{self.R})"
        return f"M0({self.L},{self.R})"

    def copy(self):
        return Macro(self.kind, list(self.L), self.c, list(self.R))


# ============================================================
# Macro <-> raw tape conversion
# ============================================================

def macro_to_tape(m):
    """Build (tape: dict, head: int, state: int, ones_set: set) from a Macro."""
    tape = {}
    ones = set()
    head = 0

    def w1(p):
        tape[p] = 1
        ones.add(p)

    if m.kind == 'M':
        w1(head)
        for i in range(1, m.c):
            w1(head - i)
        # head - m.c is separator (0 by default)
        pos = head - m.c - 1
        for j, run_len in enumerate(m.L):
            for _ in range(run_len):
                w1(pos)
                pos -= 1
            if j < len(m.L) - 1:
                pos -= 1  # separator
        # right: head+1, head+2 default 0; runs(R) starts at head+3
        pos = head + 3
        for j, run_len in enumerate(m.R):
            for _ in range(run_len):
                w1(pos)
                pos += 1
            if j < len(m.R) - 1:
                pos += 1
    else:  # M0
        # head reads 0 (already 0 by default)
        pos = head - 1
        for j, run_len in enumerate(m.L):
            for _ in range(run_len):
                w1(pos)
                pos -= 1
            if j < len(m.L) - 1:
                pos -= 1
        pos = head + 3
        for j, run_len in enumerate(m.R):
            for _ in range(run_len):
                w1(pos)
                pos += 1
            if j < len(m.R) - 1:
                pos += 1
    return tape, head, 0, ones


def tape_to_macro(tape, head, state, ones, leftmost, rightmost):
    """Detect a clean macro config at (tape, head, state). Returns Macro or None.

    A clean macro config requires state A and the boundary structure
    head+1 = head+2 = 0. M_Config additionally requires head = 1 and parses the
    cursor's left-ones; M0_Config requires head = 0 and head-1 = 1 (L nonempty
    per invariant)."""
    if state != 0:
        return None
    if not ones:
        return None
    sym = tape.get(head, 0)
    if tape.get(head + 1, 0) != 0 or tape.get(head + 2, 0) != 0:
        return None

    if sym == 1:
        # Count cursor leftward
        c = 1
        p = head - 1
        while tape.get(p, 0) == 1:
            c += 1
            p -= 1
        # tape[p] == 0; L starts (if at all) at p-1
        L = []
        if p - 1 >= leftmost:
            pos = p - 1
            while True:
                if tape.get(pos, 0) != 1:
                    return None
                run_len = 0
                while pos >= leftmost and tape.get(pos, 0) == 1:
                    run_len += 1
                    pos -= 1
                L.append(run_len)
                if pos < leftmost:
                    break
                # pos is at a 0; another run further left iff leftmost < pos
                if leftmost >= pos:
                    break
                pos -= 1  # skip separator
        R = []
        if head + 3 <= rightmost:
            pos = head + 3
            while True:
                if tape.get(pos, 0) != 1:
                    return None
                run_len = 0
                while pos <= rightmost and tape.get(pos, 0) == 1:
                    run_len += 1
                    pos += 1
                R.append(run_len)
                if pos > rightmost:
                    break
                if rightmost <= pos:
                    break
                pos += 1  # skip separator
        return Macro('M', L, c, R)
    else:  # sym == 0
        if tape.get(head - 1, 0) != 1:
            return None  # M0 invariant L ≠ []
        L = []
        pos = head - 1
        while True:
            if tape.get(pos, 0) != 1:
                return None
            run_len = 0
            while pos >= leftmost and tape.get(pos, 0) == 1:
                run_len += 1
                pos -= 1
            L.append(run_len)
            if pos < leftmost:
                break
            if leftmost >= pos:
                break
            pos -= 1
        R = []
        if head + 3 <= rightmost:
            pos = head + 3
            while True:
                if tape.get(pos, 0) != 1:
                    return None
                run_len = 0
                while pos <= rightmost and tape.get(pos, 0) == 1:
                    run_len += 1
                    pos += 1
                R.append(run_len)
                if pos > rightmost:
                    break
                if rightmost <= pos:
                    break
                pos += 1
        return Macro('M0', L, 0, R)


def check_invariant(m):
    """MacroInvariant: AllGe1 L, c ≥ 2 (M only), AllGe1 R, R ≠ [] (M),
    L ≠ [] and R ≠ [] (M0), NoHaltPattern R (M0)."""
    if m.kind == 'M':
        if not m.R:
            return False
        if m.c < 2:
            return False
        if not all(x >= 1 for x in m.L):
            return False
        if not all(x >= 1 for x in m.R):
            return False
        return True
    else:
        if not m.L or not m.R:
            return False
        if not all(x >= 1 for x in m.L):
            return False
        if not all(x >= 1 for x in m.R):
            return False
        # NoHaltPattern: R ≠ 1 :: (z+1) :: R'
        if len(m.R) >= 2 and m.R[0] == 1 and m.R[1] >= 1:
            return False
        return True


# ============================================================
# Axiom classification
# ============================================================

def classify_axiom(m):
    """Return ('R1'|'R2'|'R3', params) if m matches an axiom shape, else None."""
    if m.kind == 'M':
        if not m.L and m.c == 3 and m.R:
            return 'R1', {
                'd': m.R[0],
                'R': list(m.R),
                'R_len': len(m.R),
                'R_sum': sum(m.R),
            }
    else:
        if m.L and m.R and m.R[0] >= 3 and m.R[-1] == 2:
            if len(m.R) == 3 and m.R[1] == 1:
                return 'R2', {
                    'r': m.R[0] - 3,  # so R[0] = r+3
                    'a': m.L[0],
                    'L': list(m.L),
                    'L_len': len(m.L),
                    'L_sum': sum(m.L),
                }
            if len(m.R) >= 4:
                return 'R3', {
                    'r': m.R[0] - 3,
                    'middle': list(m.R[1:-1]),
                    'a': m.L[0],
                    'L': list(m.L),
                    'L_len': len(m.L),
                    'L_sum': sum(m.L),
                    'middle_len': len(m.R) - 2,
                    'middle_sum': sum(m.R[1:-1]),
                }
    return None


# ============================================================
# Macro-step dispatch (mirrors machine.lean macroStep + compound rules)
# ============================================================

# Sentinels for non-macro outcomes
AXIOM_R1 = '__AXIOM_R1__'
AXIOM_R2 = '__AXIOM_R2__'
AXIOM_R3 = '__AXIOM_R3__'
HALT = '__HALT__'


def macro_step(m):
    """Apply one macro transition. Returns (result, steps, rule_name).

    result is either:
      - a Macro (normal transition)
      - AXIOM_R1 / AXIOM_R2 / AXIOM_R3 (axiom shape; caller must bridge)
      - HALT (halt pattern detected)
      - None (invariant violation / unhandled)"""
    if m.kind == 'M':
        L, c, R = m.L, m.c, m.R
        if not R:
            return None, 0, 'M_R_empty'
        if c == 1:
            if not L:
                return None, 0, 'M_c1_no_L'
            return Macro('M', L[1:], L[0], [1] + R), 6, 'shift'
        if c == 0:
            return None, 0, 'M_c0'
        if c == 2:
            if not L:
                return Macro('M0', [1], 0, [R[0] + 1] + R[1:]), 11, 'sweep_to_zero_left_empty'
            return Macro('M0', [L[0] + 1] + L[1:], 0, [R[0] + 1] + R[1:]), 11, 'sweep_to_zero'
        if c == 3:
            if not L:
                return AXIOM_R1, 0, 'AXIOM_R1'
            # sweep_and_shift compound: 19 steps
            return Macro('M', L[1:], L[0] + 1, [1, R[0] + 1] + R[1:]), 19, 'sweep_and_shift'
        # c >= 4
        steps = 2 * c + 7
        if not L:
            return Macro('M', [1], c - 2, [R[0] + 1] + R[1:]), steps, 'sweep_left_empty'
        return Macro('M', [L[0] + 1] + L[1:], c - 2, [R[0] + 1] + R[1:]), steps, 'sweep'
    # M0
    L, R = m.L, m.R
    if not L:
        return None, 0, 'M0_L_empty'
    if not R:
        return None, 0, 'M0_R_empty'
    a = L[0]
    L_rest = L[1:]
    # Halt pattern
    if len(R) >= 2 and R[0] == 1 and R[1] >= 1:
        return HALT, 6, 'halt'
    if len(R) == 1:
        r = R[0]
        if r == 1:
            a_orig = L[0] - 1
            if len(L) >= 2:
                return Macro('M', [L[1] + 1] + L[2:], a_orig + 4, [1]), 2 * a_orig + 27, 'era_and_sweep'
            return Macro('M', [1], a_orig + 4, [1]), 2 * a_orig + 27, 'era_and_sweep_solo'
        if r == 2:
            return Macro('M', L_rest, a + 3, [1]), 8, 'zero_two_solo'
        if r == 3:
            return Macro('M0', [a + 4] + L_rest, 0, [1]), 12, 'zero_bounce_to_zero'
        if r == 4:
            return Macro('M', L_rest, a + 4, [1, 1]), 19, 'zero_bounce_and_shift'
        z = r - 5
        return Macro('M', [a + 4] + L_rest, z + 2, [1]), z + 14, 'zero_bounce'
    # Multi-element R
    if R[0] == 0:
        return None, 0, 'M0_R_starts_0'
    if R[0] == 1:
        # halt pattern caught above; this means R[1] == 0, invariant violation
        return None, 0, 'M0_R_starts_1_invalid'
    if R[0] == 2:
        return Macro('M', L_rest, a + 3, [R[1] + 1] + R[2:]), 8, 'zero_two'
    # R[0] >= 3
    last = R[-1]
    R_mid = R[1:-1]
    n = len(R_mid)
    if last == 2:
        if len(R) == 2:
            if R[0] == 3:
                # macro_multi_bounce_2_double_shift: 22 steps, M(L', a+4, [1,1,1])
                return Macro('M', L_rest, a + 4, [1, 1, 1]), 22, 'multi_bounce_2_double_shift'
            r2 = R[0] - 4  # so R[0] = r2+4, r2 >= 0
            return Macro('M', [a + 4] + L_rest, r2 + 2, [1, 1]), r2 + 24, 'multi_bounce_2_and_shift'
        if len(R) == 3:
            e = R[1]
            if e == 1:
                return AXIOM_R2, 0, 'AXIOM_R2'
            # e >= 2: macro_multi_bounce_3run_last_2
            # Output: M((r'+1) :: (a+4) :: L, e, [1,1])
            r_prime = R[0] - 3
            steps = r_prime + 3 + e + 17 + 6  # = r'+e+26
            return Macro('M', [r_prime + 1, a + 4] + L_rest, e, [1, 1]), steps, 'multi_bounce_3run_last_2'
        # 4+ runs ending in 2: AXIOM R3
        return AXIOM_R3, 0, 'AXIOM_R3'
    if last == 1:
        r = R[0] - 3
        steps = r + 3 * n + sum(R_mid) + 16
        new_L = list(reversed(R_mid)) + [r + 1, a + 4] + L_rest
        return Macro('M0', new_L, 0, [1]), steps, 'multi_bounce_general_to_zero'
    if last >= 3:
        r = R[0] - 3
        z = last - 2
        steps = r + z + 3 * n + sum(R_mid) + 17
        new_L = list(reversed(R_mid)) + [r + 1, a + 4] + L_rest
        return Macro('M', new_L, z + 1, [1]), steps, 'multi_bounce_general'
    return None, 0, 'M0_unhandled'


# ============================================================
# Bridge: raw TM simulation through axiom shapes
# ============================================================

def bridge_axiom(m, max_steps=10**6):
    """Bridge an axiom shape via raw TM steps. Returns (new_macro, steps, halted)."""
    tape, head, state, ones = macro_to_tape(m)
    if not ones:
        return None, 0, False
    leftmost = min(ones)
    rightmost = max(ones)

    for i in range(1, max_steps + 1):
        sym = tape.get(head, 0)
        key = (state, sym)
        if key not in RULES:
            return None, i, True  # halted
        write, move, new_state = RULES[key]
        if write != sym:
            tape[head] = write
            if write == 1:
                ones.add(head)
                if head < leftmost:
                    leftmost = head
                if head > rightmost:
                    rightmost = head
            else:
                ones.discard(head)
                if head == leftmost or head == rightmost:
                    if ones:
                        leftmost = min(ones)
                        rightmost = max(ones)
                    else:
                        return None, i, False  # tape empty, weird
        head += move
        state = new_state

        # Try macro detection (cheap early-exit on state ≠ A)
        if state != 0:
            continue
        m_new = tape_to_macro(tape, head, state, ones, leftmost, rightmost)
        if m_new is None:
            continue
        if not check_invariant(m_new):
            continue
        # Skip if same as input (shouldn't happen, but defensive)
        if (m_new.kind == m.kind and m_new.L == m.L
                and m_new.c == m.c and m_new.R == m.R):
            continue
        return m_new, i, False
    return None, max_steps, False


# ============================================================
# Main simulator loop
# ============================================================

# After 43 raw steps from blank tape, we reach M_Config([1], 4, [1])
INIT_MACRO = Macro('M', [1], 4, [1])
INIT_RAW = 43


def _era_record(era, macro_count, raw_steps, m):
    return {
        'era': era,
        'macro_step': macro_count,
        'raw_step': raw_steps,
        'kind': m.kind,
        'c': m.c,
        'L': list(m.L),
        'R': list(m.R),
        'L_len': len(m.L),
        'L_sum': sum(m.L),
        'R_len': len(m.R),
        'R_sum': sum(m.R),
        'L_head': m.L[0] if m.L else 0,
        'L_last': m.L[-1] if m.L else 0,
        'R_head': m.R[0] if m.R else 0,
        'R_last': m.R[-1] if m.R else 0,
    }


def run(max_macro_steps, log_path=None, verbose_period=None,
        era_log_path=None, max_eras=None):
    m = INIT_MACRO.copy()
    raw_steps = INIT_RAW
    macro_count = 0
    rule_counts = Counter()
    axioms = []
    prev_rule = 'init'
    era = 0  # era 0 starts at INIT_MACRO

    log_fp = open(log_path, 'w') if log_path else None
    era_fp = open(era_log_path, 'w') if era_log_path else None
    if era_fp:
        json.dump(_era_record(0, 0, raw_steps, m), era_fp)
        era_fp.write('\n')
    halted = False
    stuck_reason = None

    while macro_count < max_macro_steps:
        macro_count += 1

        if verbose_period and macro_count % verbose_period == 0:
            sys.stderr.write(f"  [m={macro_count} raw~{raw_steps}] {m}\n")

        result, steps, rule = macro_step(m)

        if result is None:
            stuck_reason = rule
            sys.stderr.write(f"STUCK at macro={macro_count} raw~{raw_steps}: {m} ({rule})\n")
            break
        if result == HALT:
            halted = True
            sys.stderr.write(f"HALT at macro={macro_count} raw~{raw_steps}: {m}\n")
            break

        if result in (AXIOM_R1, AXIOM_R2, AXIOM_R3):
            ax_class, params = classify_axiom(m)
            assert ax_class is not None, f"axiom flag {result} but classify_axiom returned None: {m}"

            m_new, bridge_k, did_halt = bridge_axiom(m)
            entry = {
                'macro_step': macro_count,
                'raw_step': raw_steps,
                'axiom': ax_class,
                'producer': prev_rule,
                'config_in': str(m),
                'params': params,
                'bridge_steps': bridge_k,
                'config_out': str(m_new) if m_new else None,
                'out_kind': m_new.kind if m_new else None,
                'out_c': m_new.c if m_new else None,
                'out_L_len': len(m_new.L) if m_new else None,
                'out_R_len': len(m_new.R) if m_new else None,
                'halted': did_halt,
            }
            axioms.append(entry)
            if log_fp:
                json.dump(entry, log_fp)
                log_fp.write('\n')
                log_fp.flush()

            rule_counts[f'AXIOM_{ax_class}'] += 1
            if did_halt:
                halted = True
                sys.stderr.write(f"HALT during bridge of {ax_class} at raw~{raw_steps}\n")
                break
            if m_new is None:
                stuck_reason = f"bridge_failed_{ax_class}"
                sys.stderr.write(f"BRIDGE FAILED for {ax_class} at raw~{raw_steps}\n")
                break

            raw_steps += bridge_k
            prev_rule = f'AXIOM_{ax_class}'
            m = m_new
            continue

        # Normal transition
        rule_counts[rule] += 1
        prev_rule = rule
        raw_steps += steps
        m = result

        if rule == 'era_and_sweep' or rule == 'era_and_sweep_solo':
            era += 1
            if era_fp:
                json.dump(_era_record(era, macro_count, raw_steps, m), era_fp)
                era_fp.write('\n')
            if max_eras is not None and era >= max_eras:
                break

    if log_fp:
        log_fp.close()
    if era_fp:
        era_fp.close()

    return {
        'halted': halted,
        'stuck': stuck_reason,
        'macro_count': macro_count,
        'raw_steps': raw_steps,
        'era': era,
        'final_config': str(m),
        'rule_counts': dict(rule_counts),
        'axioms': axioms,
    }


def summarize(result, top_n=10):
    print(f"=== Run summary ===")
    print(f"Halted: {result['halted']}")
    if result['stuck']:
        print(f"Stuck: {result['stuck']}")
    print(f"Macro steps: {result['macro_count']:,}")
    print(f"Raw steps: ~{result['raw_steps']:,}")
    print(f"Era count: {result.get('era', 0):,}")
    print(f"Final config: {result['final_config']}")
    print(f"Axiom occurrences total: {len(result['axioms'])}")

    print(f"\n=== Rule counts (top {top_n}) ===")
    for rule, n in sorted(result['rule_counts'].items(), key=lambda x: -x[1])[:top_n]:
        print(f"  {rule:40s} {n:>10,}")

    # Per-axiom breakdown
    by_ax = defaultdict(list)
    for e in result['axioms']:
        by_ax[e['axiom']].append(e)

    for ax in ['R1', 'R2', 'R3']:
        entries = by_ax.get(ax, [])
        print(f"\n=== Axiom {ax}: {len(entries)} occurrences ===")
        if not entries:
            continue
        print(f"  First: macro={entries[0]['macro_step']} raw~{entries[0]['raw_step']}")
        print(f"    in : {entries[0]['config_in']}")
        print(f"    out: {entries[0]['config_out']}  (bridge={entries[0]['bridge_steps']} raw)")
        print(f"  Last : macro={entries[-1]['macro_step']} raw~{entries[-1]['raw_step']}")
        print(f"    in : {entries[-1]['config_in']}")
        print(f"    out: {entries[-1]['config_out']}  (bridge={entries[-1]['bridge_steps']} raw)")
        bridges = [e['bridge_steps'] for e in entries]
        if bridges:
            print(f"  Bridge steps: min={min(bridges)} max={max(bridges)} "
                  f"mean={sum(bridges) / len(bridges):.1f}")
        # Producer distribution
        producers = Counter(e['producer'] for e in entries)
        print(f"  Producers: {dict(producers.most_common(5))}")
        # Output kind distribution
        out_kinds = Counter(e['out_kind'] for e in entries)
        print(f"  Out kinds: {dict(out_kinds)}")


def main():
    p = argparse.ArgumentParser(description='Macro-step simulator + axiom logger')
    p.add_argument('-n', '--macro-steps', type=int, default=100000,
                   help='Max macro steps (default 100K)')
    p.add_argument('-l', '--log', default=None,
                   help='JSON Lines log file for axiom occurrences')
    p.add_argument('-e', '--era-log', default=None,
                   help='JSON Lines log file for era-boundary states')
    p.add_argument('-E', '--max-eras', type=int, default=None,
                   help='Stop after this many era boundaries')
    p.add_argument('-v', '--verbose', type=int, default=None,
                   help='Print progress every N macro steps')
    args = p.parse_args()

    result = run(args.macro_steps, log_path=args.log,
                 era_log_path=args.era_log, max_eras=args.max_eras,
                 verbose_period=args.verbose)
    summarize(result)


if __name__ == '__main__':
    main()
