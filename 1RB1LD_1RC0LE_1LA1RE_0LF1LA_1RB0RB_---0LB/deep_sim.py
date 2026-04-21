#!/usr/bin/env python3
"""Deep simulator for 1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB.

Checks invariant: at every E-turnaround (state E, head on 0 past rightmost 1),
are all block sizes ≡ 2 (mod 3)?

Memory-capped to 2 GB.  Reports stats: #events, max block, min block,
block-mod-3 distribution, any violations.

Also monitors peak memory usage every N steps.
"""

import os
import resource
import sys
import time

# Hard cap 2 GB virtual memory.
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB"


def parse_tm(s):
    trs = {}
    for i, row in enumerate(s.split("_")):
        for j, trans in enumerate([row[:3], row[3:]]):
            if trans == "---":
                trs[(i, j)] = None
            else:
                w, d, ns = int(trans[0]), trans[1], ord(trans[2]) - ord('A')
                trs[(i, j)] = (w, d, ns)
    return trs


TR = parse_tm(TM_STR)
# Flatten transitions into arrays indexed by state*2 + sym for speed.
WRITE = [0] * 12
DIR = [0] * 12  # 1 = R, -1 = L
NEXT = [0] * 12  # next state, -1 for halt
for (s, sym), t in TR.items():
    i = s * 2 + sym
    if t is None:
        NEXT[i] = -1
    else:
        w, d, ns = t
        WRITE[i] = w
        DIR[i] = 1 if d == 'R' else -1
        NEXT[i] = ns

STATE_NAMES = "ABCDEF"
STE = 4


class FastTape:
    """Offset-indexed tape.  Block-based, doubles on boundary overflow."""
    __slots__ = ("arr", "lo", "hi", "hp", "state", "steps", "halted")

    def __init__(self, cap=1 << 16):
        self.arr = bytearray(cap)
        mid = cap // 2
        self.lo = self.hi = self.hp = mid
        self.state = 0
        self.steps = 0
        self.halted = False

    def _grow(self):
        n = len(self.arr)
        # Only grow if approaching edge; keep total RAM << 2 GB.
        if self.hp < 32:
            shift = n
            new = bytearray(n + shift)
            new[shift:shift + n] = self.arr
            self.arr = new
            self.lo += shift
            self.hi += shift
            self.hp += shift
        elif self.hp >= n - 32:
            self.arr.extend(b"\x00" * n)

    def run_steps(self, n):
        """Run up to n steps.  Returns True if halted."""
        arr = self.arr
        hp = self.hp
        state = self.state
        lo = self.lo
        hi = self.hi
        W = WRITE
        D = DIR
        N = NEXT
        for _ in range(n):
            idx = state * 2 + arr[hp]
            ns = N[idx]
            if ns == -1:
                self.halted = True
                self.hp = hp
                self.state = state
                self.lo = lo
                self.hi = hi
                self.steps += _
                return True
            w = W[idx]
            arr[hp] = w
            if w:
                if hp < lo:
                    lo = hp
                if hp > hi:
                    hi = hp
            hp += D[idx]
            state = ns
            if hp < 32 or hp >= len(arr) - 32:
                # Need to grow; sync state and resize.
                self.hp = hp
                self.state = state
                self.lo = lo
                self.hi = hi
                self.steps += _ + 1
                self._grow()
                arr = self.arr
                hp = self.hp
                lo = self.lo
                hi = self.hi
                # Continue from this point (already counted this step).
                continue
        self.hp = hp
        self.state = state
        self.lo = lo
        self.hi = hi
        self.steps += n
        return False

    def step_one(self):
        """Single step (used between run_steps chunks)."""
        arr = self.arr
        idx = self.state * 2 + arr[self.hp]
        ns = NEXT[idx]
        if ns == -1:
            self.halted = True
            return
        w = WRITE[idx]
        arr[self.hp] = w
        if w:
            if self.hp < self.lo:
                self.lo = self.hp
            if self.hp > self.hi:
                self.hi = self.hp
        self.hp += DIR[idx]
        self.state = ns
        self.steps += 1
        if self.hp < 32 or self.hp >= len(arr) - 32:
            self._grow()

    def extract_blocks_at_E_turnaround(self):
        """If state E and head past rightmost 1 on 0, return block sizes L-to-R.
        Otherwise return None."""
        if self.state != STE:
            return None
        if self.arr[self.hp] != 0:
            return None
        if self.hp <= self.hi:
            return None
        blocks = []
        cur = 0
        for i in range(self.lo, self.hp):
            if self.arr[i] == 1:
                cur += 1
            else:
                if cur > 0:
                    blocks.append(cur)
                    cur = 0
        if cur > 0:
            blocks.append(cur)
        return blocks


def get_rss_mb():
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024


def check_invariant_deep(max_steps=10**9, report_every_n_events=1000,
                          max_events=None, stop_on_violation=True,
                          time_budget_sec=None):
    """Run raw TM, check invariant at every E-turnaround.

    Uses step_one loop; can be slow but memory-safe.
    """
    t = FastTape()
    events = 0
    violations = []
    max_block = 0
    min_block = float('inf')
    mod3_counts = [0, 0, 0]  # counts by sᵢ mod 3
    start_time = time.monotonic()
    last_report = start_time

    # We need to check E-turnaround after every step; a fast check is:
    # state == STE, arr[hp] == 0, hp > hi.  Do this inline.
    arr = t.arr
    while t.steps < max_steps:
        if t.halted:
            print(f"HALT at step {t.steps}")
            break
        # Fast inline check
        if t.state == STE and arr[t.hp] == 0 and t.hp > t.hi:
            blocks = t.extract_blocks_at_E_turnaround()
            if blocks:
                events += 1
                for s in blocks:
                    r = s % 3
                    mod3_counts[r] += 1
                    if r != 2:
                        violations.append((t.steps, blocks, s))
                        if stop_on_violation:
                            print(f"!! VIOLATION at step {t.steps}: block size {s} ≡ {r} (mod 3)")
                            print(f"   Blocks: {blocks}")
                            return events, violations, max_block, min_block, mod3_counts
                    if s > max_block:
                        max_block = s
                    if s < min_block:
                        min_block = s
                if events % report_every_n_events == 0:
                    now = time.monotonic()
                    rate = t.steps / (now - start_time) if now > start_time else 0
                    print(f"  event #{events:8d} step={t.steps:12d} "
                          f"blocks(n={len(blocks):3d}, max={max(blocks):5d}, "
                          f"min={min(blocks):3d}) RSS={get_rss_mb():.0f}MB "
                          f"rate={rate:.0f}steps/s")
                    last_report = now
                if max_events and events >= max_events:
                    break
        if time_budget_sec and (time.monotonic() - start_time) > time_budget_sec:
            print(f"  (time budget exhausted at {time_budget_sec}s)")
            break
        t.step_one()
        arr = t.arr  # re-read after potential grow
    elapsed = time.monotonic() - start_time
    print(f"\n=== Summary ===")
    print(f"Final step: {t.steps:,}  elapsed: {elapsed:.1f}s")
    print(f"Events: {events:,}")
    print(f"Block size mod 3 distribution: 0→{mod3_counts[0]}  "
          f"1→{mod3_counts[1]}  2→{mod3_counts[2]}")
    print(f"Max block size: {max_block}   Min block size: {min_block}")
    print(f"Violations: {len(violations)}")
    print(f"Peak RSS: {get_rss_mb():.0f} MB")
    return events, violations, max_block, min_block, mod3_counts


if __name__ == "__main__":
    max_steps = int(sys.argv[1]) if len(sys.argv) > 1 else 10**7
    time_budget = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    print(f"Running with max_steps={max_steps:,}, time budget {time_budget}s")
    check_invariant_deep(max_steps=max_steps, time_budget_sec=time_budget,
                          report_every_n_events=500)
