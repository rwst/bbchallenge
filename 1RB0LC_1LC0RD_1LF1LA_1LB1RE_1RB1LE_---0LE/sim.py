#!/usr/bin/env python3
"""Simulator for 1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE.

Transitions:
  A: 0->1RB, 1->0LC
  B: 0->1LC, 1->0RD
  C: 0->1LF, 1->1LA
  D: 0->1LB, 1->1RE
  E: 0->1RB, 1->1LE
  F: 0->HALT, 1->0LE
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE"

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
STATE_NAMES = "ABCDEF"
STA, STB, STC, STD, STE, STF = range(6)


class Tape:
    __slots__ = ("arr", "lo", "hi", "hp", "state", "steps", "halted")

    def __init__(self, cap=1 << 14):
        self.arr = bytearray(cap)
        mid = cap // 2
        self.lo = self.hi = self.hp = mid
        self.state = 0
        self.steps = 0
        self.halted = False

    def _ensure(self):
        n = len(self.arr)
        if self.hp <= 16:
            shift = n
            new = bytearray(n + shift)
            new[shift:shift + n] = self.arr
            self.arr = new
            self.lo += shift; self.hi += shift; self.hp += shift
        elif self.hp >= n - 16:
            self.arr.extend(b"\x00" * n)

    def step(self):
        sym = self.arr[self.hp]
        t = TR[(self.state, sym)]
        if t is None:
            self.halted = True
            return
        w, direction, ns = t
        self.arr[self.hp] = w
        if w and self.hp < self.lo: self.lo = self.hp
        if w and self.hp > self.hi: self.hi = self.hp
        if direction == 'R':
            self.hp += 1
        else:
            self.hp -= 1
        self.state = ns
        self.steps += 1
        self._ensure()

    def pretty(self, window=80):
        lo = max(self.lo - 1, self.hp - window)
        hi = min(self.hi + 1, self.hp + window)
        s = []
        for i in range(lo, hi + 1):
            c = str(self.arr[i])
            if i == self.hp:
                c = f"[{STATE_NAMES[self.state]}]{c}"
            s.append(c)
        return "".join(s)

    def tape_str(self):
        lo = min(self.lo, self.hp)
        hi = max(self.hi, self.hp)
        return "".join(str(self.arr[i]) for i in range(lo, hi + 1)), self.hp - lo

    def blocks_between(self, lo, hi):
        """Decompose self.arr[lo:hi+1] as runs of 1s separated by 0s.
        Returns list of (run_length) from left to right, dropping zero-runs."""
        runs = []
        i = lo
        while i <= hi:
            if self.arr[i] == 1:
                j = i
                while j <= hi and self.arr[j] == 1:
                    j += 1
                runs.append(j - i)
                i = j
            else:
                i += 1
        return runs


def run_from_blank(n):
    t = Tape()
    for _ in range(n):
        if t.halted:
            return t
        t.step()
    return t


def trace(n, filt=None):
    t = Tape()
    for _ in range(n):
        if t.halted:
            print(f"step {t.steps}: HALT"); return t
        if filt is None or filt(t):
            print(f"step {t.steps:6d}: {t.pretty(60)}")
        t.step()
    return t


def find_events(n, pred, max_events=200):
    """Return list of (steps, state, tape_str, head_rel_pos) where pred(t) is True."""
    t = Tape()
    out = []
    while t.steps < n and len(out) < max_events:
        if t.halted:
            out.append((t.steps, 'H', '', 0))
            break
        if pred(t):
            ts, hp = t.tape_str()
            out.append((t.steps, STATE_NAMES[t.state], ts, hp))
        t.step()
    return out


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "trace"
    if cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
        trace(n)
    elif cmd == "evt":
        st = sys.argv[2] if len(sys.argv) > 2 else "E"
        sym = int(sys.argv[3]) if len(sys.argv) > 3 else 0
        n = int(sys.argv[4]) if len(sys.argv) > 4 else 5000
        side = sys.argv[5] if len(sys.argv) > 5 else "R"  # L or R: head at left/right boundary
        idx = STATE_NAMES.index(st)
        if side == "R":
            pred = lambda t: t.state == idx and t.arr[t.hp] == sym and t.hp > t.hi
        elif side == "L":
            pred = lambda t: t.state == idx and t.arr[t.hp] == sym and t.hp < t.lo
        else:
            pred = lambda t: t.state == idx and t.arr[t.hp] == sym
        for ts, st_, tape, hp in find_events(n, pred):
            print(f"step {ts:7d} [{st_}] hp={hp:3d} tape={tape}")
    elif cmd == "blocks":
        # Track block sizes at right-blank events
        st_want = sys.argv[2] if len(sys.argv) > 2 else "E"
        n = int(sys.argv[3]) if len(sys.argv) > 3 else 50000
        max_ev = int(sys.argv[4]) if len(sys.argv) > 4 else 40
        idx = STATE_NAMES.index(st_want)
        t = Tape()
        prev = 0
        count = 0
        while t.steps < n and count < max_ev:
            if t.halted:
                print(f"HALT at step {t.steps}"); break
            # Right-blank event
            if t.state == idx and t.arr[t.hp] == 0 and t.hp > t.hi:
                blocks = t.blocks_between(min(t.lo, t.hp), max(t.hi, t.hp))
                dt = t.steps - prev
                print(f"step {t.steps:7d} dt={dt:6d} [{STATE_NAMES[t.state]}] blocks={blocks}")
                prev = t.steps
                count += 1
            t.step()
    elif cmd == "scan":
        # Scan state x (sym at head) x (at-right-blank? at-left-blank? interior?) frequency
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 50000
        from collections import Counter
        c = Counter()
        t = Tape()
        while t.steps < n:
            if t.halted: break
            boundary = "R" if t.hp > t.hi else ("L" if t.hp < t.lo else "I")
            c[(STATE_NAMES[t.state], t.arr[t.hp], boundary)] += 1
            t.step()
        for k, v in sorted(c.items(), key=lambda x: -x[1]):
            print(f"{k}: {v}")
