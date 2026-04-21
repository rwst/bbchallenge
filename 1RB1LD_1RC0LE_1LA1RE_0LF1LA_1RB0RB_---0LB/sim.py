#!/usr/bin/env python3
"""Simulator for 1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB.

Transitions:
  A: 0->1RB, 1->1LD
  B: 0->1RC, 1->0LE
  C: 0->1LA, 1->1RE
  D: 0->0LF, 1->1LA
  E: 0->1RB, 1->0RB
  F: 0->HALT, 1->0LB

Racheline hint: "shift-overflow counter, chaotic. 0=E, 1=A, 2=D on a
given bit." The Python recurrence in previous-work/racheline.txt tracks
the state-sequence hitting each bit of a right-growing tape region.
"""

import resource, sys
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
        """Tape as string of 0/1, head position marked separately."""
        lo = min(self.lo, self.hp)
        hi = max(self.hi, self.hp)
        return "".join(str(self.arr[i]) for i in range(lo, hi + 1)), self.hp - lo


def run_from_blank(n):
    t = Tape()
    for _ in range(n):
        if t.halted:
            return t
        t.step()
    return t


def trace(n, filt=None):
    """Print config every step matching `filt(t) -> bool` (or every step)."""
    t = Tape()
    for _ in range(n):
        if t.halted:
            print(f"step {t.steps}: HALT"); return t
        if filt is None or filt(t):
            print(f"step {t.steps:6d}: {t.pretty(40)}")
        t.step()
    return t


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "trace"
    if cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 200
        trace(n)
    elif cmd == "evt":
        # event-based: print at specific state
        st = sys.argv[2] if len(sys.argv) > 2 else "A"
        n = int(sys.argv[3]) if len(sys.argv) > 3 else 5000
        idx = STATE_NAMES.index(st)
        trace(n, lambda t: t.state == idx and t.arr[t.hp] == 0 and t.hp > t.hi)
