#!/usr/bin/env python3
"""Simulator for BMO1: 1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE.

Verifies macro rules:
  A(a,b) -> A(a-b, 4b+2)     if a > b
  A(a,b) -> A(2a+1, b-a)     if a < b
  A(a,b) -> Halt             if a = b
Start A(1, 2).

A(a,b) corresponds to E(a-1, 0, b) (Shawn's notation):
  0^inf 1 0^(a-1) 0 1 1^b E> 0^inf.
"""

import resource
# Hard cap 2 GB virtual memory.
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE"

def parse_tm(s):
    trs = {}
    rows = s.split("_")
    for i, row in enumerate(rows):
        for j, trans in enumerate([row[:3], row[3:]]):
            if trans == "---":
                trs[(i, j)] = None
            else:
                w = int(trans[0])
                d = trans[1]
                ns = ord(trans[2]) - ord('A')
                trs[(i, j)] = (w, d, ns)
    return trs

TR = parse_tm(TM_STR)
STATE_NAMES = "ABCDEF"
STE = 4  # state E index

# Tape representation: two Python bytearrays "left" (indexed 0 = cell at pos-1,
# growing rightward as head moves left) and "right" (indexed 0 = cell at pos,
# growing rightward as head moves right). Head symbol stored in right[0].
# min_left = leftmost nonzero index into left bytearray; similarly max_right.


class Tape:
    __slots__ = ("left", "right", "state", "steps", "halted",
                 "left_len", "right_len")

    def __init__(self, cap=1024):
        self.left = bytearray(cap)
        self.right = bytearray(cap)
        self.left_len = 0     # number of used cells on the left (logical length)
        self.right_len = 1    # head at right[0]
        self.state = 0
        self.steps = 0
        self.halted = False

    def _grow_right(self):
        self.right.extend(b"\x00" * len(self.right))

    def _grow_left(self):
        self.left.extend(b"\x00" * len(self.left))

    def step(self):
        sym = self.right[0]
        t = TR[(self.state, sym)]
        if t is None:
            self.halted = True
            return
        w, direction, ns = t
        self.right[0] = w
        if direction == 'R':
            # Head moves right. left grows by one (receives the cell we wrote).
            new_cell = self.right[0]
            # push new_cell onto left
            if self.left_len == len(self.left):
                self._grow_left()
            self.left[self.left_len] = new_cell
            self.left_len += 1
            # pop the new head from right
            # shift right by 1 logically: new head is right[1]
            # Use memmove via slice assignment only occasionally; here we track
            # an index instead. Simpler: actually maintain right as deque.
            # For simplicity, use offsets.
            # fallback: do left-shift every step is O(n). Let's track offset.
            raise RuntimeError  # replaced below


# Offset-based tape: store cells in a single bytearray arr with head at index
# `hp`. Leftmost logical cell is index `lo`, rightmost is index `hi`. When the
# head moves beyond [lo, hi], we extend the bytearray and memorymove if needed.
class Tape2:
    __slots__ = ("arr", "lo", "hi", "hp", "state", "steps", "halted")

    def __init__(self, cap=4096):
        self.arr = bytearray(cap)
        mid = cap // 2
        self.lo = self.hi = self.hp = mid
        self.state = 0
        self.steps = 0
        self.halted = False

    def _ensure(self):
        n = len(self.arr)
        if self.hp <= 16:
            shift = n // 2
            new = bytearray(n + shift)
            new[shift:shift + n] = self.arr
            self.arr = new
            self.lo += shift; self.hi += shift; self.hp += shift
        elif self.hp >= n - 16:
            self.arr.extend(b"\x00" * (n // 2))

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
            if self.hp > self.hi: self.hi = self.hp if self.arr[self.hp] else self.hi
        else:
            self.hp -= 1
            if self.hp < self.lo: self.lo = self.hp if self.arr[self.hp] else self.lo
        self.state = ns
        self.steps += 1
        self._ensure()

    def set_from_A(self, alpha, beta):
        """A(alpha, beta) = 0^inf (10)^(alpha-1) 0 1^beta [E>] 0^inf (wiki form).

        For alpha=1: tape is 0^inf 0 1^beta [E>] 0^inf = 0^inf 1^beta [E>] 0^inf
        (leading 0 merges with 0^inf).
        """
        assert alpha >= 1 and beta >= 1
        cap = max(4096, 4 * (alpha + beta + 64))
        self.arr = bytearray(cap)
        self.hp = cap - 32
        L = 2 * (alpha - 1) + 1 + beta
        start = self.hp - L
        p = start
        for _ in range(alpha - 1):
            self.arr[p] = 1; p += 1
            self.arr[p] = 0; p += 1
        self.arr[p] = 0; p += 1
        for _ in range(beta):
            self.arr[p] = 1; p += 1
        self.arr[self.hp] = 0
        # lo = leftmost nonzero; for alpha=1 there is no leading 1 so the first
        # "1" is the start of the beta-block.
        if alpha >= 2:
            self.lo = start
        else:
            self.lo = self.hp - beta
        self.hi = self.hp - 1
        self.state = STE
        self.steps = 0
        self.halted = False

    def extract_A(self):
        """Return (alpha, beta) if config matches 0^inf (10)^(alpha-1) 0 1^beta [E>] 0^inf.

        alpha >= 1, beta >= 1. For alpha=1 the tape reduces to 0^inf 1^beta [E>] 0^inf.
        """
        if self.state != STE: return None
        if self.arr[self.hp] != 0: return None
        for i in range(self.hp + 1, self.hi + 1):
            if self.arr[i]: return None
        cells = []  # r-to-l: cells[0] = arr[hp-1], cells[1] = arr[hp-2], ...
        p = self.hp - 1
        while p >= self.lo:
            cells.append(self.arr[p]); p -= 1
        # Trim trailing 0s (they merge with 0^inf).
        while cells and cells[-1] == 0:
            cells.pop()
        if not cells: return None  # no ones, not a valid A config
        # Count leading 1s = beta.
        i = 0
        while i < len(cells) and cells[i] == 1:
            i += 1
        beta = i
        if beta < 1: return None
        rest = cells[beta:]
        # alpha=1: rest is empty (trailing 0 was trimmed).
        if not rest:
            return (1, beta)
        # alpha >= 2: rest r-to-l must be [0, 0, 1, 0, 1, 0, 1, ...], ending in 1.
        if len(rest) < 3 or rest[0] != 0 or rest[1] != 0 or rest[2] != 1: return None
        alpha = 2
        j = 3
        while j < len(rest):
            if rest[j] != 0: return None
            j += 1
            if j >= len(rest) or rest[j] != 1: return None
            alpha += 1
            j += 1
        return (alpha, beta)


def verify_rule(a, b, max_steps=10**7):
    t = Tape2()
    t.set_from_A(a, b)
    assert t.extract_A() == (a, b), f"init mismatch"
    # Take one step to leave the macro config, then scan until we match again.
    t.step()
    check_every = 1  # we only check when state == E and head on 0 past rightmost 1
    while t.steps < max_steps:
        if t.halted: return t.steps, "HALT"
        # Quick filter before extract.
        if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
            res = t.extract_A()
            if res is not None:
                return t.steps, res
        t.step()
    return None, "TIMEOUT"


def count_from_blank(max_steps=10000):
    t = Tape2()
    while t.steps < max_steps:
        if t.halted: return t.steps, None
        if t.state == STE and t.arr[t.hp] == 0 and t.hp > t.hi:
            res = t.extract_A()
            if res is not None:
                return t.steps, res
        t.step()
    return None, None


def main():
    steps, first = count_from_blank(2000)
    print(f"From blank to first macro config A({first}): {steps} steps")

    print("\n--- Rule a > b:  A(a,b) -> A(a-b, 4b+2) ---")
    for (a, b) in [(2,1), (3,1), (5,2), (7,3), (10,4), (20,7), (50,3)]:
        s, nxt = verify_rule(a, b)
        exp = (a - b, 4*b + 2)
        ok = "OK" if nxt == exp else "MISMATCH"
        print(f"  A({a},{b}) -> {nxt}, steps={s}  [expect {exp}]  {ok}")

    print("\n--- Rule a < b:  A(a,b) -> A(2a+1, b-a) ---")
    for (a, b) in [(1,2), (1,3), (2,5), (3,10), (5,13), (7,20), (3, 50)]:
        s, nxt = verify_rule(a, b)
        exp = (2*a + 1, b - a)
        ok = "OK" if nxt == exp else "MISMATCH"
        print(f"  A({a},{b}) -> {nxt}, steps={s}  [expect {exp}]  {ok}")

    print("\n--- Rule a = b: A(a,a) -> Halt ---")
    for a in [1, 2, 3, 4, 5, 7, 10]:
        s, nxt = verify_rule(a, a)
        ok = "OK" if nxt == "HALT" else "MISMATCH"
        print(f"  A({a},{a}) -> {nxt}, steps={s}  {ok}")

    print("\n--- Macro iteration from A(1,2), 30 steps of the map ---")
    a, b = 1, 2
    for i in range(30):
        if a > b:
            na, nb = a - b, 4*b + 2; tag = ">"
        elif a < b:
            na, nb = 2*a + 1, b - a; tag = "<"
        else:
            print(f"  iter {i}: A({a},{b}) HALT"); break
        print(f"  iter {i}: A({a},{b}) [{tag}] -> A({na},{nb})")
        a, b = na, nb

    # Closed-form step counts.
    print("\n--- Step counts as function of a,b (guessing closed form) ---")
    print("a>b branch (fix a=100, vary b):")
    rows = []
    for b in range(1, 9):
        s, _ = verify_rule(100, b); rows.append((b, s))
        print(f"  A(100,{b}): {s} steps")
    # check linearity / quadratic in b.
    print("  differences:", [rows[i+1][1]-rows[i][1] for i in range(len(rows)-1)])
    print("  second differences:", [
      (rows[i+2][1]-rows[i+1][1]) - (rows[i+1][1]-rows[i][1])
      for i in range(len(rows)-2)])

    print("a>b branch (fix b=1, vary a):")
    rows = []
    for a in range(2, 11):
        s, _ = verify_rule(a, 1); rows.append((a, s))
        print(f"  A({a},1): {s} steps")
    print("  differences:", [rows[i+1][1]-rows[i][1] for i in range(len(rows)-1)])

    print("a<b branch (fix b=100, vary a):")
    rows = []
    for a in range(1, 9):
        s, _ = verify_rule(a, 100); rows.append((a, s))
        print(f"  A({a},100): {s} steps")
    print("  differences:", [rows[i+1][1]-rows[i][1] for i in range(len(rows)-1)])

    print("a<b branch (fix a=1, vary b):")
    rows = []
    for b in range(2, 11):
        s, _ = verify_rule(1, b); rows.append((b, s))
        print(f"  A(1,{b}): {s} steps")
    print("  differences:", [rows[i+1][1]-rows[i][1] for i in range(len(rows)-1)])


if __name__ == "__main__":
    main()
