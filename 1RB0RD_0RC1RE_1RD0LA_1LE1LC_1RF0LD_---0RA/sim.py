#!/usr/bin/env python3
"""Simulator for 1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA ("Lucy's Moonlight").

Transitions:
  A: 0->1RB, 1->0RD
  B: 0->0RC, 1->1RE
  C: 0->1RD, 1->0LA
  D: 0->1LE, 1->1LC
  E: 0->1RF, 1->0LD
  F: 0->HALT, 1->0RA

Halt iff F reads a 0.  F is entered only via E,0 -> 1RF.

Ligocki's macro config (previous-work/wiki.txt):
  C(a, b, c) = 0^inf (1011)^a 1^b (10)^c  C> 0^inf
  C(a, b)    = C(a, b, 1)

Wiki rules (to be verified here):
  C(a+1, 3k)   -> C(a, 8k+6)
  C(a+2, 3k+1) -> C(a, 8k+16)
  C(a+2, 3k+2) -> C(a, 8k+22)
  C(0,   3k)   -> C(2k, 8)
  C(0,   3k+1) -> C(0, 8k+5)
  C(1,   3k+1) -> Halt
  C(0,   3k+2) -> C(0, 8k+5)
  C(1,   3k+2) -> C(2k+4, 8)
  start -(2 steps)-> C(0, 0)
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA"

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


# ---------- C(a, b, c) setup ----------
def setup_C(a, b, c=1, pad=128):
    """Build a tape representing  0^inf (1011)^a 1^b (10)^c [C] 0^inf.

    Layout (indices ascending -> right):
      [pad blanks] [1011 repeated a] [1 repeated b] [10 repeated c]
                   ^ start of a-block                ^ head just right of last (10)
    """
    core = []
    for _ in range(a):
        core.extend([1, 0, 1, 1])
    for _ in range(b):
        core.append(1)
    for _ in range(c):
        core.extend([1, 0])
    cap = 2 * pad + len(core) + 32
    t = Tape(cap=cap)
    t.arr = bytearray(cap)
    for i, v in enumerate(core):
        t.arr[pad + i] = v
    # Determine lo/hi: first and last 1-cell indices, or sentinel.
    ones_idx = [pad + i for i, v in enumerate(core) if v == 1]
    if ones_idx:
        t.lo, t.hi = ones_idx[0], ones_idx[-1]
    else:
        t.lo = t.hi = pad  # vacuous
    t.hp = pad + len(core)   # right of last "(10)" cell
    t.state = STC
    t.steps = 0
    t.halted = False
    return t


def detect_C_config(t):
    """If current config has the shape  0^inf (1011)^a 1^b (10)^c [C] 0^inf
    with state C reading a blank, return (a, b, c).  Else None.

    Left-to-right parse: leading blanks, then maximal (1011)^a, then 1^b,
    then (10)^c, then head on blank.
    """
    if t.state != STC or t.halted:
        return None
    if t.arr[t.hp] != 0:
        return None
    # Everything strictly right of hp must be blank (up to hi).
    for j in range(t.hp + 1, t.hi + 1):
        if t.arr[j] != 0:
            return None
    # Find first non-blank cell on the left.
    i = 0
    while i < t.hp and t.arr[i] == 0:
        i += 1
    if i == t.hp:
        return None  # empty → no final (10), not a C-config
    # Parse (1011)^a, reserving at least 2 cells at the tail for (10).
    a = 0
    while i + 3 < t.hp and t.hp - (i + 4) >= 2 and (
        t.arr[i] == 1 and t.arr[i+1] == 0 and
        t.arr[i+2] == 1 and t.arr[i+3] == 1):
        a += 1
        i += 4
    # Parse 1^b, reserving at least 2 cells at the tail for (10).
    b = 0
    while i < t.hp and t.hp - (i + 1) >= 2 and t.arr[i] == 1:
        b += 1
        i += 1
    # Parse (10)^c.
    c = 0
    while i + 1 < t.hp and t.arr[i] == 1 and t.arr[i+1] == 0:
        c += 1
        i += 2
    if i != t.hp or c < 1:
        return None
    return (a, b, c)


# Lightweight detector: only accept c = 1 (the standard macro form).
def detect_C_c1(t):
    r = detect_C_config(t)
    if r is None or r[2] != 1:
        return None
    return (r[0], r[1])


def run_macro_step(a, b, c=1, step_limit=5_000_000):
    """Run setup_C(a,b,c) until next C(a', b', 1) or halt."""
    t = setup_C(a, b, c)
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_C_c1(t)
        if cfg is not None and t.steps > 0:
            return ("C", cfg[0], cfg[1]), t.steps
    return ("timeout",), t.steps


def verify_wiki_rules():
    print(f"TM: {TM_STR}\n")
    print("Verifying Ligocki rules (and collecting dt):\n")

    def check(label, a, b, expected, note=""):
        res, dt = run_macro_step(a, b)
        ok = res == expected
        tag = "OK  " if ok else "FAIL"
        exp_str = f"{expected}"
        print(f"  {label:<22}  C({a},{b}) -> {res}  [{tag} expected {exp_str}]  dt={dt}  {note}")
        return dt if ok else None

    print("R1: C(a+1, 3k) -> C(a, 8k+6)")
    for a in range(0, 4):
        for k in range(0, 5):
            check("R1", a + 1, 3 * k, ("C", a, 8 * k + 6))

    print("\nR2: C(a+2, 3k+1) -> C(a, 8k+16)")
    for a in range(0, 4):
        for k in range(0, 5):
            check("R2", a + 2, 3 * k + 1, ("C", a, 8 * k + 16))

    print("\nR3: C(a+2, 3k+2) -> C(a, 8k+22)")
    for a in range(0, 4):
        for k in range(0, 5):
            check("R3", a + 2, 3 * k + 2, ("C", a, 8 * k + 22))

    print("\nE1: C(0, 3k) -> C(2k, 8)  (k >= 1 to avoid start)")
    for k in range(1, 5):
        check("E1", 0, 3 * k, ("C", 2 * k, 8))

    print("\nE2: C(0, 3k+1) -> C(0, 8k+5)")
    for k in range(0, 5):
        check("E2", 0, 3 * k + 1, ("C", 0, 8 * k + 5))

    print("\nE3: C(0, 3k+2) -> C(0, 8k+5)")
    for k in range(0, 5):
        check("E3", 0, 3 * k + 2, ("C", 0, 8 * k + 5))

    print("\nH1: C(1, 3k+1) -> Halt")
    for k in range(0, 5):
        res, dt = run_macro_step(1, 3 * k + 1)
        print(f"  H1                      C(1,{3*k+1}) -> {res}  dt={dt}")

    print("\nE4: C(1, 3k+2) -> C(2k+4, 8)")
    for k in range(0, 5):
        check("E4", 1, 3 * k + 2, ("C", 2 * k + 4, 8))

    print("\nDegenerate halt: C(0, 0)")
    res, dt = run_macro_step(0, 0)
    print(f"  (start case)          C(0,0) -> {res}  dt={dt}")


def initial_reach():
    """From blank tape, find smallest k such that the config matches C(0, 0).

    Wiki says "Start -(2)-> C(0,0)" but that would require the tape after
    2 steps to have state C and detectable (10)^1 pattern.  Check explicitly.
    """
    t = Tape()
    print(f"step {t.steps:4d}: [{STATE_NAMES[t.state]}] {t.pretty(30)}")
    for k in range(60):
        t.step()
        r = detect_C_c1(t)
        tag = f" MATCH C{r}" if r is not None else ""
        print(f"step {t.steps:4d}: [{STATE_NAMES[t.state]}] {t.pretty(30)}{tag}")
        if t.halted:
            break


def trace(n):
    t = Tape()
    for _ in range(n):
        print(f"step {t.steps:5d}: [{STATE_NAMES[t.state]}] {t.pretty(40)}")
        if t.halted:
            break
        t.step()


def orbit(N):
    """Follow macro rules starting from C(0,0) and print the trajectory."""
    a, b = 0, 0
    total = 2  # start -> C(0,0) takes 2 steps (per wiki); verified separately
    print(f"{'i':>4} {'a':>8} {'b':>8} {'dt':>12} {'total':>14}")
    for i in range(N):
        res, dt = run_macro_step(a, b)
        total += dt
        print(f"{i:>4} {a:>8} {b:>8} {dt:>12} {total:>14}  {res}")
        if res[0] != "C":
            break
        a, b = res[1], res[2]


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        verify_wiki_rules()
    elif cmd == "init":
        initial_reach()
    elif cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 80
        trace(n)
    elif cmd == "orbit":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
        orbit(N)
    else:
        print(f"unknown: {cmd}", file=sys.stderr); sys.exit(1)
