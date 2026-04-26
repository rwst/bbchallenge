#!/usr/bin/env python3
"""Simulator for 1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE.

Transitions:
  A: 0->1RB, 1->1LE
  B: 0->0LC, 1->0LB
  C: 0->1RD, 1->1LC
  D: 0->1RD, 1->1RA
  E: 0->1RF, 1->0LA
  F: 0->HALT, 1->1RE

Halt iff F reads a 0.  F is reached only from E,0 -> 1RF (writes 1, moves R)
and F gets entered after that, head is to the right.

Wiki claim (Racheline):
  A(n+6, m) = 0^inf <C (10)^n 1^m 0^inf
  Rules:
    A(2n,   m)   -> A(3n,   m-3)
    A(2n+1, m)   -> A(3n+1, m-2)
    A(2n,   0)   -> translated cycler
    A(2n+1, 0)   -> A(6, 6n-15)
    A(n, 1)      = A(n+1, 0)
    A(2n,   2)   -> halt
    A(2n+1, 2)   -> A(6, 6n-10)
  start from A(6, 3)
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE"

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


def run_from_blank(n):
    t = Tape()
    for _ in range(n):
        if t.halted:
            return t
        t.step()
    return t


# ---------- Macro analysis ----------
# A(N, m) interpretation: we need to determine where the head is.
# Per wiki: "0^inf <C (10)^n 1^m 0^inf" with N = n + 6.
# The "<C" suggests state C, head reading the 0 just LEFT of the pattern.
# Try this interpretation: head on a 0 cell, with `(10)^n 1^m` to the right.

def setup_A(N, m, pad=128):
    """Build a tape representing 0^inf [C](0) (10)^n 1^m 0^inf
    where N = n + 6 (so n = N - 6).  Head on the 0 cell just left of the
    (10)^n 1^m block, state C.

    Actually try several interpretations; return setup as bytearray + position.
    """
    assert N >= 6, f"N={N} < 6"
    n = N - 6
    cap = 2 * pad + 2*n + m + 32
    t = Tape(cap=cap)
    t.arr = bytearray(cap)
    # Head sits on a 0; the (10)^n 1^m block starts at hp+1.
    hp = pad
    # Lay out (10)^n 1^m starting at hp+1.
    pos = hp + 1
    for _ in range(n):
        t.arr[pos] = 1; pos += 1
        t.arr[pos] = 0; pos += 1
    for _ in range(m):
        t.arr[pos] = 1; pos += 1
    t.lo = hp + 1 if (n > 0 or m > 0) else hp
    t.hi = pos - 1 if pos > hp + 1 else hp
    if t.hi < t.lo:
        t.hi = t.lo = hp
    t.hp = hp
    t.state = STC
    t.steps = 0
    t.halted = False
    return t


def detect_A_config(t):
    """Detect if current config matches 0^inf <C (10)^n 1^m 0^inf, i.e.
    state C, head on 0, with (10)^n 1^m to the right (n>=0, m>=0), all
    blanks elsewhere.  Returns (N, m) with N = n + 6 if matched, else None.
    """
    if t.halted or t.state != STC:
        return None
    if t.arr[t.hp] != 0:
        return None
    # All cells <= hp must be 0.
    for i in range(t.lo, t.hp):
        if t.arr[i] != 0:
            return None
    # Right of head: parse (10)^n 1^m.
    i = t.hp + 1
    n = 0
    while i + 1 <= t.hi and t.arr[i] == 1 and t.arr[i+1] == 0:
        n += 1
        i += 2
    # Now at a position; remaining ones run = m
    m = 0
    while i <= t.hi and t.arr[i] == 1:
        m += 1
        i += 1
    # rest must be 0
    for j in range(i, t.hi + 1):
        if t.arr[j] != 0:
            return None
    return (n + 6, m)


def run_macro_step(N, m, step_limit=10_000_000):
    """Run setup_A(N, m) until next A-config or halt or timeout."""
    t = setup_A(N, m)
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_A_config(t)
        if cfg is not None and t.steps > 0:
            return ("A", cfg[0], cfg[1]), t.steps
    return ("timeout",), t.steps


def initial_reach():
    """From blank tape, find smallest k such that the config matches A(N,m)."""
    t = Tape()
    for k in range(2000):
        cfg = detect_A_config(t)
        if cfg is not None and k > 0:
            return k, cfg
        if t.halted:
            return k, None
        t.step()
    return None, None


def verify_dt_formulas():
    """Check the closed-form dt formulas derived from sample data."""
    print("Verifying closed-form dt formulas (n in 3..10):")
    print("  R_even   (m=3..7, n>=3):    A(2n,m)   -> A(3n,m-3)    dt = 6n^2 - 10n - 7")
    for n in range(3, 11):
        for m in range(3, 6):
            res, dt = run_macro_step(2*n, m)
            exp_dt = 6*n*n - 10*n - 7
            ok = res == ("A", 3*n, m-3) and dt == exp_dt
            print(f"    A({2*n},{m})  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")

    print("  R_odd    (m=3..7, n>=3):    A(2n+1,m) -> A(3n+1,m-2)  dt = 6n^2 - 10n + 2")
    for n in range(3, 11):
        for m in range(3, 6):
            res, dt = run_macro_step(2*n+1, m)
            exp_dt = 6*n*n - 10*n + 2
            ok = res == ("A", 3*n+1, m-2) and dt == exp_dt
            print(f"    A({2*n+1},{m})  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")

    print("  R_odd_0  (m=0,   n>=3):     A(2n+1,0) -> A(6,6n-15)   dt = 6n^2 - 22n + 19")
    for n in range(3, 11):
        res, dt = run_macro_step(2*n+1, 0)
        exp_dt = 6*n*n - 22*n + 19
        ok = res == ("A", 6, 6*n-15) and dt == exp_dt
        print(f"    A({2*n+1},0)  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")

    print("  R_even_0 (m=0,   n>=4):     A(2n,0)   -> A(6,0)       dt = 6n^2 - 34n + 48")
    for n in range(4, 11):
        res, dt = run_macro_step(2*n, 0)
        exp_dt = 6*n*n - 34*n + 48
        ok = res == ("A", 6, 0) and dt == exp_dt
        print(f"    A({2*n},0)  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")

    print("  R_even_2 (m=2,   n>=3):     A(2n,2)   -> halt         dt = 6n^2 - 16n + 4")
    for n in range(3, 11):
        res, dt = run_macro_step(2*n, 2)
        exp_dt = 6*n*n - 16*n + 4
        ok = res == ("halt",) and dt == exp_dt
        print(f"    A({2*n},2)  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")

    print("  R_odd_2  (m=2,   n>=3):     A(2n+1,2) -> A(6,6n-10)   dt = 6n^2 - 10n + 1")
    for n in range(3, 11):
        res, dt = run_macro_step(2*n+1, 2)
        exp_dt = 6*n*n - 10*n + 1
        ok = res == ("A", 6, 6*n-10) and dt == exp_dt
        print(f"    A({2*n+1},2)  dt={dt} expected {exp_dt}  out={res}  {'OK' if ok else 'FAIL'}")


def verify_wiki_rules():
    """Check Racheline's rules against simulation."""
    print("Verifying Racheline's rules:")
    # A(2n, m) -> A(3n, m-3)  (assumes m >= 3? Test for various m.)
    print("  A(2n, m) -> A(3n, m-3)")
    for n in range(3, 8):  # 2n must be >= 6 => n >= 3
        for m in range(3, 7):
            res, dt = run_macro_step(2*n, m)
            expected = ("A", 3*n, m - 3)
            ok = res == expected
            mark = "OK" if ok else "FAIL"
            print(f"    A({2*n},{m}) -> {res}  [{mark} expected {expected}]  dt={dt}")

    print("  A(2n+1, m) -> A(3n+1, m-2)")
    for n in range(3, 8):
        for m in range(2, 7):
            res, dt = run_macro_step(2*n+1, m)
            expected = ("A", 3*n+1, m-2)
            ok = res == expected
            mark = "OK" if ok else "FAIL"
            print(f"    A({2*n+1},{m}) -> {res}  [{mark} expected {expected}]  dt={dt}")

    print("  A(2n+1, 0) -> A(6, 6n-15)  (need 6n-15 >= 0, n >= 3)")
    for n in range(3, 8):
        res, dt = run_macro_step(2*n+1, 0)
        expected = ("A", 6, 6*n - 15)
        ok = res == expected
        mark = "OK" if ok else "FAIL"
        print(f"    A({2*n+1},0) -> {res}  [{mark} expected {expected}]  dt={dt}")

    print("  A(n, 1) = A(n+1, 0)  (i.e. A(n,1) reaches A(n+1,0) trivially)")
    for N in range(6, 14):
        res, dt = run_macro_step(N, 1)
        expected = ("A", N+1, 0)
        ok = res == expected
        mark = "OK" if ok else "FAIL"
        print(f"    A({N},1) -> {res}  [{mark} expected {expected}]  dt={dt}")

    print("  A(2n, 2) -> halt")
    for n in range(3, 8):
        res, dt = run_macro_step(2*n, 2)
        ok = res[0] == "halt"
        mark = "OK" if ok else "FAIL"
        print(f"    A({2*n},2) -> {res}  [{mark}]  dt={dt}")

    print("  A(2n+1, 2) -> A(6, 6n-10)  (need 6n-10 >= 0 and 2n+1 >= 7, n >= 3)")
    for n in range(3, 8):
        res, dt = run_macro_step(2*n+1, 2)
        expected = ("A", 6, 6*n - 10)
        ok = res == expected
        mark = "OK" if ok else "FAIL"
        print(f"    A({2*n+1},2) -> {res}  [{mark} expected {expected}]  dt={dt}")


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        verify_wiki_rules()
    elif cmd == "dt":
        verify_dt_formulas()
    elif cmd == "init":
        k, cfg = initial_reach()
        print(f"First A(N,m) reached at step {k}: {cfg}")
    elif cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 100
        t = Tape()
        for _ in range(n):
            print(f"step {t.steps:4d}: {t.pretty(40)}")
            if t.halted:
                print(f"step {t.steps}: HALT")
                break
            t.step()
    elif cmd == "orbit":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
        # start from A(6, 3) per wiki
        Nm, mm = 6, 3
        total = 0
        print(f"{'i':>3} {'N':>6} {'m':>6} {'dt':>10} {'total':>12}")
        for i in range(N):
            res, dt = run_macro_step(Nm, mm)
            total += dt
            print(f"{i:>3} {Nm:>6} {mm:>6} {dt:>10} {total:>12}  {res}")
            if res[0] != "A":
                break
            Nm, mm = res[1], res[2]
