#!/usr/bin/env python3
"""Simulator for 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF.

Transitions:
  A: 0->1RB, 1->1RE
  B: 0->1LC, 1->1LD
  C: 0->HALT, 1->1LA
  D: 0->1LB, 1->1LE
  E: 0->0RF, 1->0RA
  F: 0->1LD, 1->1RF

Halt only via (C, 0) -> ---.

## Macro config (Racheline's wiki)

  A(m, k) with k >= 9 encodes
      0^inf  1^m  (01)^{k-9}  0  [A]>  0^inf
  head in state A facing right, on the first 0 of the right blank.

The "zebra count" is n := k - 9.  We work in n.  Wiki's argument is k = n + 9.

## Wiki rules (in Racheline's k notation; j a free Nat)

  A(m+4, 2j)     -> A(m, 3j)           k even: k -> 3k/2
  A(m+4, 2j+1)   -> A(m, 3j+1)         k odd:  k -> (3k-1)/2
  A(0, 2j)       -> halt
  A(0, 2j+1)     -> A(6j-23, 10)
  A(1, 2j)       -> A(6j-23, 10)
  A(1, 2j+1)     -> halt
  A(2, k)        -> halt  (all k)
  A(3, 2j)       -> A(6j-20, 10)
  A(3, 2j+1)     -> A(6j-18, 10)

  start from A(1, 10).

B(m) := A(m, 10) gives the compressed orbit driven by HydraMap on 10.
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF"

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


# ---------------- macro config ----------------

def setup_A(m, n, pad=80):
    """Build tape  0^inf 1^m (01)^n 0 [A]> 0^inf  (head on 0 at right)."""
    if m < 0 or n < 0:
        return None
    width = m + 2 * n + 1 + 2 * pad + 8
    t = Tape(cap=width)
    mid = pad
    # positions (mid .. mid+m-1) = 1^m
    for i in range(m):
        t.arr[mid + i] = 1
    # positions (mid+m .. mid+m+2n-1) = (01)^n, so 0,1,0,1,...
    zstart = mid + m
    for i in range(n):
        t.arr[zstart + 2 * i] = 0  # explicit
        t.arr[zstart + 2 * i + 1] = 1
    # position mid+m+2n = 0 (the separator)
    # head at mid+m+2n+1
    hp = mid + m + 2 * n + 1
    t.hp = hp
    t.state = STA
    t.steps = 0
    t.halted = False
    # lo/hi
    if m + 2 * n > 0:
        t.lo = mid
    else:
        t.lo = hp
    # last non-blank is at mid+m+2n-1 (the last 1 in zebra) if n >= 1
    # or at mid+m-1 (last 1 in ones block) if n = 0 and m >= 1
    # or at hp - 1 (which is 0) otherwise
    if n >= 1:
        t.hi = zstart + 2 * n - 1
    elif m >= 1:
        t.hi = mid + m - 1
    else:
        t.hi = hp - 1
    return t


def detect_A_config(t):
    """If current config matches A(m, n) shape, return (m, n); else None.

    Canonical parse of the tape between the leftmost nonblank and head-1:
    must match  1^m (01)^n 0  (m leading ones then (n+1) cells of 010...0 pattern).
    """
    if t.state != STA or t.halted:
        return None
    if t.arr[t.hp] != 0:
        return None
    # right of head must be all 0
    for i in range(t.hp + 1, t.hi + 1):
        if t.arr[i] != 0:
            return None
    # find leftmost nonblank position p0 < t.hp; if none, m=0, n=0
    p0 = None
    for i in range(max(0, t.lo), t.hp):
        if t.arr[i] != 0:
            p0 = i
            break
    if p0 is None:
        return (0, 0)
    # count leading 1s starting at p0
    m = 0
    p = p0
    while p < t.hp and t.arr[p] == 1:
        m += 1
        p += 1
    # remaining cells p..hp-1 must match (01)^n 0, i.e. odd length >= 1,
    # starting with 0 and alternating 0, 1, 0, 1, ..., 0.
    rem = t.hp - p
    if rem < 1 or rem % 2 == 0:
        return None
    for i in range(rem):
        expected = 0 if i % 2 == 0 else 1
        if t.arr[p + i] != expected:
            return None
    n = (rem - 1) // 2
    return (m, n)


def run_macro_step(m, n, step_limit=2_000_000):
    """Run from A(m, n) until next A-config or halt; return (result, dt)."""
    t = setup_A(m, n)
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_A_config(t)
        if cfg is not None and t.steps > 0:
            return ("A", cfg[0], cfg[1]), t.steps
    return ("timeout",), t.steps


# ---------------- verification ----------------

def hydra_map(k):
    """HydraMap on k: 3k/2 if even, (3k-1)/2 if odd."""
    return (3 * k) // 2


def verify_wiki_rules():
    print("Encoding: A(m, k) with k = n + 9,  tape = 0^inf 1^m (01)^n 0 [A]> 0^inf.")
    print("Working in n = zebra count.  Wiki's k = n + 9.\n")

    print("=== A(m+4, k) -> A(m, HydraMap(k))  [shift rule]")
    # Scan m, k exhaustively in small range
    fails = []
    for m in range(4, 10):           # LHS m
        for k in range(9, 25):       # LHS k (so n = k-9)
            n_lhs = k - 9
            if n_lhs < 0: continue
            k_rhs = hydra_map(k)
            n_rhs = k_rhs - 9
            res, dt = run_macro_step(m, n_lhs)
            expected = ("A", m - 4, n_rhs)
            ok = res == expected
            tag = "OK" if ok else "FAIL"
            print(f"    m={m:2d} k={k:2d} (n={n_lhs:2d}) -> {res}  expected {expected}  dt={dt} [{tag}]")
            if not ok: fails.append((m, k))

    print()
    print("=== Small-m cases")
    # A(0, 2j): halt
    print("  A(0, k even = 2j):")
    for j in range(5, 11):
        k = 2 * j
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(0, n)
        print(f"    k={k} n={n} -> {res}  dt={dt}  (expected halt)")
    # A(0, 2j+1): A(6j-23, 10)
    print("  A(0, k odd = 2j+1) -> A(6j-23, 10):")
    for j in range(5, 11):
        k = 2 * j + 1
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(0, n)
        exp_m = 6 * j - 23
        print(f"    k={k} n={n} j={j} -> {res}  expected A({exp_m}, 10)=A(_, n=1)  dt={dt}")
    # A(1, 2j): A(6j-23, 10)
    print("  A(1, k even = 2j) -> A(6j-23, 10):")
    for j in range(5, 11):
        k = 2 * j
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(1, n)
        exp_m = 6 * j - 23
        print(f"    k={k} n={n} j={j} -> {res}  expected A({exp_m}, 10)=A(_, n=1)  dt={dt}")
    # A(1, 2j+1): halt
    print("  A(1, k odd = 2j+1): expect halt")
    for j in range(5, 11):
        k = 2 * j + 1
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(1, n)
        print(f"    k={k} n={n} -> {res}  dt={dt}")
    # A(2, k): halt
    print("  A(2, k): expect halt")
    for k in range(9, 17):
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(2, n)
        print(f"    k={k} n={n} -> {res}  dt={dt}")
    # A(3, 2j): A(6j-20, 10)
    print("  A(3, k even = 2j) -> A(6j-20, 10):")
    for j in range(5, 11):
        k = 2 * j
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(3, n)
        print(f"    k={k} n={n} j={j} -> {res}  expected A({6*j-20}, 10)=A(_, n=1)  dt={dt}")
    # A(3, 2j+1): A(6j-18, 10)
    print("  A(3, k odd = 2j+1) -> A(6j-18, 10):")
    for j in range(5, 11):
        k = 2 * j + 1
        n = k - 9
        if n < 0: continue
        res, dt = run_macro_step(3, n)
        print(f"    k={k} n={n} j={j} -> {res}  expected A({6*j-18}, 10)=A(_, n=1)  dt={dt}")

    print()
    if fails:
        print(f"FAILURES in main rule: {fails}")
    else:
        print("All main rule instances passed.")


def initial_reach():
    """From blank tape, find smallest step k such that the config matches
    some A(m, n), and return (k, (m, n))."""
    t = Tape()
    for k in range(1000):
        cfg = detect_A_config(t)
        if cfg is not None and k > 0:
            return k, cfg
        if t.halted:
            return k, None
        t.step()
    return None, None


def orbit_from_start(N=40):
    """Follow macro rules starting from A(1, n=1) [wiki's A(1,10)]."""
    m, n = 1, 1
    total = 0
    print(f"{'i':>3} {'m':>8} {'n':>6} {'k':>6} {'dt':>12} {'total':>14}")
    for i in range(N):
        res, dt = run_macro_step(m, n)
        total += dt
        k = n + 9
        print(f"{i:>3} {m:>8} {n:>6} {k:>6} {dt:>12} {total:>14}  -> {res}")
        if res[0] != "A":
            break
        m, n = res[1], res[2]


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        verify_wiki_rules()
    elif cmd == "init":
        k, cfg = initial_reach()
        print(f"First A(m, n) reached at step {k}: {cfg}  (wiki k = {cfg[1]+9 if cfg else '?'})")
    elif cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 80
        t = Tape()
        for _ in range(n):
            if t.halted:
                print(f"step {t.steps}: HALT")
                break
            print(f"step {t.steps:4d}: {t.pretty(40)}")
            t.step()
    elif cmd == "orbit":
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 30
        orbit_from_start(N)
    elif cmd == "detect":
        # Run a specific setup and print the detected config
        m = int(sys.argv[2]); n = int(sys.argv[3])
        t = setup_A(m, n)
        print(f"setup A(m={m}, n={n}): {t.pretty(40)}")
        print(f"detect: {detect_A_config(t)}")
