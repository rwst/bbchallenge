#!/usr/bin/env python3
"""Simulator for 1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE.

Transitions:
  A: 0->1RB, 1->1LA
  B: 0->0LC, 1->0RC
  C: 0->1LE, 1->1RD
  D: 0->1RE, 1->1RC
  E: 0->1LF, 1->0LA
  F: 0->HALT, 1->1LE

Halt iff F reads a 0.  F is reached only via E,0 -> 1LF, so the head
must come from the E-state hitting a blank on the left side.

Wiki claim (Daniel Yuan):
  A(m, n) encodes config  "1^m [E] 1^n" (head on first cell of 1^n, state E).
  Rules:
    (0, 0) -> halt
    (1, n) -> halt
    (0, n+1) -> (2, n)
    (2m+2, n) -> (3m + n + 2, 2)
    (2m+3, n) -> (m, m + n + 4)
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE"

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
def setup_A(m, n, pad=64):
    """Build a tape representing 1^m [E] 1^n, with generous blank padding.

    Layout (indices ascending → right):
      [pad blanks] [1^m] [E head at first cell of right block] [1^n] [pad blanks]
    """
    cap = 2 * pad + m + n + 32
    t = Tape(cap=cap)
    mid = pad + m
    t.arr = bytearray(cap)
    for i in range(m):
        t.arr[pad + i] = 1
    for i in range(n):
        t.arr[mid + i] = 1
    t.lo = pad if m > 0 else mid
    t.hi = mid + n - 1 if n > 0 else mid - 1
    t.hp = mid
    t.state = STE
    t.steps = 0
    t.halted = False
    return t


def detect_A_config(t):
    """If current config has shape 1^m [E] 1^n over blanks, return (m, n).
    Otherwise return None."""
    if t.state != STE or t.halted:
        return None
    # head must be on 1 or blank (start of right 1-block)
    # Scan right for run of 1s
    i = t.hp
    while i <= t.hi and t.arr[i] == 1:
        i += 1
    # After that, all must be 0 (blank) up to hi
    for j in range(i, t.hi + 1):
        if t.arr[j] != 0:
            return None
    n = i - t.hp
    # Scan left for run of 1s immediately left of hp
    j = t.hp - 1
    while j >= t.lo and t.arr[j] == 1:
        j -= 1
    # Everything to left of j must be 0
    for k in range(t.lo, j + 1):
        if t.arr[k] != 0:
            return None
    m = t.hp - 1 - j
    return (m, n)


def run_macro_step(m, n, step_limit=10_000_000):
    """Run setup_A(m, n) until next A-configuration is reached or halt.
    Returns (result, dt) where result is ('A', m', n') or ('halt',) or ('timeout',)."""
    t = setup_A(m, n)
    # Take at least one step first to avoid re-detecting initial config
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_A_config(t)
        if cfg is not None and t.steps > 0:
            return ("A", cfg[0], cfg[1]), t.steps
    return ("timeout",), t.steps


def verify_wiki_rules():
    """Check Yuan's rules against simulation."""
    print("Verifying Yuan's rules:")
    print("  (0, n+1) -> (2, n)")
    for n in range(0, 6):
        res, dt = run_macro_step(0, n + 1)
        expected = ("A", 2, n)
        ok = res == expected
        print(f"    (0,{n+1}) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print("  (2m+2, n) -> (3m+n+2, 2)")
    for m in range(0, 4):
        for n in range(1, 5):
            res, dt = run_macro_step(2*m + 2, n)
            expected = ("A", 3*m + n + 2, 2)
            ok = res == expected
            print(f"    ({2*m+2},{n}) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print("  (2m+3, n) -> (m, m+n+4)")
    for m in range(0, 4):
        for n in range(1, 5):
            res, dt = run_macro_step(2*m + 3, n)
            expected = ("A", m, m + n + 4)
            ok = res == expected
            print(f"    ({2*m+3},{n}) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print("\nHalt cases:")
    for m, n in [(0, 0), (1, 0), (1, 1), (1, 2), (1, 3)]:
        res, dt = run_macro_step(m, n)
        print(f"    ({m},{n}) -> {res}  dt={dt}")


def initial_reach():
    """From blank tape, find smallest k such that the config matches some A(m, n)."""
    t = Tape()
    for k in range(200):
        cfg = detect_A_config(t)
        if cfg is not None and k > 0:
            return k, cfg
        if t.halted:
            return k, None
        t.step()
    return None, None


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        verify_wiki_rules()
    elif cmd == "init":
        k, cfg = initial_reach()
        print(f"First A(m,n) reached at step {k}: {cfg}")
    elif cmd == "trace":
        n = int(sys.argv[2]) if len(sys.argv) > 2 else 80
        t = Tape()
        for _ in range(n):
            if t.halted:
                print(f"step {t.steps}: HALT")
                break
            print(f"step {t.steps:4d}: [{STATE_NAMES[t.state]}] {t.pretty(30)}")
            t.step()
    elif cmd == "orbit":
        # Follow macro rules from (2, 2) (first macro config from blank tape) and
        # print the trajectory.
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
        m, n = 2, 2
        total = 0
        print(f"{'i':>3} {'m':>6} {'n':>6} {'dt':>10} {'total':>12}")
        for i in range(N):
            res, dt = run_macro_step(m, n)
            total += dt
            print(f"{i:>3} {m:>6} {n:>6} {dt:>10} {total:>12}  {res}")
            if res[0] != "A":
                break
            m, n = res[1], res[2]
