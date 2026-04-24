#!/usr/bin/env python3
"""Simulator for 1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB.

Transitions:
  A: 0->1RB, 1->0RE
  B: 0->1LC, 1->1LD
  C: 0->0RA, 1->0LD
  D: 0->1LB, 1->0LA
  E: 0->1RF, 1->1RA
  F: 0->HALT, 1->1LB

Halt iff F reads a 0.  F is reached only via E,0 -> 1RF.

Wiki claim (Racheline):
  A(n,m) = 0^inf (01)^(3n-4) [A>] (01)^m 0^inf
  (head on first 0 of the right-block's (01)^m, state A, moving right.)
  Rules:
    A(n, 0)    -> A(2, 3n-4)
    A(2n, m)   -> A(3n, m-2)
    A(2n+1, m) -> A(3n+1, m-1)
    A(n, -1)   -> halt
  start from A(2, 0)
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"

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

    def __init__(self, cap=1 << 16):
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

    def pretty(self, window=60):
        lo = max(self.lo - 1, self.hp - window)
        hi = min(self.hi + 1, self.hp + window)
        s = []
        for i in range(lo, hi + 1):
            c = str(self.arr[i])
            if i == self.hp:
                c = f"[{STATE_NAMES[self.state]}]{c}"
            s.append(c)
        return "".join(s)


# ---------- A(n,m) macro encoding ----------
#
# A(n, m):  ... 0 (01)^(3n-4) [A>] (01)^m 0 ...
#   head on the first cell of (01)^m, which is a 0, state A.
#   left of head: (01)^(3n-4) ending at head-1 = '1'.
#   right of head: head+1 = '1', head+2 = '0', ..., a "01" pattern m times
#                  (head itself is the first '0'), then blanks.
#
# So the right block visible to the sim is: head on 0, followed by (10)^m
# (i.e. the pattern "1,0" repeated m times, where the 0 of each "10" is the
# start of the next (01) group). Equivalently: over indices [hp .. hp+2m-1],
# the tape reads "0,1,0,1,...,0,1" starting with 0 at position hp.


def setup_A(n, m, pad=128):
    """Build a tape representing A(n, m)."""
    assert n >= 2, "A(n,m) requires n >= 2 (left block is (01)^(3n-4))"
    assert m >= 0
    left_pairs = 3 * n - 4  # number of (01) groups to left of head
    right_pairs = m
    cap = 2 * pad + 2 * left_pairs + 2 * right_pairs + 32
    t = Tape(cap=cap)
    hp = pad + 2 * left_pairs  # head position
    # Write left block: (01)^left_pairs ending at hp-1.
    for i in range(left_pairs):
        base = pad + 2 * i
        t.arr[base]     = 0
        t.arr[base + 1] = 1
    # Head cell is 0 (first char of (01)^m, or blank if m=0).
    t.arr[hp] = 0
    # Right block: positions hp+1, hp+2, ..., hp+2m-1 encode
    # (01)^(m) starting at hp. So tape[hp+2i]=0, tape[hp+2i+1]=1 for 0<=i<m.
    # We've set hp (=hp+0) = 0. Now set hp+1..hp+2m-1.
    for i in range(m):
        t.arr[hp + 2 * i]     = 0
        t.arr[hp + 2 * i + 1] = 1
    # Update bounds: leftmost '1' is at pad+1 if left_pairs>0; rightmost '1'
    # is at hp + 2m - 1 if m>0.
    if left_pairs > 0:
        t.lo = pad + 1
    else:
        t.lo = hp  # fallback; no 1s to the left
    if right_pairs > 0:
        t.hi = hp + 2 * m - 1
    else:
        # If left has 1s, hi is already set by left block.
        t.hi = (pad + 2 * left_pairs - 1) if left_pairs > 0 else hp
    t.hp = hp
    t.state = STA
    t.steps = 0
    t.halted = False
    return t


def detect_A(t):
    """Return (n, m) if config matches A(n, m), else None.
    Requires state=A, head reads 0."""
    if t.state != STA or t.halted:
        return None
    if t.arr[t.hp] != 0:
        return None
    # Walk right: expect pattern (01)^m followed by blanks.
    # Starting at hp, read successive cells; they should be
    # 0,1,0,1,... We've verified hp=0, now read hp+1,hp+2,...
    i = t.hp
    m = 0
    # We're at a 0 at position i. Check if next is 1 — then we have a (01)
    # pair. Keep going.
    while i + 1 <= t.hi and t.arr[i] == 0 and t.arr[i + 1] == 1:
        m += 1
        i += 2
    # At index i: should be a 0 (which we just didn't pair with a 1 on the
    # right), OR we've reached past hi. If i <= hi, t.arr[i] must be 0 AND
    # either i == hi (and t.arr[i]=0 means we overshot, so fail) or the next
    # cell breaks the pattern. Actually, let's just require everything from
    # i onward up to hi+1 be 0.
    for j in range(i, t.hi + 1):
        if t.arr[j] != 0:
            return None
    # Now check left side: positions hp-1, hp-2, ... should follow pattern
    # 1,0,1,0,... for 2*(3n-4) cells, then all blanks.
    j = t.hp - 1
    pairs = 0
    while j - 1 >= t.lo and t.arr[j] == 1 and t.arr[j - 1] == 0:
        pairs += 1
        j -= 2
    # Everything left of j must be 0.
    for k in range(t.lo, j + 1):
        if t.arr[k] != 0:
            return None
    # pairs = 3n - 4, so n = (pairs + 4) / 3.
    if (pairs + 4) % 3 != 0:
        return None
    n = (pairs + 4) // 3
    if n < 2:
        return None
    return (n, m)


def run_macro_step(n, m, step_limit=10_000_000):
    """Run setup_A(n, m) until next A-configuration is reached or halt."""
    t = setup_A(n, m)
    # Take one step to avoid re-detecting initial.
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_A(t)
        if cfg is not None and t.steps > 0:
            return ("A", cfg[0], cfg[1]), t.steps
    return ("timeout",), t.steps


def verify_wiki_rules():
    """Check Racheline's rules against simulation."""
    print("Verifying Racheline's rules:")
    print()
    print("  A(n, 0) -> A(2, 3n-4)")
    for n in range(2, 10):
        res, dt = run_macro_step(n, 0)
        expected = ("A", 2, 3 * n - 4)
        ok = res == expected
        print(f"    A({n},0) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print()
    print("  A(2n, m) -> A(3n, m-2)    (even n, m >= 2)")
    for n in range(1, 6):
        for m in range(2, 6):
            res, dt = run_macro_step(2 * n, m)
            expected = ("A", 3 * n, m - 2)
            if expected[2] < 0:
                continue
            ok = res == expected
            print(f"    A({2*n},{m}) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print()
    print("  A(2n+1, m) -> A(3n+1, m-1)  (odd n, m >= 1)")
    for n in range(1, 6):
        for m in range(1, 6):
            res, dt = run_macro_step(2 * n + 1, m)
            expected = ("A", 3 * n + 1, m - 1)
            if expected[2] < 0:
                continue
            ok = res == expected
            print(f"    A({2*n+1},{m}) -> {res}  [{'OK' if ok else 'FAIL'} expected {expected}]  dt={dt}")

    print()
    print("  Halt cases (rules would drive m to -1):")
    # Halt reachable when the rule produces m = -1. For even n with m=1,
    # A(2n, 1) -> A(3n, -1) = halt.  Similarly? Actually m=-1 only from
    # even n (m-2) applied at m=1. Odd n takes m-1 so halts when m=0 but
    # m=0 is the reset rule. Let's just test.
    for n, m in [(2, 1), (4, 1), (6, 1), (8, 1)]:
        res, dt = run_macro_step(n, m)
        print(f"    A({n},{m}) -> {res}  dt={dt}")


def initial_reach(limit=200):
    """From blank tape, find smallest k such that config matches some A(n,m)."""
    t = Tape()
    for k in range(limit):
        cfg = detect_A(t)
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
        k, cfg = initial_reach(int(sys.argv[2]) if len(sys.argv) > 2 else 500)
        print(f"First A(n,m) reached at step {k}: {cfg}")
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
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 40
        n_, m_ = 2, 0
        total = 0
        print(f"{'i':>3} {'n':>6} {'m':>6} {'dt':>10} {'total':>14}")
        for i in range(N):
            res, dt = run_macro_step(n_, m_)
            total += dt
            print(f"{i:>3} {n_:>6} {m_:>6} {dt:>10} {total:>14}  {res}")
            if res[0] != "A":
                break
            n_, m_ = res[1], res[2]
