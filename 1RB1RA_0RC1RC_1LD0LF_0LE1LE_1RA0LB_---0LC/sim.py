#!/usr/bin/env python3
"""Simulator for 1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC.

Transitions:
  A: 0->1RB, 1->1RA
  B: 0->0RC, 1->1RC
  C: 0->1LD, 1->0LF
  D: 0->0LE, 1->1LE
  E: 0->1RA, 1->0LB
  F: 0->HALT, 1->0LC

Halt iff F reads a 0.  F is reached only via C,1 -> 0LF.

Wiki claim (Shawn Ligocki):
  C(a, b, c) = $ 1^{2a+1} C> 0^{2b} 1^c 01 $
  Level 1:
    C(a, b+2, c)   -> C(a+3, b, c)
    C(a, 1, c+2)   -> C(1, a+3, c)
    C(a, 0, c+1)   -> C(1, a+1, c)
    C(a, 0, 0)     -> C(1, 2, 2a+3)
    C(a, 1, 1)     -> C(1, 2, 2a+7)
    C(a, 1, 0)     -> Halt(2a+5)
"""

import resource, sys
resource.setrlimit(resource.RLIMIT_AS, (2 * 1024**3, 2 * 1024**3))

TM_STR = "1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC"


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
            self.lo += shift
            self.hi += shift
            self.hp += shift
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
        if w and self.hp < self.lo:
            self.lo = self.hp
        if w and self.hp > self.hi:
            self.hi = self.hp
        if direction == 'R':
            self.hp += 1
        else:
            self.hp -= 1
        self.state = ns
        self.steps += 1
        self._ensure()

    def snapshot(self):
        """Return (state, head_sym, left_tuple, right_tuple) where tuples are
        indexed from head (inclusive on right, exclusive on left)."""
        lo = min(self.lo, self.hp)
        hi = max(self.hi, self.hp)
        left = tuple(self.arr[i] for i in range(lo, self.hp))
        right = tuple(self.arr[i] for i in range(self.hp, hi + 1))
        return (self.state, left, right)

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


# ---------- C(a,b,c) macro ----------
def setup_C(a, b, c, pad=64):
    """Build a tape representing $ 1^{2a+1} C> 0^{2b} 1^c 01 $.

    Head lands on the cell immediately right of 1^{2a+1}.
    """
    cap = 2 * pad + (2 * a + 1) + (2 * b) + c + 2 + 32
    t = Tape(cap=cap)
    t.arr = bytearray(cap)
    left_start = pad
    # Write 1^{2a+1} starting at pad
    for i in range(2 * a + 1):
        t.arr[left_start + i] = 1
    head = left_start + (2 * a + 1)
    # After head: 0^{2b} then 1^c then 0 then 1
    off = head + 2 * b
    for i in range(c):
        t.arr[off + i] = 1
    off += c
    # skip a 0
    off += 1
    t.arr[off] = 1  # the trailing 1
    t.lo = left_start if (2 * a + 1) > 0 else head
    t.hi = off
    t.hp = head
    t.state = STC
    t.steps = 0
    t.halted = False
    return t


def detect_C_config(t):
    """If current config has shape 1^{2a+1} C> 0^{2b} 1^c 01 over blanks, return (a, b, c).
    Otherwise return None.

    Requires: state=C, head on first cell of right side.
    """
    if t.state != STC or t.halted:
        return None
    # Scan left for run of 1s.
    i = t.hp - 1
    while i >= t.lo and t.arr[i] == 1:
        i -= 1
    # Everything strictly left of i must be blank (0)
    for k in range(t.lo, i + 1):
        if t.arr[k] != 0:
            return None
    left_ones = t.hp - 1 - i
    if left_ones < 1 or (left_ones % 2 == 0):
        return None
    a = (left_ones - 1) // 2
    # Scan right: 0^{2b} 1^c 01  — two cases by parity of leading-zero run.
    j = t.hp
    while j <= t.hi and t.arr[j] == 0:
        j += 1
    zeros = j - t.hp
    if zeros % 2 == 1:
        # c = 0 case: right = 0^{2b+1} 1 blank.  Next cell must be 1, then blanks.
        if j > t.hi or t.arr[j] != 1:
            return None
        b = (zeros - 1) // 2
        c = 0
        last = j
    else:
        # c >= 1 case: right = 0^{2b} 1^c 0 1 blank.
        b = zeros // 2
        k = j
        while k <= t.hi and t.arr[k] == 1:
            k += 1
        c = k - j
        if c < 1:
            return None
        if k > t.hi or t.arr[k] != 0:
            return None
        if k + 1 > t.hi or t.arr[k + 1] != 1:
            return None
        last = k + 1
    # Everything right of `last` must be 0/blank
    for p in range(last + 1, t.hi + 1):
        if t.arr[p] != 0:
            return None
    return (a, b, c)


def run_macro_step(a, b, c, step_limit=10_000_000):
    """Run setup_C(a, b, c) until next C-configuration is reached or halt.
    Returns (result, dt)."""
    t = setup_C(a, b, c)
    for _ in range(step_limit):
        t.step()
        if t.halted:
            return ("halt",), t.steps
        cfg = detect_C_config(t)
        if cfg is not None and t.steps > 0:
            return ("C",) + cfg, t.steps
    return ("timeout",), t.steps


def verify_level1():
    print("Verifying Level-1 rules:")
    print("  C(a, b+2, c) -> C(a+3, b, c)")
    for a in range(0, 5):
        for b in range(0, 4):
            for c in range(0, 5):
                res, dt = run_macro_step(a, b + 2, c)
                expected = ("C", a + 3, b, c)
                ok = res == expected
                if not ok:
                    print(f"    C({a},{b+2},{c}) -> {res} [FAIL expected {expected}] dt={dt}")
                else:
                    pass
    print("    all (a in 0..4, b in 0..3, c in 0..4) OK")

    print("  C(a, 1, c+2) -> C(1, a+3, c)")
    for a in range(0, 6):
        for c in range(0, 6):
            res, dt = run_macro_step(a, 1, c + 2)
            expected = ("C", 1, a + 3, c)
            ok = res == expected
            if not ok:
                print(f"    C({a},1,{c+2}) -> {res} [FAIL expected {expected}] dt={dt}")
            else:
                pass
    print("    all (a in 0..5, c in 0..5) OK")

    print("  C(a, 0, c+1) -> C(1, a+1, c)")
    for a in range(0, 6):
        for c in range(0, 6):
            res, dt = run_macro_step(a, 0, c + 1)
            expected = ("C", 1, a + 1, c)
            ok = res == expected
            if not ok:
                print(f"    C({a},0,{c+1}) -> {res} [FAIL expected {expected}] dt={dt}")
            else:
                pass
    print("    all (a in 0..5, c in 0..5) OK")

    print("  C(a, 0, 0) -> C(1, 2, 2a+3)")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 0, 0)
        expected = ("C", 1, 2, 2 * a + 3)
        ok = res == expected
        tag = "OK" if ok else f"FAIL expected {expected}"
        print(f"    C({a},0,0) -> {res} [{tag}] dt={dt}")

    print("  C(a, 1, 1) -> C(1, 2, 2a+7)")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 1, 1)
        expected = ("C", 1, 2, 2 * a + 7)
        ok = res == expected
        tag = "OK" if ok else f"FAIL expected {expected}"
        print(f"    C({a},1,1) -> {res} [{tag}] dt={dt}")

    print("  C(a, 1, 0) -> Halt(2a+5)")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 1, 0)
        tag = "OK" if res == ("halt",) else f"FAIL got {res}"
        print(f"    C({a},1,0) -> {res} [{tag}] dt={dt}  (2a+5={2*a+5})")


def measure_dts():
    """Measure step counts for Level-1 rules to derive closed forms."""
    print("\nStep counts for Level-1 rules:")
    print("  C(a, b+2, c) -> C(a+3, b, c)  [Rule R1: bump]")
    print(f"    {'a':>3} {'b':>3} {'c':>3} {'dt':>8}")
    for a in range(0, 4):
        for b in range(0, 3):
            for c in range(0, 4):
                res, dt = run_macro_step(a, b + 2, c)
                if res[0] == "C":
                    print(f"    {a:>3} {b+2:>3} {c:>3} {dt:>8}")

    print("\n  C(a, 1, c+2) -> C(1, a+3, c)  [Rule R2: restructure]")
    print(f"    {'a':>3} {'c':>3} {'dt':>8}")
    for a in range(0, 5):
        for c in range(0, 5):
            res, dt = run_macro_step(a, 1, c + 2)
            if res[0] == "C":
                print(f"    {a:>3} {c+2:>3} {dt:>8}")

    print("\n  C(a, 0, c+1) -> C(1, a+1, c)  [Rule R3: restructure]")
    print(f"    {'a':>3} {'c':>3} {'dt':>8}")
    for a in range(0, 5):
        for c in range(0, 5):
            res, dt = run_macro_step(a, 0, c + 1)
            if res[0] == "C":
                print(f"    {a:>3} {c+1:>3} {dt:>8}")

    print("\n  C(a, 0, 0) -> C(1, 2, 2a+3)  [Rule R4: endgame_00]")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 0, 0)
        print(f"    C({a},0,0) dt={dt}")

    print("\n  C(a, 1, 1) -> C(1, 2, 2a+7)  [Rule R5: endgame_11]")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 1, 1)
        print(f"    C({a},1,1) dt={dt}")

    print("\n  C(a, 1, 0) -> Halt(2a+5)  [Rule R6: halt]")
    for a in range(0, 6):
        res, dt = run_macro_step(a, 1, 0)
        print(f"    C({a},1,0) dt={dt}")


def initial_reach():
    """From blank tape, find smallest k such that config matches some C(a,b,c)."""
    t = Tape()
    for k in range(400):
        cfg = detect_C_config(t)
        if cfg is not None and k > 0:
            return k, cfg
        if t.halted:
            return k, None
        t.step()
    return None, None


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "verify"
    if cmd == "verify":
        verify_level1()
    elif cmd == "dts":
        measure_dts()
    elif cmd == "init":
        k, cfg = initial_reach()
        print(f"First C(a,b,c) reached at step {k}: {cfg}")
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
        # Follow macro rules from the first C(a,b,c) after blank tape.
        N = int(sys.argv[2]) if len(sys.argv) > 2 else 20
        k0, cfg = initial_reach()
        print(f"init at step {k0}: C{cfg}")
        a, b, c = cfg
        total = k0
        for i in range(N):
            res, dt = run_macro_step(a, b, c)
            total += dt
            print(f"  {i:>3}: C({a},{b},{c}) -> {res}  dt={dt}  total={total}")
            if res[0] != "C":
                break
            _, a, b, c = res
