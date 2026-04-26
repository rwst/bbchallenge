#!/usr/bin/env python3
"""Canonical rule verification for 1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF.

The macro config is A(m, n) with canonical m ≥ 1 (since leading blank 0s absorb
the first cell of any zebra pair).  Test rule-by-rule in (m, n) directly.
"""
import sim

def test(m, n, expected, tag):
    res, dt = sim.run_macro_step(m, n)
    ok = res == expected
    mark = "OK" if ok else "FAIL"
    print(f"    [{mark}] {tag}: A(m={m},n={n}) -> {res}  dt={dt}  exp {expected}")
    return ok, dt

def formula(dt_fn, tag, params):
    print(f"  {tag}: {params}")
    all_ok = True
    for (m, n, expected) in params:
        ok, dt = test(m, n, expected, f"")
        if not ok: all_ok = False
    return all_ok


print("=" * 60)
print("SHIFT RULES (m ≥ 5): A(m+4, n) -> A(m, n')")
print("=" * 60)
print()
print("Shift_even: A(m+4, 2i) -> A(m, 3i+4),  dt = 6i² + 28i + 28")
# Verify for many (m, i)
fails_se = []
for m in range(1, 10):
    for i in range(0, 10):
        n_lhs = 2*i
        n_rhs = 3*i + 4
        res, dt = sim.run_macro_step(m + 4, n_lhs)
        expected = ("A", m, n_rhs)
        exp_dt = 6*i*i + 28*i + 28
        ok = res == expected and dt == exp_dt
        if not ok: fails_se.append((m, i, res, dt, expected, exp_dt))
print(f"    tested 9×10 cases; fails={len(fails_se)}")
if fails_se: print(fails_se[:3])

print()
print("Shift_odd: A(m+4, 2i+1) -> A(m, 3i+6),  dt = 6i² + 40i + 54")
fails_so = []
for m in range(1, 10):
    for i in range(0, 10):
        n_lhs = 2*i + 1
        n_rhs = 3*i + 6
        res, dt = sim.run_macro_step(m + 4, n_lhs)
        expected = ("A", m, n_rhs)
        exp_dt = 6*i*i + 40*i + 54
        ok = res == expected and dt == exp_dt
        if not ok: fails_so.append((m, i, res, dt, expected, exp_dt))
print(f"    tested 9×10 cases; fails={len(fails_so)}")
if fails_so: print(fails_so[:3])

print()
print("=" * 60)
print("M-BRIDGE (wiki m=0 case canonicalizes to m=1):")
print("=" * 60)
print()
print("A(4, 2i) -> A(1, 3i+3),  dt = 6i² + 28i + 28")
fails_m4e = []
for i in range(0, 10):
    res, dt = sim.run_macro_step(4, 2*i)
    expected = ("A", 1, 3*i + 3)
    exp_dt = 6*i*i + 28*i + 28
    ok = res == expected and dt == exp_dt
    if not ok: fails_m4e.append((i, res, dt, expected, exp_dt))
print(f"    tested 10 cases; fails={len(fails_m4e)}")
if fails_m4e: print(fails_m4e[:3])

print()
print("A(4, 2i+1) -> A(1, 3i+5),  dt = 6i² + 40i + 54")
fails_m4o = []
for i in range(0, 10):
    res, dt = sim.run_macro_step(4, 2*i + 1)
    expected = ("A", 1, 3*i + 5)
    exp_dt = 6*i*i + 40*i + 54
    ok = res == expected and dt == exp_dt
    if not ok: fails_m4o.append((i, res, dt, expected, exp_dt))
print(f"    tested 10 cases; fails={len(fails_m4o)}")
if fails_m4o: print(fails_m4o[:3])

print()
print("=" * 60)
print("SMALL-m HALT / RESET RULES")
print("=" * 60)

def test_range(m_vals, n_rule, tag):
    """m_vals: list of LHS m. n_rule(i) -> n_lhs.  Expected: from row."""
    print(f"\n  {tag}")
    for m in m_vals:
        for i in range(10):
            n = n_rule(i)
            res, dt = sim.run_macro_step(m, n)
            print(f"    m={m} i={i} n={n}: {res} dt={dt}")

# m=1, n even (wiki: A(1, k even=2j) → A(6j-23, 10)) -- i.e. canonical A(1, n=2i)
# For i = j - 5, n = 2(j-5) = 2j-10; so j = i+5, RHS m = 6j-23 = 6i+7.
print("\n  m=1, n even: A(1, 2i) -> A(6i+7, 1),  dt = ?")
for i in range(0, 8):
    n = 2*i
    res, dt = sim.run_macro_step(1, n)
    expected = ("A", 6*i + 7, 1)
    print(f"    i={i} n={n}: {res} dt={dt}  exp {expected}")

# m=1, n odd → halt (wiki: A(1, 2j+1) halt)
print("\n  m=1, n odd: A(1, 2i+1) -> halt")
for i in range(0, 8):
    n = 2*i + 1
    res, dt = sim.run_macro_step(1, n)
    print(f"    i={i} n={n}: {res} dt={dt}")

# m=2: always halt
print("\n  m=2, any n: A(2, n) -> halt")
for n in range(0, 16):
    res, dt = sim.run_macro_step(2, n)
    print(f"    n={n}: {res} dt={dt}")

# m=3, n even → A(6i+10, 1)
print("\n  m=3, n even: A(3, 2i) -> A(6i+10, 1)")
for i in range(0, 8):
    n = 2*i
    res, dt = sim.run_macro_step(3, n)
    expected = ("A", 6*i + 10, 1)
    print(f"    i={i} n={n}: {res} dt={dt}  exp {expected}")

# m=3, n odd → A(6i+12, 1)
print("\n  m=3, n odd: A(3, 2i+1) -> A(6i+12, 1)")
for i in range(0, 8):
    n = 2*i + 1
    res, dt = sim.run_macro_step(3, n)
    expected = ("A", 6*i + 12, 1)
    print(f"    i={i} n={n}: {res} dt={dt}  exp {expected}")
