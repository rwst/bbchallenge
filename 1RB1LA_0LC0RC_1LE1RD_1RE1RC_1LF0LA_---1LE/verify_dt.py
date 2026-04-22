#!/usr/bin/env python3
"""Verify proposed step-count formulas."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import run_macro_step

# (0, n+1) -> (2, n): dt = 5
print("Rule R1: A(0, n+1) -> A(2, n), dt=5")
for n in range(0, 7):
    res, dt = run_macro_step(0, n + 1)
    assert res == ("A", 2, n), f"R1 fail at n={n}: {res}"
    assert dt == 5, f"R1 dt fail at n={n}: {dt}"
print("  PASS (n = 0..6)")

# (2m+2, n) -> (3m+n+2, 2): dt = 6m² + 17m + 7 + 4mn + 7n
print("Rule R2: A(2m+2, n) -> A(3m+n+2, 2), dt = 6m² + 17m + 7 + 4mn + 7n")
# Valid for m ≥ 0 and n ≥ 0.  n=0 means head=E on blank with 1^(2m+2) to left.
for m in range(0, 8):
    for n in range(0, 8):
        res, dt = run_macro_step(2*m + 2, n)
        exp = ("A", 3*m + n + 2, 2)
        exp_dt = 6*m*m + 17*m + 7 + 4*m*n + 7*n
        ok = res == exp and dt == exp_dt
        if not ok:
            print(f"  FAIL m={m} n={n}: got {res} dt={dt}, expected {exp} dt={exp_dt}")
print("  checked m=0..7, n=0..7")

# (2m+3, n) -> (m, m+n+4): dt = 2m² + 11m + 16
print("Rule R3: A(2m+3, n) -> A(m, m+n+4), dt = 2m² + 11m + 16  (indep. of n)")
for m in range(0, 8):
    for n in range(0, 8):
        res, dt = run_macro_step(2*m + 3, n)
        exp = ("A", m, m + n + 4)
        exp_dt = 2*m*m + 11*m + 16
        ok = res == exp and dt == exp_dt
        if not ok:
            print(f"  FAIL m={m} n={n}: got {res} dt={dt}, expected {exp} dt={exp_dt}")
print("  checked m=0..7, n=0..7")

# Initial config: from blank tape, reaches A(2, 0) at step 4.
print("\nInitial config: blank tape -> A(2, 0) in 4 steps")
from sim import Tape, detect_A_config
t = Tape()
for k in range(200):
    cfg = detect_A_config(t)
    if cfg is not None and k > 0:
        print(f"  step {k}: A({cfg[0]}, {cfg[1]})")
        break
    t.step()

# Halt cases: A(0, 0), A(1, 0), A(1, n) for various n
print("\nHalt cases (wiki claims):")
print("  A(0, 0) -> halt:")
res, dt = run_macro_step(0, 0)
print(f"    dt={dt}, res={res}")
print("  A(1, n) -> halt for various n:")
for n in range(0, 5):
    res, dt = run_macro_step(1, n)
    print(f"    n={n}: dt={dt}, res={res}")
