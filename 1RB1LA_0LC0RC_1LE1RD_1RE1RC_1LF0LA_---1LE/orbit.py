#!/usr/bin/env python3
"""Follow macro rules from blank tape."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from sim import setup_A, run_macro_step, Tape, STATE_NAMES, detect_A_config

# Initial: find first A-config from blank.
t = Tape()
for _ in range(1000):
    if t.halted:
        break
    cfg = detect_A_config(t)
    if cfg is not None and t.steps > 0:
        print(f"Initial A({cfg[0]}, {cfg[1]}) at step {t.steps}")
        break
    t.step()

m, n = 2, 0
total = 0
N = int(sys.argv[1]) if len(sys.argv) > 1 else 80
print(f"{'i':>3} {'m':>10} {'n':>10} {'dt':>12}")
for i in range(N):
    print(f"{i:>3} {m:>10} {n:>10} {'':>12}")
    res, dt = run_macro_step(m, n, step_limit=50_000_000)
    total += dt
    if res[0] != "A":
        print(f"-- {res} at macro step {i}, total steps {total}")
        break
    m, n = res[1], res[2]
print(f"total: {total}")
