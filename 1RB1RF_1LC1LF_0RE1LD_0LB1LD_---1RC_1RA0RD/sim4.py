#!/usr/bin/env python3
"""Detailed rule-extraction: classify (z,m) -> (z',m') transitions."""

from sim import Tape
from sim3 import extract_C_macro, run_extract


def analyze(events):
    """Classify transitions: diff z, diff m, dt."""
    print(f"{'step':>8}  {'z':>4}  {'m':>5}  {'2z+m':>5}  {'Δstep':>7}  {'Δz':>4}  {'Δm':>5}  par  rule")
    prev_step, prev_z, prev_m = events[0][:3]
    print(f"{prev_step:8d}  {prev_z:4d}  {prev_m:5d}  {2*prev_z+prev_m:5d}  {'':>7}  {'':>4}  {'':>5}  {'e' if prev_m%2==0 else 'o'}  INIT")
    for i in range(1, len(events)):
        step, z, m, L = events[i]
        dt = step - prev_step
        dz = z - prev_z
        dm = m - prev_m
        par = 'e' if m % 2 == 0 else 'o'
        prev_par = 'e' if prev_m % 2 == 0 else 'o'
        flip = '*' if par != prev_par else ' '
        # Classify
        if dz == z - prev_z and dm == -2*prev_z + 2:
            rule = f"DBL (z'=2z: m' = m-2z+2)"
        elif dz == 2:
            rule = f"+2,Δm={dm}"
        else:
            rule = f"dz={dz},dm={dm}"
        print(f"{step:8d}  {z:4d}  {m:5d}  {2*z+m:5d}  {dt:7d}  {dz:+4d}  {dm:+5d}  {par}{flip}  {rule}")
        prev_step, prev_z, prev_m = step, z, m


if __name__ == '__main__':
    import sys
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 500000
    events, steps, halted = run_extract(n)
    print(f"Ran {steps} steps, events={len(events)}, halted={halted}")
    analyze(events)
