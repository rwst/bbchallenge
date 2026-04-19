#!/usr/bin/env python3
"""Trace tape shape during a specific macro cycle, to understand micro dynamics."""

from sim import Tape


def run_between(z0, m0, max_steps=100000):
    """Run until first C-macro match, then keep going and record every step."""
    from sim3 import extract_C_macro
    t = Tape()
    snapshot = None
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            return
        if t.state == 'C' and t.pos == t.minpos:
            mc = extract_C_macro(t)
            if mc is not None and mc == (z0, m0):
                snapshot = (step+1, z0, m0, t.length())
                print(f"Found C({z0},{m0}) at step {step+1}")
                break
    if snapshot is None:
        print(f"Not found")
        return

    # Now trace until next C-macro match
    print(f"{'step':>6}  {'pos':>5}  {'len':>5}  st  tape")
    for k in range(600):
        l_str = ''.join(str(s) for s in t.left[-40:])
        r_str = ''.join(str(s) for s in t.right[:40])
        print(f"{snapshot[0]+k:6d}  {t.pos:+5d}  {t.length():5d}  {t.state}  {l_str}[{t.state}]{r_str}")
        ok = t.step()
        if not ok:
            print("HALT"); return
        if t.state == 'C' and t.pos == t.minpos:
            from sim3 import extract_C_macro
            mc = extract_C_macro(t)
            if mc is not None:
                z, m = mc
                l_str = ''.join(str(s) for s in t.left[-40:])
                r_str = ''.join(str(s) for s in t.right[:40])
                print(f"{snapshot[0]+k+1:6d}  {t.pos:+5d}  {t.length():5d}  {t.state}  {l_str}[{t.state}]{r_str}")
                print(f"Next macro: C({z},{m}) at step {snapshot[0]+k+1}")
                return


if __name__ == '__main__':
    import sys
    z = int(sys.argv[1]) if len(sys.argv) > 1 else 2
    m = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    run_between(z, m)
