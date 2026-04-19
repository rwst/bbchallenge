#!/usr/bin/env python3
"""Simulator for BB(6) candidate TM: 1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD.

Transitions (state, sym) -> (new_sym, dir, new_state):
  A,0 -> 1,R,B     A,1 -> 1,R,F
  B,0 -> 1,L,C     B,1 -> 1,L,F
  C,0 -> 0,R,E     C,1 -> 1,L,D
  D,0 -> 0,L,B     D,1 -> 1,L,D
  E,0 -> halt      E,1 -> 1,R,C
  F,0 -> 1,R,A     F,1 -> 0,R,D
"""

from collections import defaultdict

TM = {
    ('A', 0): (1, 'R', 'B'),
    ('A', 1): (1, 'R', 'F'),
    ('B', 0): (1, 'L', 'C'),
    ('B', 1): (1, 'L', 'F'),
    ('C', 0): (0, 'R', 'E'),
    ('C', 1): (1, 'L', 'D'),
    ('D', 0): (0, 'L', 'B'),
    ('D', 1): (1, 'L', 'D'),
    ('E', 0): None,  # halt
    ('E', 1): (1, 'R', 'C'),
    ('F', 0): (1, 'R', 'A'),
    ('F', 1): (0, 'R', 'D'),
}


class Tape:
    def __init__(self):
        self.left = []    # left of head, highest index = closest to head
        self.right = []   # right of head, index 0 = at head
        self.state = 'A'
        self.pos = 0      # absolute head position (for stats)
        self.minpos = 0
        self.maxpos = 0

    def read(self):
        if not self.right:
            return 0
        return self.right[0]

    def write_move(self, sym, d):
        if not self.right:
            self.right = [0]
        self.right[0] = sym
        if d == 'L':
            left_sym = self.left.pop() if self.left else 0
            self.right.insert(0, left_sym)
            self.pos -= 1
        else:
            self.left.append(self.right.pop(0))
            self.pos += 1
        if self.pos < self.minpos:
            self.minpos = self.pos
        if self.pos > self.maxpos:
            self.maxpos = self.pos

    def step(self):
        sym = self.read()
        tr = TM[(self.state, sym)]
        if tr is None:
            return False
        ns, d, nq = tr
        self.write_move(ns, d)
        self.state = nq
        return True

    def tape_str(self, width=30):
        # build absolute strip around head
        left = self.left[-width:]
        right = self.right[:width]
        l_str = ''.join(str(s) for s in left)
        r_str = ''.join(str(s) for s in right)
        return f"{l_str}[{self.state}]{r_str}"

    def length(self):
        """Number of visited cells."""
        return self.maxpos - self.minpos + 1


def run(max_steps=2000, quiet=False):
    t = Tape()
    head_pos_min = 0
    head_pos_max = 0
    history = []
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            print(f"HALT at step {step}")
            return t, step
        if not quiet and step < 200:
            print(f"{step:4d}: pos={t.pos:+4d} len={t.length():4d} {t.tape_str()}")
        history.append((step, t.pos, t.state))
    return t, max_steps


def find_bounces(max_steps=100000):
    """Find times when head hits the leftmost or rightmost visited cell."""
    t = Tape()
    left_hits = []
    right_hits = []
    for step in range(max_steps):
        # Record extreme positions before stepping
        prev_min = t.minpos
        prev_max = t.maxpos
        ok = t.step()
        if not ok:
            return left_hits, right_hits, step, t
        # Check if we extended the range or hit an extreme
        if t.pos == t.minpos:
            if t.minpos < prev_min:
                left_hits.append((step, t.pos, t.state, 'extend'))
            else:
                left_hits.append((step, t.pos, t.state, 'hit'))
        if t.pos == t.maxpos:
            if t.maxpos > prev_max:
                right_hits.append((step, t.pos, t.state, 'extend'))
            else:
                right_hits.append((step, t.pos, t.state, 'hit'))
    return left_hits, right_hits, max_steps, t


def find_same_state_returns(max_steps=100000, target_state='A', target_pos=0):
    """Find times when head returns to target_pos in target_state."""
    t = Tape()
    events = []
    for step in range(max_steps):
        ok = t.step()
        if not ok:
            return events, step
        if t.state == target_state and t.pos == target_pos:
            events.append((step, t.length(), t.tape_str()))
    return events, max_steps


if __name__ == '__main__':
    import sys
    mode = sys.argv[1] if len(sys.argv) > 1 else 'run'

    if mode == 'run':
        run(max_steps=400, quiet=False)
    elif mode == 'bounces':
        left, right, halted_step, t = find_bounces(200000)
        print(f"Left hits: {len(left)}, Right hits: {len(right)}, final step: {halted_step}")
        print("\nLeft hits (first 50):")
        for s, p, q, k in left[:50]:
            print(f"  step={s:7d} pos={p:+5d} state={q} kind={k}")
        print("\nRight hits (first 50):")
        for s, p, q, k in right[:50]:
            print(f"  step={s:7d} pos={p:+5d} state={q} kind={k}")
    elif mode == 'ret':
        events, s = find_same_state_returns(200000, 'A', 0)
        print(f"Returns to state A at pos=0, total {len(events)}:")
        for st, ln, ts in events[:30]:
            print(f"  step={st:7d} len={ln} tape={ts}")
