/-!
# Abandoned C1Inv / SafeRight approach for TM 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

This file contains the step-level C1Inv / SafeRight invariant approach
to proving C,1 is unreachable. It was abandoned because:

1. SafeRight(false :: false :: _) = True unconditionally, which loses
   information about deeper tape structure
2. The E,1→A case requires SafeRight(E.right), which depends on D.right
   when D reads 0. When D reads 0 via the BCD chain (degenerate run),
   the invariant cannot propagate SafeRight through the unconditional True.
3. The C1Inv_ext approach (adding F-joint condition) also has a sorry
   at B,1→F due to the same fundamental coupling issue.

The macro-level AllGe1 invariant approach (in machine.lean) is the
correct path: it prevents degenerate runs entirely, making C,1 impossible
and HALT pattern impossible.
-/

import BusyLean
import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Basic

open BusyLean

namespace Sweeper

-- Assumes sweeper, stA..stF, sw_* lemmas from machine.lean
-- This file is NOT importable; it's an archive of abandoned work.

/-! ### SafeRight predicate and C1Inv approach

Period-3 recursive predicate on B.right. Ensures C always reads 0
through arbitrary depth of B→C→D chain recursion:
- B reads 0, C reads R[0]. Must be false.
- C,0→1RD: D reads R[1].
  - D reads 0: BCD extension at right edge. Safe.
  - D reads 1: D,1→1RB. New B reads R[2].
    - B reads 1: goes to F. Safe.
    - B reads 0: enters C again. Recurse on R[3:].

### A-condition

At A,0→B: B.head = listHead(A.right), B.right = listTail(A.right).
If B reads 1 (listHead A.right = true), B→F (safe, no C entry).
If B reads 0, we need SafeRight(B.right) = SafeRight(listTail A.right).

So the A-condition is: A reads 0 → either B will read 1 (safe) or
B's right tape satisfies SafeRight. -/

/-- SafeRight: period-3 recursive predicate on B.right tape.
    Ensures C always reads 0 through arbitrary B→C→D chain depth. -/
def SafeRight : List Sym → Prop
  | [] => True
  | true :: _ => False
  | false :: [] => True
  | false :: false :: _ => True
  | false :: true :: [] => True
  | false :: true :: true :: _ => True
  | false :: true :: false :: rest => SafeRight rest

def SafeRight1 : List Sym → Prop
  | [] => True
  | false :: _ => True
  | true :: [] => True
  | true :: true :: _ => True
  | true :: false :: rest => SafeRight rest

def SafeRight2 : List Sym → Prop
  | [] => True
  | true :: _ => True
  | false :: rest => SafeRight rest

/-!
### Why this approach fails

The fundamental issue is that `SafeRight(false :: false :: _) = True`
unconditionally (line 305 of the original). This means after D reads 0
via the BCD chain (B.right = false :: false :: rest'), we know
SafeRight(B.right) = True but cannot deduce SafeRight(rest').

When E,1→A needs SafeRight(E.right):
- E.right = false :: D.right (from D,0→E writing false)
- D.right = rest' (from BCD chain processing)
- SafeRight(false :: rest') may need SafeRight(rest'')
  for rest' = true :: false :: rest''
- But SafeRight(B.right) = SafeRight(false :: false :: true :: false :: rest'') = True
  tells us nothing about SafeRight(rest'')

The macro-level AllGe1 invariant avoids this entirely: it prevents
degenerate runs (run of length 0), so D never reads 0 in the BCD chain.
D,0 only occurs via F,0→D during right-edge bounces, where E.right is
always [false, true] — trivially SafeRight.
-/

end Sweeper
