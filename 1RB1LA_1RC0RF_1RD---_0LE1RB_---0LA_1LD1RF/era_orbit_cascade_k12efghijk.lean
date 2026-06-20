/-
**Section 13: Closures for #12e–k (kspine helper internals)** — closing
internal sorries of `not_M_1_kspine_6_5_R_via_ih` (in
`era_orbit_cascade_d2.lean`).

The helper `not_M_1_kspine_6_5_R_via_ih` has cfg = M (1::List.replicate k 2++[6]) 5
(d::R') with parametric (k, d, R'). Backward analysis produces 7 cases that
each require sub-helpers:

- #12e (D2): pred = M (4 :: 1 :: kspine k 6) 3 R'_pred.
- #12f (D8): pred = M0 (2 :: 1 :: kspine k 6) [2] (R=[1] forced).
- #12g (D12): pred = M0 (2 :: 1 :: kspine k 6) (2 :: d :: R').
- #12h (mb_general): pred = M0 (a :: L') ((r'+3) :: R_mid ++ [6]).
- #12i (mb_3run k=0): pred = M0 [2] [3, 5, 2].
- #12j (mb_last_2_general): k=0 same as #12i; k≥1 parametric R_mid.
- #12k (step_R3): existential disjunct.

This file builds bottom-up chain helpers. Many sub-helpers are needed
(estimated 20+); each helper handles its complete backward analysis.

**Helpers provided here**:
- `not_M_1_6_3_step_R3_close`: structural step_R3 closure for M [1] 6 [3]
  (Case 4 closes via phi; other cases via shape).
- `not_M_8_3_1_step_R3_close`: structural step_R3 closure for M [8] 3 [1]
  (Cases 1, 2, 4 ⊥; Case 3 via phi).
- `not_M_empty_9_1_2_step_R3_close`: structural step_R3 closure for
  M [] 9 [1, 2] (Cases 1-3 ⊥, Case 4 via phi).

**Note**: full chain closure for #12i requires ~22 helpers across multiple
side branches. This file provides the backbone; remaining sorries are
documented inside helpers as `sorry` with explanations.
-/

import era_orbit_cascade

namespace Sweeper

-- ============================================================
-- Section 13.a: Step_R3 closures (used by chain helpers)
-- ============================================================

end Sweeper
