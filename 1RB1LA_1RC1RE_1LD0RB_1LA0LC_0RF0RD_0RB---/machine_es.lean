import BusyLean
import BusyLean.EsTactic
import machine

open BusyLean

namespace Mxdys

set_option maxHeartbeats 3200000
set_option maxRecDepth 8192

-- Inc2: use have + exact to prevent sorry-based auto-completion
theorem Inc2_es (a b : Nat) : S2 (1 + a) b -[tm]->* S2 a (3 + b) := by
  unfold S2
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  have h1 := zebra_traverse_ev b (ones 2 ++ ones (2 * a)) [true]
  -- h1 : {C, ones 2 ++ ones(2a), true, zebra(b) ++ [true]} →* {C, rev_zebra(b) ++ ..., true, [true]}
  -- Now prove the second half separately:
  have h2 : ({ state := some stC, left := rev_zebra b ++ (ones 2 ++ ones (2 * a)),
               head := true, right := [true] } : Config 6) -[tm]->*
            { state := some stC, left := ones (2 * a), head := true,
              right := zebra (3 + b) ++ [true] } := by
    es tm [cd_pair_retreat_ev (b + 1) _]
  exact EvStep.trans h1 h2

end Mxdys
