import BusyLean
import BusyLean.EsTactic
import machine

open BusyLean

namespace Mxdys

set_option maxHeartbeats 3200000
set_option maxRecDepth 8192

theorem Inc2_es (a b : Nat) : S2 (1 + a) b -[tm]->* S2 a (3 + b) := by
  unfold S2
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  evstep_follow (zebra_traverse_ev b (ones 2 ++ ones (2 * a)) [true])
  es tm [cd_pair_retreat_ev (b + 1) _]

theorem Ov3_es (b : Nat) : S3 0 b -[tm]->* S1 0 2 (2 + b) := by
  unfold S3 S1
  simp only [show 2 * 0 = 0 from rfl, ones_zero, List.nil_append,
             show 2 * (2 + b) = 4 + 2 * b from by omega, ← ones_append]
  rw [show (zebra b : List Sym) = zebra b ++ [] from by simp]
  evstep_follow (zebra_traverse_ev b [] [])
  es tm [cd_pair_retreat_ev (b + 1) _,
         BEDA_traverse_ev (b + 2) _ _,
         A_shift_ev _ _ _]

theorem S1_to_S2_es (a b : Nat) : S1 (2 + a) b 1 -[tm]->* S2 a (6 + b) := by
  unfold S1 S2
  simp only [show 2 * (2 + a) = 4 + 2 * a from by omega, ← ones_append,
             show 2 * 1 = 2 from rfl]
  rw [show (ones 2 ++ [false, true] : List Sym) = [true, true, false, true] from rfl]
  evstep_follow (zebra_traverse_ev b (ones 4 ++ ones (2 * a)) [true, true, false, true])
  es tm [cd_pair_retreat_ev _ _,
         BEDA_traverse_ev _ _ _,
         A_shift_ev _ _ _]

theorem Ov2_raw_es (b : Nat) :
    (S2 0 b : Config 6) -[tm]->*
    { state := some stC, left := ones (4 + 2 * b), head := true,
      right := [false, true, false] } := by
  unfold S2
  simp only [show 2 * 0 = 0 from rfl, ones_zero, List.nil_append]
  evstep_follow (zebra_traverse_ev b [] [true])
  es tm [cd_pair_retreat_ev (b + 1) _,
         BEDA_traverse_ev (b + 2) _ _,
         A_shift_ev _ _ _]

theorem Inc3_absorb_es (a b : Nat) :
    ({ state := some stC, left := ones (2 * (1 + a)), head := true,
       right := zebra b ++ [false] } : Config 6) -[tm]->* S3 a (2 + b) := by
  unfold S3
  simp only [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  evstep_follow (zebra_traverse_ev b (ones 2 ++ ones (2 * a)) [false])
  es tm [cd_pair_retreat_ev (b + 1) _]

end Mxdys
