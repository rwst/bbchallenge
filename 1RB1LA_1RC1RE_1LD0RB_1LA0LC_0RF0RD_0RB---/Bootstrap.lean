import BusyLean
import machine

/-!
# Nonhalting via progress invariant: `ValidS`, `bootstrap`, `tm_not_halts`

This module contains the final stage of the BB(6) holdout nonhalting proof for
TM `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`:

1. `ValidS n i` — predicate saying `S'(n)` is a "valid" macro state at level
   `i ≥ 50`, meaning `n` falls in the R1 or R2 window for that level.
2. `ValidS_progress` — every valid state progresses (in `k > 0` concrete TM
   steps) to another valid state. Core mathematical content: uses
   `Hensel.pomme_main` to argue about parity/2-adic valuation of
   `N i = 2·3^i + i + 5`.
3. `bootstrap` — `S'(18)` reaches a valid state in finitely many steps.
   Purely computational: builds an explicit chain of `BigStep0`/`BigStep1`
   applications from level 2 up through level ≥ 50.
4. `tm_not_halts` — the main theorem, combining `init` (715 steps from the
   blank tape to `S'(18)`), `bootstrap`, and `nonhalt_of_progress` over
   `ValidS_progress`.

Everything depends on the atomic rules `BigStep0`, `BigStep1`, and the
recurrence `P_n` proved in `machine.lean`.
-/

open BusyLean

namespace Mxdys

/-- A macro state `S'(n)` is valid if `n` falls in the R1 or R2 window for some
    level `i ≥ 50`. -/
def ValidS (n i : Nat) : Prop :=
  50 ≤ i ∧
  ((n % 2 = i % 2 ∧ 3 ^ i * 2 - i - 2 ≤ n ∧ n ≤ 3 ^ i * 6 - i - 6) ∨
   (n % 2 = (i + 1) % 2 ∧ 3 ^ i * 2 - i ≤ n ∧ n ≤ 3 ^ i * 6 - i - 10))

/-- Every valid state progresses (in a positive number of TM steps) to another
    valid state. Uses `BigStep0`/`BigStep1` + `pomme_main`.

    Returns an explicit step count `k > 0` rather than an `EvStep` existential
    so callers (notably `tm_not_halts`) can chain via `run_add` without losing
    the strict-progress witness. -/
theorem ValidS_progress (n i : Nat) (hv : ValidS n i) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧ run tm (S' n) k = S' n' := by
  sorry -- case split on R1 vs R2; closure uses pomme_main

/-! #### Bootstrap chain helpers

`chain_step_B0` and `chain_step_B1` specialise `BigStep0` / `BigStep1` to the
`P_n i` instance, yielding a one-line step `S' (prev) -[tm]->* S' (next)`
after plugging in concrete `(i, c)`. -/

/-- `BigStep0` specialised to `P_n i`. Given `c ≤ 3^i·2 - 2`, advances
    `S' ((3^i·2 - i - 2) + 2c)` to `S' (5 + 2·(3^i·2 - 2 - c) + 3c)`. -/
theorem chain_step_B0 (i c : Nat) (hc : c ≤ 3^i * 2 - 2) :
    S' ((3^i * 2 - i - 2) + c * 2) -[tm]->* S' (5 + (3^i * 2 - 2 - c) * 2 + c * 3) := by
  have hP := P_n i
  have heq : (3 : Nat)^i * 2 - 2 = c + (3^i * 2 - 2 - c) := by omega
  rw [heq] at hP
  exact BigStep0 _ _ _ hP

/-- `BigStep1` specialised to `P_n i`. Given `c + 2 ≤ 3^i·2 - 2`, advances
    `S' ((3^i·2 - i - 2) + 2c + 1)` to `S' (23 + 6·(3^i·2 - 2 - c - 2) + 6c)`. -/
theorem chain_step_B1 (i c : Nat) (hc : c + 2 ≤ 3^i * 2 - 2) :
    S' ((3^i * 2 - i - 2) + c * 2 + 1) -[tm]->*
    S' (23 + (3^i * 2 - 2 - c - 2) * 6 + c * 6) := by
  have hP := P_n i
  have heq : (3 : Nat)^i * 2 - 2 = c + (2 + (3^i * 2 - 2 - c - 2)) := by omega
  rw [heq] at hP
  exact BigStep1 _ _ _ hP

/-- `S'(18)` reaches the valid state `S'(2871591950767410355080995)` at level 50.

    This is a finite computation — 97 applications of `BigStep0`/`BigStep1`
    picking the largest feasible level `i` at each step. Each step reduces to
    `simpa using chain_step_B{0,1} i c (by decide)` where `(i, c)` are
    precomputed. The level sequence climbs from 2 up to 50 as the macro value
    grows from 18 to ~2.87 × 10²⁴.

    The chosen endpoint sits in the R2 window of level 50. -/
theorem bootstrap : ∃ n i k, ValidS n i ∧ run tm (S' 18) k = S' n := by
  -- 97 chain steps from S' 18 to S' 2871591950767410355080995
  have h18 : S' 18 -[tm]->* S' 39 := by
    simpa using chain_step_B0 2 2 (by decide)
  have h39 : S' 39 -[tm]->* S' 107 := by
    simpa using chain_step_B1 2 12 (by decide)
  have h107 : S' 107 -[tm]->* S' 138 := by
    simpa using chain_step_B0 3 29 (by decide)
  have h138 : S' 138 -[tm]->* S' 323 := by
    simpa using chain_step_B1 3 44 (by decide)
  have h323 : S' 323 -[tm]->* S' 971 := by
    simpa using chain_step_B1 4 83 (by decide)
  have h971 : S' 971 -[tm]->* S' 1219 := by
    simpa using chain_step_B0 5 246 (by decide)
  have h1219 : S' 1219 -[tm]->* S' 1343 := by
    simpa using chain_step_B0 5 370 (by decide)
  have h1343 : S' 1343 -[tm]->* S' 1405 := by
    simpa using chain_step_B0 5 432 (by decide)
  have h1405 : S' 1405 -[tm]->* S' 1436 := by
    simpa using chain_step_B0 5 463 (by decide)
  have h1436 : S' 1436 -[tm]->* S' 2915 := by
    simpa using chain_step_B1 5 478 (by decide)
  have h2915 : S' 2915 -[tm]->* S' 8747 := by
    simpa using chain_step_B1 6 732 (by decide)
  have h8747 : S' 8747 -[tm]->* S' 10940 := by
    simpa using chain_step_B0 7 2191 (by decide)
  have h10940 : S' 10940 -[tm]->* S' 26243 := by
    simpa using chain_step_B1 7 3287 (by decide)
  have h26243 : S' 26243 -[tm]->* S' 78731 := by
    simpa using chain_step_B1 8 6565 (by decide)
  have h78731 : S' 78731 -[tm]->* S' 98421 := by
    simpa using chain_step_B0 9 19688 (by decide)
  have h98421 : S' 98421 -[tm]->* S' 108266 := by
    simpa using chain_step_B0 9 29533 (by decide)
  have h108266 : S' 108266 -[tm]->* S' 236195 := by
    simpa using chain_step_B1 9 34455 (by decide)
  have h236195 : S' 236195 -[tm]->* S' 708587 := by
    simpa using chain_step_B1 10 59054 (by decide)
  have h708587 : S' 708587 -[tm]->* S' 885742 := by
    simpa using chain_step_B0 11 177153 (by decide)
  have h885742 : S' 885742 -[tm]->* S' 2125763 := by
    simpa using chain_step_B1 11 265730 (by decide)
  have h2125763 : S' 2125763 -[tm]->* S' 6377291 := by
    simpa using chain_step_B1 12 531447 (by decide)
  have h6377291 : S' 6377291 -[tm]->* S' 7971623 := by
    simpa using chain_step_B0 13 1594330 (by decide)
  have h7971623 : S' 7971623 -[tm]->* S' 8768789 := by
    simpa using chain_step_B0 13 2391496 (by decide)
  have h8768789 : S' 8768789 -[tm]->* S' 9167372 := by
    simpa using chain_step_B0 13 2790079 (by decide)
  have h9167372 : S' 9167372 -[tm]->* S' 19131875 := by
    simpa using chain_step_B1 13 2989370 (by decide)
  have h19131875 : S' 19131875 -[tm]->* S' 57395627 := by
    simpa using chain_step_B1 14 4782976 (by decide)
  have h57395627 : S' 57395627 -[tm]->* S' 71744544 := by
    simpa using chain_step_B0 15 14348915 (by decide)
  have h71744544 : S' 71744544 -[tm]->* S' 172186883 := by
    simpa using chain_step_B1 15 21523373 (by decide)
  have h172186883 : S' 172186883 -[tm]->* S' 516560651 := by
    simpa using chain_step_B1 16 43046729 (by decide)
  have h516560651 : S' 516560651 -[tm]->* S' 645700825 := by
    simpa using chain_step_B0 17 129140172 (by decide)
  have h645700825 : S' 645700825 -[tm]->* S' 710270912 := by
    simpa using chain_step_B0 17 193710259 (by decide)
  have h710270912 : S' 710270912 -[tm]->* S' 1549681955 := by
    simpa using chain_step_B1 17 225995302 (by decide)
  have h1549681955 : S' 1549681955 -[tm]->* S' 4649045867 := by
    simpa using chain_step_B1 18 387420498 (by decide)
  have h4649045867 : S' 4649045867 -[tm]->* S' 5811307346 := by
    simpa using chain_step_B0 19 1162261477 (by decide)
  have h5811307346 : S' 5811307346 -[tm]->* S' 13947137603 := by
    simpa using chain_step_B1 19 1743392216 (by decide)
  have h13947137603 : S' 13947137603 -[tm]->* S' 41841412811 := by
    simpa using chain_step_B1 20 3486784411 (by decide)
  have h41841412811 : S' 41841412811 -[tm]->* S' 52301766027 := by
    simpa using chain_step_B0 21 10460353214 (by decide)
  have h52301766027 : S' 52301766027 -[tm]->* S' 57531942635 := by
    simpa using chain_step_B0 21 15690529822 (by decide)
  have h57531942635 : S' 57531942635 -[tm]->* S' 60147030939 := by
    simpa using chain_step_B0 21 18305618126 (by decide)
  have h60147030939 : S' 60147030939 -[tm]->* S' 61454575091 := by
    simpa using chain_step_B0 21 19613162278 (by decide)
  have h61454575091 : S' 61454575091 -[tm]->* S' 62108347167 := by
    simpa using chain_step_B0 21 20266934354 (by decide)
  have h62108347167 : S' 62108347167 -[tm]->* S' 62435233205 := by
    simpa using chain_step_B0 21 20593820392 (by decide)
  have h62435233205 : S' 62435233205 -[tm]->* S' 62598676224 := by
    simpa using chain_step_B0 21 20757263411 (by decide)
  have h62598676224 : S' 62598676224 -[tm]->* S' 125524238435 := by
    simpa using chain_step_B1 21 20838984920 (by decide)
  have h125524238435 : S' 125524238435 -[tm]->* S' 376572715307 := by
    simpa using chain_step_B1 22 31381059620 (by decide)
  have h376572715307 : S' 376572715307 -[tm]->* S' 470715894148 := by
    simpa using chain_step_B0 23 94143178839 (by decide)
  have h470715894148 : S' 470715894148 -[tm]->* S' 1129718145923 := by
    simpa using chain_step_B1 23 141214768259 (by decide)
  have h1129718145923 : S' 1129718145923 -[tm]->* S' 3389154437771 := by
    simpa using chain_step_B1 24 282429536493 (by decide)
  have h3389154437771 : S' 3389154437771 -[tm]->* S' 4236443047229 := by
    simpa using chain_step_B0 25 847288609456 (by decide)
  have h4236443047229 : S' 4236443047229 -[tm]->* S' 4660087351958 := by
    simpa using chain_step_B0 25 1270932914185 (by decide)
  have h4660087351958 : S' 4660087351958 -[tm]->* S' 10167463313315 := by
    simpa using chain_step_B1 25 1482755066549 (by decide)
  have h10167463313315 : S' 10167463313315 -[tm]->* S' 30502389939947 := by
    simpa using chain_step_B1 26 2541865828342 (by decide)
  have h30502389939947 : S' 30502389939947 -[tm]->* S' 38127987424950 := by
    simpa using chain_step_B0 27 7625597485001 (by decide)
  have h38127987424950 : S' 38127987424950 -[tm]->* S' 91507169819843 := by
    simpa using chain_step_B1 27 11438396227502 (by decide)
  have h91507169819843 : S' 91507169819843 -[tm]->* S' 274521509459531 := by
    simpa using chain_step_B1 28 22876792454975 (by decide)
  have h274521509459531 : S' 274521509459531 -[tm]->* S' 343151886824431 := by
    simpa using chain_step_B0 29 68630377364898 (by decide)
  have h343151886824431 : S' 343151886824431 -[tm]->* S' 377467075506881 := by
    simpa using chain_step_B0 29 102945566047348 (by decide)
  have h377467075506881 : S' 377467075506881 -[tm]->* S' 394624669848106 := by
    simpa using chain_step_B0 29 120103160388573 (by decide)
  have h394624669848106 : S' 394624669848106 -[tm]->* S' 823564528378595 := by
    simpa using chain_step_B1 29 128681957559185 (by decide)
  have h823564528378595 : S' 823564528378595 -[tm]->* S' 2470693585135787 := by
    simpa using chain_step_B1 30 205891132094664 (by decide)
  have h2470693585135787 : S' 2470693585135787 -[tm]->* S' 3088366981419752 := by
    simpa using chain_step_B0 31 617673396283963 (by decide)
  have h3088366981419752 : S' 3088366981419752 -[tm]->* S' 7412080755407363 := by
    simpa using chain_step_B1 31 926510094425945 (by decide)
  have h7412080755407363 : S' 7412080755407363 -[tm]->* S' 22236242266222091 := by
    simpa using chain_step_B1 32 1853020188851857 (by decide)
  have h22236242266222091 : S' 22236242266222091 -[tm]->* S' 27795302832777633 := by
    simpa using chain_step_B0 33 5559060566555540 (by decide)
  have h27795302832777633 : S' 27795302832777633 -[tm]->* S' 30574833116055404 := by
    simpa using chain_step_B0 33 8338590849833311 (by decide)
  have h30574833116055404 : S' 30574833116055404 -[tm]->* S' 66708726798666275 := by
    simpa using chain_step_B1 33 9728355991472196 (by decide)
  have h66708726798666275 : S' 66708726798666275 -[tm]->* S' 200126180395998827 := by
    simpa using chain_step_B1 34 16677181699666586 (by decide)
  have h200126180395998827 : S' 200126180395998827 -[tm]->* S' 250157725494998554 := by
    simpa using chain_step_B0 35 50031545098999725 (by decide)
  have h250157725494998554 : S' 250157725494998554 -[tm]->* S' 600378541187996483 := by
    simpa using chain_step_B1 35 75047317648499588 (by decide)
  have h600378541187996483 : S' 600378541187996483 -[tm]->* S' 1801135623563989451 := by
    simpa using chain_step_B1 36 150094635296999139 (by decide)
  have h1801135623563989451 : S' 1801135623563989451 -[tm]->* S' 2251419529454986835 := by
    simpa using chain_step_B0 37 450283905890997382 (by decide)
  have h2251419529454986835 : S' 2251419529454986835 -[tm]->* S' 2476561482400485527 := by
    simpa using chain_step_B0 37 675425858836496074 (by decide)
  have h2476561482400485527 : S' 2476561482400485527 -[tm]->* S' 2589132458873234873 := by
    simpa using chain_step_B0 37 787996835309245420 (by decide)
  have h2589132458873234873 : S' 2589132458873234873 -[tm]->* S' 2645417947109609546 := by
    simpa using chain_step_B0 37 844282323545620093 (by decide)
  have h2645417947109609546 : S' 2645417947109609546 -[tm]->* S' 5403406870691968355 := by
    simpa using chain_step_B1 37 872425067663807429 (by decide)
  have h5403406870691968355 : S' 5403406870691968355 -[tm]->* S' 16210220612075905067 := by
    simpa using chain_step_B1 38 1350851717672992108 (by decide)
  have h16210220612075905067 : S' 16210220612075905067 -[tm]->* S' 20262775765094881356 := by
    simpa using chain_step_B0 39 4052555153018976287 (by decide)
  have h20262775765094881356 : S' 20262775765094881356 -[tm]->* S' 48630661836227715203 := by
    simpa using chain_step_B1 39 6078832729528464431 (by decide)
  have h48630661836227715203 : S' 48630661836227715203 -[tm]->* S' 145891985508683145611 := by
    simpa using chain_step_B1 40 12157665459056928821 (by decide)
  have h145891985508683145611 : S' 145891985508683145611 -[tm]->* S' 182364981885853932037 := by
    simpa using chain_step_B0 41 36472996377170786424 (by decide)
  have h182364981885853932037 : S' 182364981885853932037 -[tm]->* S' 200601480074439325250 := by
    simpa using chain_step_B0 41 54709494565756179637 (by decide)
  have h200601480074439325250 : S' 200601480074439325250 -[tm]->* S' 437675956526049436835 := by
    simpa using chain_step_B1 41 63827743660048876243 (by decide)
  have h437675956526049436835 : S' 437675956526049436835 -[tm]->* S' 1313027869578148310507 := by
    simpa using chain_step_B1 42 109418989131512359230 (by decide)
  have h1313027869578148310507 : S' 1313027869578148310507 -[tm]->* S' 1641284836972685388158 := by
    simpa using chain_step_B0 43 328256967394537077649 (by decide)
  have h1641284836972685388158 : S' 1641284836972685388158 -[tm]->* S' 3939083608734444931523 := by
    simpa using chain_step_B1 43 492385451091805616474 (by decide)
  have h3939083608734444931523 : S' 3939083608734444931523 -[tm]->* S' 11817250826203334794571 := by
    simpa using chain_step_B1 44 984770902183611232903 (by decide)
  have h11817250826203334794571 : S' 11817250826203334794571 -[tm]->* S' 14771563532754168493239 := by
    simpa using chain_step_B0 45 2954312706550833698666 (by decide)
  have h14771563532754168493239 : S' 14771563532754168493239 -[tm]->* S' 16248719886029585342573 := by
    simpa using chain_step_B0 45 4431469059826250548000 (by decide)
  have h16248719886029585342573 : S' 16248719886029585342573 -[tm]->* S' 16987298062667293767240 := by
    simpa using chain_step_B0 45 5170047236463958972667 (by decide)
  have h16987298062667293767240 : S' 16987298062667293767240 -[tm]->* S' 35451752478610004383715 := by
    simpa using chain_step_B1 45 5539336324782813185000 (by decide)
  have h35451752478610004383715 :
      S' 35451752478610004383715 -[tm]->* S' 106355257435830013151147 := by
    simpa using chain_step_B1 46 8862938119652501095952 (by decide)
  have h106355257435830013151147 :
      S' 106355257435830013151147 -[tm]->* S' 132944071794787516438960 := by
    simpa using chain_step_B0 47 26588814358957503287811 (by decide)
  have h132944071794787516438960 :
      S' 132944071794787516438960 -[tm]->* S' 319065772307490039453443 := by
    simpa using chain_step_B1 47 39883221538436254931717 (by decide)
  have h319065772307490039453443 :
      S' 319065772307490039453443 -[tm]->* S' 957197316922470118360331 := by
    simpa using chain_step_B1 48 79766443076872509863385 (by decide)
  have h957197316922470118360331 :
      S' 957197316922470118360331 -[tm]->* S' 1196496646153087647950441 := by
    simpa using chain_step_B0 49 239299329230617529590108 (by decide)
  have h1196496646153087647950441 :
      S' 1196496646153087647950441 -[tm]->* S' 1316146310768396412745496 := by
    simpa using chain_step_B0 49 358948993845926294385163 (by decide)
  have h1316146310768396412745496 :
      S' 1316146310768396412745496 -[tm]->* S' 2871591950767410355080995 := by
    simpa using chain_step_B1 49 418773826153580676782690 (by decide)
  -- Chain all 97 steps via `.trans`
  have chain : S' 18 -[tm]->* S' 2871591950767410355080995 :=
    h18.trans <| h39.trans <| h107.trans <| h138.trans <| h323.trans <| h971.trans <|
    h1219.trans <| h1343.trans <| h1405.trans <| h1436.trans <| h2915.trans <|
    h8747.trans <| h10940.trans <| h26243.trans <| h78731.trans <| h98421.trans <|
    h108266.trans <| h236195.trans <| h708587.trans <| h885742.trans <| h2125763.trans <|
    h6377291.trans <| h7971623.trans <| h8768789.trans <| h9167372.trans <|
    h19131875.trans <| h57395627.trans <| h71744544.trans <| h172186883.trans <|
    h516560651.trans <| h645700825.trans <| h710270912.trans <| h1549681955.trans <|
    h4649045867.trans <| h5811307346.trans <| h13947137603.trans <| h41841412811.trans <|
    h52301766027.trans <| h57531942635.trans <| h60147030939.trans <| h61454575091.trans <|
    h62108347167.trans <| h62435233205.trans <| h62598676224.trans <| h125524238435.trans <|
    h376572715307.trans <| h470715894148.trans <| h1129718145923.trans <|
    h3389154437771.trans <| h4236443047229.trans <| h4660087351958.trans <|
    h10167463313315.trans <| h30502389939947.trans <| h38127987424950.trans <|
    h91507169819843.trans <| h274521509459531.trans <| h343151886824431.trans <|
    h377467075506881.trans <| h394624669848106.trans <| h823564528378595.trans <|
    h2470693585135787.trans <| h3088366981419752.trans <| h7412080755407363.trans <|
    h22236242266222091.trans <| h27795302832777633.trans <| h30574833116055404.trans <|
    h66708726798666275.trans <| h200126180395998827.trans <| h250157725494998554.trans <|
    h600378541187996483.trans <| h1801135623563989451.trans <| h2251419529454986835.trans <|
    h2476561482400485527.trans <| h2589132458873234873.trans <| h2645417947109609546.trans <|
    h5403406870691968355.trans <| h16210220612075905067.trans <|
    h20262775765094881356.trans <| h48630661836227715203.trans <|
    h145891985508683145611.trans <| h182364981885853932037.trans <|
    h200601480074439325250.trans <| h437675956526049436835.trans <|
    h1313027869578148310507.trans <| h1641284836972685388158.trans <|
    h3939083608734444931523.trans <| h11817250826203334794571.trans <|
    h14771563532754168493239.trans <| h16248719886029585342573.trans <|
    h16987298062667293767240.trans <| h35451752478610004383715.trans <|
    h106355257435830013151147.trans <| h132944071794787516438960.trans <|
    h319065772307490039453443.trans <| h957197316922470118360331.trans <|
    h1196496646153087647950441.trans h1316146310768396412745496
  obtain ⟨k, hk⟩ := chain
  refine ⟨2871591950767410355080995, 50, k, ?_, hk⟩
  -- ValidS at level 50: hits the R2 window
  refine ⟨by decide, Or.inr ⟨?_, ?_, ?_⟩⟩ <;> decide

/-- `S'(n)` has `state = some stC ≠ none`. -/
theorem S'_not_halted (n : Nat) : ¬ (S' n).halted := by
  simp [S', S1, Config.halted]

/-- **Main theorem**: the TM never halts.

    Proof structure:
    1. `bootstrap` gives an explicit step count `k_init` such that
       `S' 18 →{k_init} S' n_init` with `n_init` valid.
    2. `init` plus `run_add` lifts to
       `initConfig 6 →{715 + k_init} S' n_init`.
    3. `nonhalt_of_progress` (using `ValidS_progress` + the `Q` predicate)
       shows `S' n_init` never halts.
    4. For any step `m` of `initConfig 6`:
       - If `m ≤ 715 + k_init`: the prefix is alive because its endpoint
         `S' n_init` is alive — apply `run_alive_of_later`.
       - If `m > 715 + k_init`: split off the prefix via `run_add` and
         appeal to step 3. -/
theorem tm_not_halts : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  obtain ⟨n_init, i_init, k_init, hv_init, hk_init⟩ := bootstrap
  have h_reach : run tm (initConfig 6) (715 + k_init) = S' n_init := by
    rw [run_add, init, hk_init]
  let Q : Config 6 → Prop := fun c => ∃ n i, ValidS n i ∧ c = S' n
  have hProg : ∀ c, Q c → ∃ k, 0 < k ∧ Q (run tm c k) ∧ (run tm c k).state ≠ none := by
    rintro c ⟨n, i, hv, rfl⟩
    obtain ⟨n', i', k, hv', hkpos, hk⟩ := ValidS_progress n i hv
    refine ⟨k, hkpos, ⟨n', i', hv', hk⟩, ?_⟩
    rw [hk]; exact S'_not_halted n'
  have hQ : Q (S' n_init) := ⟨n_init, i_init, hv_init, rfl⟩
  have h_safe : ∀ m, (run tm (S' n_init) m).state ≠ none :=
    nonhalt_of_progress tm Q hProg (S' n_init) hQ
  have h_alive_at : (run tm (initConfig 6) (715 + k_init)).state ≠ none := by
    rw [h_reach]; exact S'_not_halted n_init
  intro m hhalt
  by_cases hle : m ≤ 715 + k_init
  · exact run_alive_of_later tm (initConfig 6) m (715 + k_init) hle h_alive_at hhalt
  · have hsplit : m = (715 + k_init) + (m - (715 + k_init)) := by omega
    rw [hsplit, run_add, h_reach] at hhalt
    exact h_safe (m - (715 + k_init)) hhalt

end Mxdys
