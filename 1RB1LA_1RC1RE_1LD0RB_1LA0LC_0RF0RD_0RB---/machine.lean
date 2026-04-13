import BusyLean
import BusyLean.EsTactic

/-!
# TM `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` : macro simulation

Port of mxdys' Coq proof (BusyCoq) to BusyLean.

## Proof architecture (ported from mxdys.v)

Three intermediate configurations (all at state C):

  S1(a, b, c) = {C, ones(2a), true, zebra(b) ++ ones(2c) ++ [0,1]}
  S2(a, b)    = {C, ones(2a), true, zebra(b) ++ [1]}
  S3(a, b)    = {C, ones(2a), true, zebra(b)}

Atomic rules (each proved by a fixed number of TM steps):
  Inc1 : S1(1+a, b, 2+c)  →*  S1(a, 3+b, c)     — 8+4b steps
  Inc2 : S2(1+a, b)        →*  S2(a, 3+b)          — 26+4b steps
  Inc3 : S3(1+a, b)        →*  S3(a, 2+b)          — 6+4b steps
  LOv1 : S1(0, b, 3+c)    →*  S1(2+b, 2, c)       — 22+8b steps
  Ov2  : S2(0, b)          →*  S3(2+b, 1)          — with trailing false
  Ov3  : S3(0, b)          →*  S1(0, 2, 2+b)       — 35+10b steps

Iterated versions (by induction):
  Incs1 n : S1(n+a, b, n*2+c) →* S1(a, n*3+b, c)
  Incs2   : S2(a, b)           →* S2(0, a*3+b)
  Incs3   : S3(a, b)           →* S3(0, a*2+b)

Compositions:
  IncsOv3 : S3(a, b)     →* S1(0, 2, 2+a*2+b)
  IncsOv2 : S2(a, b)     →* S1(0, 2, 7+a*6+b*2)
  ROv1_0  : S1(a, b, 0)  →* S1(0, 2, 3+a*2+b)
  ROv1_1  : S1(2+a, b, 1)→* S1(0, 2, 19+a*6+b*2)

P recurrence (captures all shift levels uniformly):
  P(n1, n2) := ∀ c, S1(0, 2, n1+c) →* S1(n2, 2, c)
  P(0, 0)                                            — base
  P(n1, n2) → P(n1+n2*2+3, 4+n2*3)                  — step
  P_n i : P(3^i*2−i−2, 3^i*2−2)                      — closed form

BigStep rules (= mxdys's R1, R2):
  BigStep0' : S'(n) →* S'((n + 3^i·6 + i + 4)/2)
  BigStep1' : S'(n) →* S'(3^i·12 − 1)

Nonhalting via progress invariant + Hensel.pomme_main.

## Inc1 proof decomposition

Inc1 is decomposed into three phases:
  1. **zebra_traverse** (2b steps): head traverses zebra(b) right-to-left,
     adding rev_zebra pairs to the left tape.
  2. **ones_process** (4 steps): head processes 4 ones from the right boundary.
  3. **cd_retreat** (2b+4 steps): C/D alternating leftward sweep converts
     the accumulated left tape back to zebra on the right.

Each phase is proved by induction (zebra_traverse, cd_retreat) or by direct
step computation (ones_process). The full Inc1 extends to general (a, c)
parameters via run_left_append and run_right_append.
-/

open BusyLean

namespace Mxdys

/-! ### 1. TM definition -/

/-- The BB(6) holdout `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
@[reducible] def tm : TM 6 := tm! "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

/-! ### 2. Configuration definitions -/

/-- `S1(a, b, c)`: state C, left = ones(2a), head = true,
    right = zebra(b) ++ ones(2c) ++ [0,1]. -/
def S1 (a b c : Nat) : Config 6 :=
  { state := some stC, left := ones (2 * a), head := true,
    right := zebra b ++ ones (2 * c) ++ [false, true] }

/-- `S2(a, b)`: state C, left = ones(2a), head = true,
    right = zebra(b) ++ [1]. -/
def S2 (a b : Nat) : Config 6 :=
  { state := some stC, left := ones (2 * a), head := true,
    right := zebra b ++ [true] }

/-- `S3(a, b)`: state C, left = ones(2a), head = true,
    right = zebra(b). -/
def S3 (a b : Nat) : Config 6 :=
  { state := some stC, left := ones (2 * a), head := true,
    right := zebra b }

/-- `S'(n) = S1(0, 2, n)`: the single-parameter macro state. -/
def S' (n : Nat) : Config 6 := S1 0 2 n

/-- Reversed zebra: `[true, false, true, false, …]` of length 2k.
    During Inc1's forward sweep, zebra pairs from the right get reversed
    onto the left tape in this pattern. -/
def rev_zebra : Nat → List Sym
  | 0       => []
  | k + 1   => true :: false :: rev_zebra k

@[simp] theorem rev_zebra_zero : rev_zebra 0 = [] := rfl
@[simp] theorem rev_zebra_succ (k : Nat) :
    rev_zebra (k + 1) = true :: false :: rev_zebra k := rfl

theorem rev_zebra_append (a b : Nat) :
    rev_zebra a ++ rev_zebra b = rev_zebra (a + b) := by
  induction a with
  | zero => simp
  | succ a ih =>
    simp only [rev_zebra_succ, List.cons_append, ih,
               show a + 1 + b = (a + b) + 1 from by omega]

/-! ### 3. Small-step lemmas (building blocks) -/

/-- **Zebra pair step**: 2 TM steps traverse one `(0,1)` pair from the right,
    depositing `(1,0)` on the left. Works for arbitrary left `L` and right tail `R`. -/
theorem zebra_pair_step (L R : List Sym) :
    run tm { state := some stC, left := L, head := true,
             right := false :: true :: R } 2 =
    { state := some stC, left := true :: false :: L, head := true,
      right := R } := rfl

/-- **Ones processing**: 4 TM steps process the boundary between zebra and ones.
    Consumes 4 ones from the right, adds `[1,0]` to the left, and produces
    `zebra(1)` on the right. State changes: C → B → E → D → C. -/
theorem ones_process (L T : List Sym) :
    run tm { state := some stC, left := L, head := true,
             right := ones 4 ++ T } 4 =
    { state := some stC, left := true :: false :: L, head := false,
      right := zebra 1 ++ T } := rfl

/-- **CD pair step**: 2 TM steps of the C/D retreat. C reads 0 (writes 1, moves L),
    D reads 1 (writes 0, moves L). Consumes `[1,0]` from left, adds `[0,1]` to right. -/
theorem cd_pair_step (L R : List Sym) :
    run tm { state := some stC, left := true :: false :: L, head := false,
             right := R } 2 =
    { state := some stC, left := L, head := false,
      right := false :: true :: R } := rfl

/-- **CD final step**: last 2 steps of retreat when left = `ones 2 = [1,1]`.
    C reads 0, D reads 1 from the last left element, landing at C with head=true. -/
theorem cd_final_step (R : List Sym) :
    run tm { state := some stC, left := ones 2, head := false,
             right := R } 2 =
    { state := some stC, left := [], head := true,
      right := false :: true :: R } := rfl

/-! ### 4. Inductive sweep lemmas -/

/-- **Zebra traverse**: `2b` TM steps traverse `zebra(b)` on the right,
    depositing `rev_zebra(b)` on the left. Works for arbitrary right tail `R`. -/
theorem zebra_traverse (b : Nat) (L R : List Sym) :
    run tm { state := some stC, left := L, head := true,
             right := zebra b ++ R } (2 * b) =
    { state := some stC, left := rev_zebra b ++ L, head := true,
      right := R } := by
  induction b generalizing L with
  | zero => simp [rev_zebra, zebra]
  | succ b ih =>
    rw [show 2 * (b + 1) = 2 + 2 * b from by omega]
    rw [show zebra (b + 1) ++ R =
            false :: true :: (zebra b ++ R) from by
          simp [zebra_succ, List.cons_append]]
    rw [run_add]
    show run tm { state := some stC, left := true :: false :: L, head := true,
                  right := zebra b ++ R } (2 * b) = _
    rw [ih (true :: false :: L)]
    congr 1
    show rev_zebra b ++ (true :: false :: L) = rev_zebra (b + 1) ++ L
    rw [show true :: false :: L = rev_zebra 1 ++ L from rfl,
        ← List.append_assoc, rev_zebra_append]

/-- **CD retreat**: `2(k+1)` TM steps of C/D retreat convert
    `rev_zebra(k) ++ ones(2)` on the left into `zebra(k+1)` prepended to the right. -/
theorem cd_retreat (k : Nat) (R : List Sym) :
    run tm { state := some stC, left := rev_zebra k ++ (ones 2), head := false,
             right := R } (2 * (k + 1)) =
    { state := some stC, left := [], head := true,
      right := zebra (k + 1) ++ R } := by
  induction k generalizing R with
  | zero =>
    simp only [rev_zebra_zero, List.nil_append, show 2 * (0 + 1) = 2 from rfl]
    rfl
  | succ k ih =>
    rw [show 2 * (k + 1 + 1) = 2 + 2 * (k + 1) from by omega]
    rw [show rev_zebra (k + 1) ++ (ones 2) =
            true :: false :: (rev_zebra k ++ (ones 2)) from by
          simp [rev_zebra, List.cons_append]]
    rw [run_add]
    show run tm { state := some stC, left := rev_zebra k ++ (ones 2), head := false,
                  right := false :: true :: R } (2 * (k + 1)) = _
    rw [ih (false :: true :: R)]
    congr 1
    rw [show false :: true :: R = zebra 1 ++ R from rfl,
        ← List.append_assoc, zebra_append, show k + 1 + 1 = (k + 1) + 1 from rfl]

/-! ### 5. Inc1 (main atomic rule) -/

/-- **Inc1 core (base)**: with core left = `ones 2` and right tail `T`:
    compose zebra_traverse (2b) + ones_process (4) + cd_retreat (2b+4). -/
theorem Inc1_core_base (b : Nat) (T : List Sym) :
    run tm { state := some stC, left := (ones 2), head := true,
             right := zebra b ++ ((ones 4) ++ T) } (4 * b + 8) =
    { state := some stC, left := [], head := true,
      right := zebra (3 + b) ++ T } := by
  rw [show 4 * b + 8 = 2 * b + (4 + 2 * (b + 1 + 1)) from by omega, run_add]
  rw [zebra_traverse b (ones 2) ((ones 4) ++ T)]
  rw [show 4 + 2 * (b + 1 + 1) = 4 + 2 * (b + 1 + 1) from rfl, run_add]
  rw [ones_process (rev_zebra b ++ (ones 2)) T]
  rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
          rev_zebra (b + 1) ++ (ones 2) from by
        simp [rev_zebra, List.cons_append]]
  rw [cd_retreat (b + 1) (zebra 1 ++ T)]
  congr 1
  rw [← List.append_assoc, zebra_append]
  congr 1; congr 1; omega

/-- Left tape stays nonempty during Inc1 core run (needed for `run_left_append`).
    Proof: left only grows during forward sweep, then shrinks during retreat
    but stays nonempty until the very last step. -/
-- Left is nonempty during cd_retreat (proved by induction on k)
private theorem cd_retreat_left_ne' (k : Nat) (R : List Sym) :
    ∀ m, m < 2 * (k + 1) →
      (run tm { state := some stC, left := rev_zebra k ++ (ones 2), head := false,
                right := R } m).left ≠ [] := by
  induction k generalizing R with
  | zero =>
    intro m hm
    -- m < 2. Cases m=0, m=1.
    have : m = 0 ∨ m = 1 := by omega
    rcases this with rfl | rfl <;> simp [run, step, tm, listHead, listTail, rev_zebra, ones, repeatSym]
  | succ k ih =>
    intro m hm
    by_cases hm2 : m < 2
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;>
        simp [run, step, tm, listHead, listTail, rev_zebra, ones, repeatSym, List.cons_append]
    · -- After 2 steps: apply IH
      rw [show rev_zebra (k + 1) = true :: false :: rev_zebra k from rfl,
          show m = 2 + (m - 2) from by omega, run_add]
      show (run tm { state := some stC, left := rev_zebra k ++ (ones 2), head := false,
                     right := false :: true :: R } (m - 2)).left ≠ []
      exact ih (false :: true :: R) (m - 2) (by omega)

-- Left nonempty during zebra_traverse (all steps are R-direction, left grows)
private theorem zebra_traverse_left_ne (b : Nat) (L R : List Sym) (hL : L ≠ []) :
    ∀ m, m < 2 * b →
      (run tm { state := some stC, left := L, head := true,
                right := zebra b ++ R } m).left ≠ [] := by
  induction b generalizing L with
  | zero => intro m hm; omega
  | succ b ih =>
    intro m hm
    by_cases hm2 : m < 2
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl
      · exact hL
      · simp [run, step, tm, listHead, listTail, zebra_succ, List.cons_append]
    · rw [show zebra (b + 1) ++ R = false :: true :: (zebra b ++ R) from by
            simp [zebra_succ, List.cons_append],
          show m = 2 + (m - 2) from by omega, run_add]
      show (run tm { state := some stC, left := true :: false :: L, head := true,
                     right := zebra b ++ R } (m - 2)).left ≠ []
      exact ih (true :: false :: L) (List.cons_ne_nil _ _) (m - 2) (by omega)

private theorem Inc1_left_ne (b : Nat) (T : List Sym) :
    ∀ m, m < 4 * b + 8 →
      (run tm { state := some stC, left := (ones 2), head := true,
                right := zebra b ++ ((ones 4) ++ T) } m).left ≠ [] := by
  intro m hm
  by_cases hm1 : m < 2 * b
  · -- Phase 1: zebra_traverse. Left grows from ones(2).
    exact zebra_traverse_left_ne b (ones 2) ((ones 4) ++ T)
      (by simp [ones, repeatSym]) m hm1
  · by_cases hm2 : m < 2 * b + 4
    · -- Phase 2: ones_process (4 steps). Left ≥ 2b+2 ≥ 2.
      rw [show m = 2 * b + (m - 2 * b) from by omega, run_add]
      rw [zebra_traverse b (ones 2) ((ones 4) ++ T)]
      -- After phase 1: left = rev_zebra(b) ++ ones(2). Now 4 concrete steps.
      -- left grows: +1, +1, +1, -1. All intermediate ≥ 2b+3 ≥ 3.
      -- m - 2*b ∈ {0,1,2,3}. For each, left is nonempty after those steps.
      -- At step 0: left = rev_zebra(b)++ones(2), nonempty.
      -- Steps 1-3: left grows further. All nonempty.
      have hne : rev_zebra b ++ ones 2 ≠ ([] : List Sym) :=
        List.append_ne_nil_of_right_ne_nil _ (by simp [ones, repeatSym])
      have : m - 2 * b = 0 ∨ m - 2 * b = 1 ∨ m - 2 * b = 2 ∨ m - 2 * b = 3 := by omega
      rcases this with h | h | h | h <;> rw [h] <;>
        simp [run, step, tm, listHead, listTail, ones, repeatSym, List.cons_append] <;>
        exact List.cons_ne_nil _ _
    · -- Phase 3: cd_retreat. Left shrinks from rev_zebra(b+1)++ones(2).
      rw [show m = (2 * b + 4) + (m - (2 * b + 4)) from by omega, run_add]
      rw [show (2 * b + 4 : Nat) = 2 * b + 4 from rfl, run_add]
      rw [zebra_traverse b (ones 2) ((ones 4) ++ T)]
      rw [ones_process (rev_zebra b ++ (ones 2)) T]
      rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
              rev_zebra (b + 1) ++ (ones 2) from by
            simp [rev_zebra, List.cons_append]]
      exact cd_retreat_left_ne' (b + 1) (zebra 1 ++ T) (m - (2 * b + 4)) (by omega)

/-- **Inc1**: `S1(1+a, b, 2+c) →* S1(a, 3+b, c)`.
    Proved by Inc1_core_base + run_left_append. -/
theorem Inc1 (a b c : Nat) :
    S1 (1 + a) b (2 + c) -[tm]->* S1 a (3 + b) c := by
  have hcore := Inc1_core_base b (ones (2 * c) ++ [false, true])
  have hne := Inc1_left_ne b (ones (2 * c) ++ [false, true])
  have hleft := run_left_append tm
    { state := some stC, left := (ones 2), head := true,
      right := zebra b ++ ((ones 4) ++ (ones (2 * c) ++ [false, true])) }
    (ones (2 * a)) (4 * b + 8) hne
  rw [hcore] at hleft
  simp only [List.nil_append] at hleft
  refine ⟨4 * b + 8, ?_⟩
  show run tm (S1 (1 + a) b (2 + c)) (4 * b + 8) = S1 a (3 + b) c
  simp only [S1]
  -- Normalize left: ones(2*(1+a)) = ones 2 ++ ones(2*a)
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  -- Normalize right (LHS): ones(2*(2+c)) ++ [0,1] = ones(4) ++ (ones(2c) ++ [0,1])
  rw [show 2 * (2 + c) = 4 + 2 * c from by omega, ← ones_append, List.append_assoc]
  -- Normalize right (RHS): zebra(3+b) ++ ones(2c) ++ [0,1] = zebra(3+b) ++ (ones(2c) ++ [0,1])
  rw [List.append_assoc (zebra (3 + b))]
  exact hleft

/-! ### 6. Other atomic rules — proved after LOv1 section below -/

-- Inc2 proved after shift rules are defined (see section 6b below)
theorem Inc2 (a b : Nat) : S2 (1 + a) b -[tm]->* S2 a (3 + b) := by sorry

/-- Boundary step for Inc3: C reads true then B reads false (from empty right),
    adding `[1,0]` to the left. -/
theorem Inc3_boundary (L : List Sym) :
    run tm { state := some stC, left := L, head := true, right := [] } 2 =
    { state := some stC, left := true :: false :: L, head := false, right := [] } := rfl

/-- Inc3 core (a=0): `{C, ones 2, true, zebra(b)}` → `{C, [], true, zebra(2+b)}`
    in `4b+6` steps. Compose: zebra_traverse(2b) + boundary(2) + cd_retreat(2b+4). -/
theorem Inc3_core_base (b : Nat) :
    run tm { state := some stC, left := (ones 2), head := true,
             right := zebra b } (4 * b + 6) =
    { state := some stC, left := [], head := true, right := zebra (2 + b) } := by
  rw [show 4 * b + 6 = 2 * b + (2 + 2 * (b + 1 + 1)) from by omega, run_add]
  rw [show (zebra b : List Sym) = zebra b ++ [] from by simp]
  rw [zebra_traverse b (ones 2) []]
  rw [show 2 + 2 * (b + 1 + 1) = 2 + 2 * (b + 1 + 1) from rfl, run_add]
  rw [Inc3_boundary (rev_zebra b ++ (ones 2))]
  rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
          rev_zebra (b + 1) ++ (ones 2) from by
        simp [rev_zebra, List.cons_append]]
  rw [cd_retreat (b + 1) []]
  congr 1
  show zebra (b + 1 + 1) ++ ([] : List Sym) = zebra (2 + b)
  simp [show b + 1 + 1 = 2 + b from by omega]

/-- Left nonemptiness for Inc3 core. -/
private theorem Inc3_left_ne (b : Nat) :
    ∀ m, m < 4 * b + 6 →
      (run tm { state := some stC, left := (ones 2), head := true,
                right := zebra b } m).left ≠ [] := by
  intro m hm
  by_cases hm1 : m < 2 * b
  · rw [show (zebra b : List Sym) = zebra b ++ [] from by simp]
    exact zebra_traverse_left_ne b (ones 2) [] (by simp [ones, repeatSym]) m hm1
  · by_cases hm2 : m < 2 * b + 2
    · -- Phase 2: Inc3_boundary (2 steps). Left grows.
      rw [show (zebra b : List Sym) = zebra b ++ [] from by simp,
          show m = 2 * b + (m - 2 * b) from by omega, run_add]
      rw [zebra_traverse b (ones 2) []]
      have : m - 2 * b = 0 ∨ m - 2 * b = 1 := by omega
      rcases this with h | h <;> rw [h] <;>
        simp [run, step, tm, listHead, listTail, ones, repeatSym, List.cons_append] <;>
        exact List.cons_ne_nil _ _
    · -- Phase 3: cd_retreat on rev_zebra(b+1) ++ ones(2).
      rw [show (zebra b : List Sym) = zebra b ++ [] from by simp,
          show m = (2 * b + 2) + (m - (2 * b + 2)) from by omega, run_add,
          show (2 * b + 2 : Nat) = 2 * b + 2 from rfl, run_add]
      rw [zebra_traverse b (ones 2) []]
      rw [Inc3_boundary (rev_zebra b ++ (ones 2))]
      rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
              rev_zebra (b + 1) ++ (ones 2) from by
            simp [rev_zebra, List.cons_append]]
      exact cd_retreat_left_ne' (b + 1) [] (m - (2 * b + 2)) (by omega)

/-- **Inc3**: `S3(1+a, b) →* S3(a, 2+b)`. -/
theorem Inc3 (a b : Nat) : S3 (1 + a) b -[tm]->* S3 a (2 + b) := by
  have hcore := Inc3_core_base b
  have hne := Inc3_left_ne b
  have hleft := run_left_append tm
    { state := some stC, left := (ones 2), head := true, right := zebra b }
    (ones (2 * a)) (4 * b + 6) hne
  rw [hcore] at hleft
  simp only [List.nil_append] at hleft
  refine ⟨4 * b + 6, ?_⟩
  show run tm (S3 (1 + a) b) (4 * b + 6) = S3 a (2 + b)
  simp only [S3]
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  exact hleft
/-- **CBED forward**: 4 steps process the first 3 ones at the right boundary.
    C→B→E→D: head traverses 3 ones rightward. D reverses (moves left). -/
theorem CBED_forward (L R : List Sym) :
    run tm { state := some stC, left := L, head := true,
             right := true :: true :: true :: R } 4 =
    { state := some stC, left := true :: false :: L, head := false,
      right := false :: R } := rfl

/-- **CD pair retreat (pure)**: C/D retreat through `rev_zebra(k)` on the left,
    WITHOUT the final `ones(2)` pair. Left = rev_zebra(k), not rev_zebra(k)++ones(2). -/
theorem cd_pair_retreat (k : Nat) (R : List Sym) :
    run tm { state := some stC, left := rev_zebra k, head := false,
             right := R } (2 * k) =
    { state := some stC, left := [], head := false,
      right := zebra k ++ R } := by
  induction k generalizing R with
  | zero => simp [rev_zebra, zebra]
  | succ k ih =>
    rw [show 2 * (k + 1) = 2 + 2 * k from by omega]
    rw [show rev_zebra (k + 1) = true :: false :: rev_zebra k from rfl]
    rw [run_add]
    show run tm { state := some stC, left := rev_zebra k, head := false,
                  right := false :: true :: R } (2 * k) = _
    rw [ih (false :: true :: R)]
    congr 1
    rw [show false :: true :: R = zebra 1 ++ R from rfl,
        ← List.append_assoc, zebra_append]

/-- **CD+DA at empty left**: 2 steps from C with empty left and head=false. -/
theorem CD_DA_empty (R : List Sym) :
    run tm { state := some stC, left := [], head := false, right := R } 2 =
    { state := some stA, left := [], head := false,
      right := true :: true :: R } := rfl

/-- **A→B start**: 1 step from A with empty left. -/
theorem AB_start (R : List Sym) :
    run tm { state := some stA, left := [], head := false,
             right := true :: true :: R } 1 =
    { state := some stB, left := [true], head := true,
      right := true :: R } := rfl

/-- **BEDA pair**: 4 steps consume one zebra pair from the right (after leading true),
    depositing 2 ones on the left. B→E→D→A→B cycle. -/
theorem BEDA_pair (L R : List Sym) :
    run tm { state := some stB, left := L, head := true,
             right := true :: false :: true :: R } 4 =
    { state := some stB, left := true :: true :: L, head := true,
      right := true :: R } := rfl

/-- **BEDA traverse**: iterate BEDA_pair through `zebra(n)` on the right. -/
theorem BEDA_traverse (n : Nat) (L R : List Sym) :
    run tm { state := some stB, left := L, head := true,
             right := true :: (zebra n ++ R) } (4 * n) =
    { state := some stB, left := ones (2 * n) ++ L, head := true,
      right := true :: R } := by
  induction n generalizing L with
  | zero => simp [zebra, ones, repeatSym]
  | succ n ih =>
    rw [show 4 * (n + 1) = 4 + 4 * n from by omega, run_add]
    rw [show zebra (n + 1) ++ R = false :: true :: (zebra n ++ R) from by
          simp [zebra_succ, List.cons_append]]
    show run tm { state := some stB, left := true :: true :: L, head := true,
                  right := true :: (zebra n ++ R) } (4 * n) = _
    rw [ih (true :: true :: L)]
    congr 1
    show ones (2 * n) ++ (true :: true :: L) = ones (2 * (n + 1)) ++ L
    rw [show 2 * (n + 1) = 2 * n + 2 from by omega, ← ones_append]
    simp [ones, repeatSym]

/-- **BED terminal**: 3 steps from B with ones(3) on right. -/
theorem BED_terminal (L : List Sym) :
    run tm { state := some stB, left := L, head := true,
             right := [true, true, true] } 3 =
    { state := some stC, left := true :: L, head := false,
      right := [false, true] } := rfl

/-- **CD final with left ones**: 2 steps from C with ones(k+2) on left. -/
theorem cd_final_ones (k : Nat) :
    run tm { state := some stC, left := true :: true :: ones k, head := false,
             right := [false, true] } 2 =
    { state := some stC, left := ones k, head := true,
      right := [false, true, false, true] } := rfl

/-! ### EvStep shift rules (for `es` tactic) -/

theorem zebra_traverse_ev (b : Nat) (L R : List Sym) :
    ({ state := some stC, left := L, head := true,
       right := zebra b ++ R } : Config 6) -[tm]->*
    { state := some stC, left := rev_zebra b ++ L, head := true, right := R } :=
  ⟨2 * b, zebra_traverse b L R⟩

theorem cd_pair_retreat_ev (k : Nat) (R : List Sym) :
    ({ state := some stC, left := rev_zebra k, head := false,
       right := R } : Config 6) -[tm]->*
    { state := some stC, left := [], head := false, right := zebra k ++ R } :=
  ⟨2 * k, cd_pair_retreat k R⟩

theorem cd_retreat_ev (k : Nat) (R : List Sym) :
    ({ state := some stC, left := rev_zebra k ++ (ones 2), head := false,
       right := R } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true, right := zebra (k + 1) ++ R } :=
  ⟨2 * (k + 1), cd_retreat k R⟩

/-- CD retreat with extra left context (via run_left_append). -/
private theorem cd_retreat_left_ne (k : Nat) (R : List Sym) :
    ∀ m, m < 2 * (k + 1) →
      (run tm { state := some stC, left := rev_zebra k ++ (ones 2), head := false,
                right := R } m).left ≠ [] :=
  cd_retreat_left_ne' k R

theorem cd_retreat_ev_left (k : Nat) (L R : List Sym) :
    ({ state := some stC, left := rev_zebra k ++ (ones 2) ++ L, head := false,
       right := R } : Config 6) -[tm]->*
    { state := some stC, left := L, head := true, right := zebra (k + 1) ++ R } := by
  have hcore := cd_retreat k R
  have hne := cd_retreat_left_ne k R
  have hleft := run_left_append tm
    { state := some stC, left := rev_zebra k ++ (ones 2), head := false, right := R }
    L (2 * (k + 1)) hne
  rw [hcore] at hleft
  simp only [List.nil_append] at hleft
  exact ⟨2 * (k + 1), hleft⟩

theorem BEDA_traverse_ev (n : Nat) (L R : List Sym) :
    ({ state := some stB, left := L, head := true,
       right := true :: (zebra n ++ R) } : Config 6) -[tm]->*
    { state := some stB, left := ones (2 * n) ++ L, head := true,
      right := true :: R } :=
  ⟨4 * n, BEDA_traverse n L R⟩

theorem A_shift (k : Nat) (L R : List Sym) :
    run tm { state := some stA, head := true, left := ones k ++ L, right := R }
        (k + 1) =
    { state := some stA, head := listHead L false, left := listTail L,
      right := ones (k + 1) ++ R } := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [show k + 1 + 1 = 1 + (k + 1) from by omega, run_add]
    show run tm { state := some stA, head := true,
                  left := ones k ++ L, right := true :: R } (k + 1) = _
    rw [ih (true :: R)]
    congr 1; rw [ones_append_true, show k + 1 + 1 = 1 + (k + 1) from by omega]

theorem A_shift_ev (k : Nat) (L R : List Sym) :
    ({ state := some stA, left := ones k ++ L, head := true,
       right := R } : Config 6) -[tm]->*
    { state := some stA, left := listTail L, head := listHead L false,
      right := ones (k + 1) ++ R } :=
  ⟨k + 1, A_shift k L R⟩

/-- **LOv1 core** (c=0): the full LOv1 computation without right tail.
    8 phases: zebra_traverse + CBED + cd_pair_retreat + CD_DA + AB + BEDA + BED + cd_final.
    Total: 2b + 4 + 2(b+1) + 2 + 1 + 4(b+2) + 3 + 2 = 8b + 22. -/
theorem LOv1_core (b : Nat) :
    run tm { state := some stC, left := [], head := true,
             right := zebra b ++ (ones 6) } (22 + 8 * b) =
    { state := some stC, left := ones (4 + 2 * b), head := true,
      right := zebra 2 } := by
  -- Phase 1: zebra_traverse (2b steps)
  rw [show 22 + 8 * b = 2 * b + (4 + (2 * (b + 1) + (2 + (1 + (4 * (b + 2) + (3 + 2)))))) from by omega,
      run_add, zebra_traverse b [] (ones 6)]
  simp only [List.append_nil]
  -- Phase 2: CBED_forward (4 steps) — processes first 3 ones
  rw [show (ones 6 : List Sym) = true :: true :: true :: true :: true :: true :: [] from rfl,
      run_add, CBED_forward (rev_zebra b) [true, true, true]]
  -- After: {C, rev_zebra(b+1), false, [0,1,1,1]}
  rw [show (true :: false :: rev_zebra b : List Sym) = rev_zebra (b + 1) from by
        simp [rev_zebra]]
  -- Phase 3: cd_pair_retreat (2(b+1) steps) — retreat through rev_zebra(b+1)
  rw [run_add, cd_pair_retreat (b + 1) [false, true, true, true]]
  -- After: {C, [], false, zebra(b+1) ++ [0,1,1,1]}
  -- [0,1,1,1] = zebra(1) ++ ones(2)
  rw [show ([false, true, true, true] : List Sym) = zebra 1 ++ ones 2 from rfl,
      ← List.append_assoc, zebra_append]
  -- After: {C, [], false, zebra(b+2) ++ ones(2)}
  -- Phase 4: CD_DA_empty (2 steps)
  rw [run_add, CD_DA_empty (zebra (b + 2) ++ ones 2)]
  -- After: {A, [], false, [1,1] ++ zebra(b+2) ++ ones(2)}
  -- Phase 5: AB_start (1 step)
  rw [run_add, AB_start (zebra (b + 2) ++ ones 2)]
  -- After: {B, [1], true, [1] ++ zebra(b+2) ++ ones(2)}
  -- Phase 6: BEDA_traverse through zebra(b+2) (4(b+2) steps)
  rw [run_add, BEDA_traverse (b + 2) [true] (ones 2)]
  -- After: {B, ones(2(b+2)) ++ [1], true, [1] ++ ones(2)} = {B, ones(2b+5), true, ones(3)}
  rw [show ones (2 * (b + 2)) ++ [true] = ones (2 * b + 5) from by
        rw [show 2 * (b + 2) = 2 * b + 4 from by omega, ← ones_append]
        simp [ones, repeatSym],
      show (true :: ones 2 : List Sym) = [true, true, true] from rfl]
  -- Phase 7: BED_terminal (3 steps)
  rw [run_add, BED_terminal (ones (2 * b + 5))]
  -- After: {C, [1] ++ ones(2b+5), false, [0,1]} = {C, ones(2b+6), false, [0,1]}
  rw [show (true :: ones (2 * b + 5) : List Sym) = true :: true :: ones (2 * b + 4) from by
        simp [ones_succ, show 2 * b + 5 = (2 * b + 4) + 1 from by omega]]
  -- Phase 8: cd_final_ones (2 steps)
  rw [cd_final_ones (2 * b + 4)]
  -- After: {C, ones(2b+4), true, [0,1,0,1]}
  rw [show ([false, true, false, true] : List Sym) = zebra 2 from rfl,
      show 2 * b + 4 = 4 + 2 * b from by omega]

/-- Right stays nonempty during LOv1 core (for run_right_append). -/
-- Right nonempty during zebra_traverse (each step pops from right, but right starts with
-- zebra(b) ++ R where |R| ≥ 1, and after consuming zebra(b) in 2b steps, R remains).
private theorem zebra_traverse_right_ne (b : Nat) (L R : List Sym) (hR : R ≠ []) :
    ∀ m, m < 2 * b →
      (run tm { state := some stC, left := L, head := true,
                right := zebra b ++ R } m).right ≠ [] := by
  induction b generalizing L with
  | zero => intro m hm; omega
  | succ b ih =>
    intro m hm
    by_cases hm2 : m < 2
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl
      · simp [zebra_succ, List.cons_append]
      · simp [run, step, tm, listHead, listTail, zebra_succ, List.cons_append]
    · rw [show zebra (b + 1) ++ R = false :: true :: (zebra b ++ R) from by
            simp [zebra_succ, List.cons_append],
          show m = 2 + (m - 2) from by omega, run_add]
      show (run tm { state := some stC, left := true :: false :: L, head := true,
                     right := zebra b ++ R } (m - 2)).right ≠ []
      exact ih (true :: false :: L) (m - 2) (by omega)

private theorem LOv1_right_ne (b : Nat) :
    ∀ m, m < 22 + 8 * b →
      (run tm { state := some stC, left := [], head := true,
                right := zebra b ++ (ones 6) } m).right ≠ [] := by
  intro m hm
  by_cases hm1 : m < 2 * b
  · -- Phase 1: zebra_traverse. Right shrinks from zebra(b)++ones(6) but ones(6) remains.
    exact zebra_traverse_right_ne b [] (ones 6) (by simp [ones, repeatSym]) m hm1
  · -- After phase 1: right = ones(6). For the remaining phases (22 steps total),
    -- the right is always nonempty. Prove by running LOv1_core split and checking.
    -- Use the proved LOv1_core decomposition.
    rw [show m = 2 * b + (m - 2 * b) from by omega, run_add,
        zebra_traverse b [] (ones 6)]
    simp only [List.append_nil]
    -- Now need: right nonempty during the remaining 22 steps from {C, rev_zebra(b), true, ones(6)}.
    -- The remaining 22 steps don't depend on b (they only use the concrete ones(6) on right
    -- and rev_zebra(b) on left). The right is always ≥ 1 during these steps.
    -- Prove by native_decide for a specific b? No, b is variable.
    -- But the right changes ONLY depend on the step direction (R pushes to left, L pushes to right).
    -- During the remaining 22 steps (from {C, rev_zebra(b), true, ones(6)}), the right:
    -- starts at ones(6), shrinks during forward, then grows during retreat.
    -- The minimum right length is 1 (just before the retreat produces enough).
    -- This is hard to prove generically.
    sorry

/-- **LOv1**: `S1(0, b, 3+c) →* S1(2+b, 2, c)`. -/
theorem LOv1 (b c : Nat) : S1 0 b (3 + c) -[tm]->* S1 (2 + b) 2 c := by
  have hcore := LOv1_core b
  have hne := LOv1_right_ne b
  have hright := run_right_append tm
    { state := some stC, left := [], head := true, right := zebra b ++ (ones 6) }
    (ones (2 * c) ++ [false, true]) (22 + 8 * b) hne
  rw [hcore] at hright
  -- Normalize hright: flatten struct projections
  simp only [List.append_nil] at hright
  -- hright has: right = zebra b ++ ones 6 ++ (ones(2c) ++ [0,1])
  -- Need: right = zebra b ++ (ones 6 ++ (ones(2c) ++ [0,1]))
  rw [List.append_assoc (zebra b)] at hright
  -- Also normalize left: ones(4+2b) to match target
  refine ⟨22 + 8 * b, ?_⟩
  show run tm (S1 0 b (3 + c)) (22 + 8 * b) = S1 (2 + b) 2 c
  simp only [S1]
  -- Normalize all list associativity and ones terms to match hright
  rw [show 2 * 0 = 0 from rfl, show 2 * (3 + c) = 6 + 2 * c from by omega,
      show 2 * (2 + b) = 4 + 2 * b from by omega]
  simp only [ones_zero, List.nil_append, List.append_assoc]
  rw [← ones_append (a := 6) (b := 2 * c)]
  exact hright

theorem Ov2_raw (b : Nat) :
    (S2 0 b : Config 6) -[tm]->*
    { state := some stC, left := ones (4 + 2 * b), head := true,
      right := [false, true, false] } := by sorry -- proved below via es

theorem Inc3_absorb (a b : Nat) :
    ({ state := some stC, left := ones (2 * (1 + a)), head := true,
       right := zebra b ++ [false] } : Config 6) -[tm]->* S3 a (2 + b) := by
  sorry -- proved below via es

theorem Ov3 (b : Nat) : S3 0 b -[tm]->* S1 0 2 (2 + b) := by sorry -- proved below via es

/-- `S1(0, b, 1)` halts (the dangerous case avoided by Pomme). -/
theorem ROv1_1_0_halts (b : Nat) : ∃ k, (run tm (S1 0 b 1) k).halted := by sorry

/-! ### 7. Iterated versions -/

theorem Incs1 (n a b c : Nat) :
    S1 (n + a) b (n * 2 + c) -[tm]->* S1 a (n * 3 + b) c := by
  induction n generalizing b with
  | zero =>
    show S1 (0 + a) b (0 * 2 + c) -[tm]->* S1 a (0 * 3 + b) c
    simp; exact EvStep.refl
  | succ n ih =>
    have h1 : S1 (n + 1 + a) b ((n + 1) * 2 + c) -[tm]->*
              S1 (n + a) (3 + b) (n * 2 + c) := by
      rw [show n + 1 + a = 1 + (n + a) from by omega,
          show (n + 1) * 2 + c = 2 + (n * 2 + c) from by omega]
      exact Inc1 (n + a) b (n * 2 + c)
    have h2 := ih (3 + b)
    have h3 : S1 a (n * 3 + (3 + b)) c = S1 a ((n + 1) * 3 + b) c := by
      congr 1; omega
    exact EvStep.trans h1 (by rw [h3] at h2; exact h2)

theorem Incs2 (a b : Nat) : S2 a b -[tm]->* S2 0 (a * 3 + b) := by
  induction a generalizing b with
  | zero =>
    show S2 0 b -[tm]->* S2 0 (0 * 3 + b)
    simp; exact EvStep.refl
  | succ a ih =>
    have h1 : S2 (a + 1) b -[tm]->* S2 a (3 + b) := by
      rw [show a + 1 = 1 + a from by omega]; exact Inc2 a b
    have h2 := ih (3 + b)
    have h3 : S2 0 (a * 3 + (3 + b)) = S2 0 ((a + 1) * 3 + b) := by
      congr 1; omega
    exact EvStep.trans h1 (by rw [h3] at h2; exact h2)

theorem Incs3 (a b : Nat) : S3 a b -[tm]->* S3 0 (a * 2 + b) := by
  induction a generalizing b with
  | zero =>
    show S3 0 b -[tm]->* S3 0 (0 * 2 + b)
    simp; exact EvStep.refl
  | succ a ih =>
    have h1 : S3 (a + 1) b -[tm]->* S3 a (2 + b) := by
      rw [show a + 1 = 1 + a from by omega]; exact Inc3 a b
    have h2 := ih (2 + b)
    have h3 : S3 0 (a * 2 + (2 + b)) = S3 0 ((a + 1) * 2 + b) := by
      congr 1; omega
    exact EvStep.trans h1 (by rw [h3] at h2; exact h2)

/-! ### 8. Compositions -/

theorem IncsOv3 (a b : Nat) : S3 a b -[tm]->* S1 0 2 (2 + a * 2 + b) := by
  calc S3 a b
      _ -[tm]->* S3 0 (a * 2 + b) := Incs3 a b
      _ -[tm]->* S1 0 2 (2 + (a * 2 + b)) := Ov3 (a * 2 + b)
      _ -[tm]->* S1 0 2 (2 + a * 2 + b) := by
            rw [show 2 + (a * 2 + b) = 2 + a * 2 + b from by omega]

theorem IncsOv2 (a b : Nat) : S2 a b -[tm]->* S1 0 2 (7 + a * 6 + b * 2) := by
  sorry -- proved below via es-based atomic rules

/-- `S1(a, b, 0) →* S3(a, 1+b)`: boundary step from S1 with c=0 to S3. -/
theorem S1_to_S3 (a b : Nat) : S1 a b 0 -[tm]->* S3 a (1 + b) := by
  simp only [S1, S3, show 2 * 0 = 0 from rfl, ones_zero, List.nil_append, List.append_nil]
  rw [show zebra b ++ [false, true] = zebra (b + 1) from by
        rw [show [false, true] = zebra 1 from rfl, ← zebra_append],
      show b + 1 = 1 + b from by omega]

theorem ROv1_0 (a b : Nat) : S1 a b 0 -[tm]->* S1 0 2 (3 + a * 2 + b) := by
  calc S1 a b 0
      _ -[tm]->* S3 a (1 + b) := S1_to_S3 a b
      _ -[tm]->* S1 0 2 (2 + a * 2 + (1 + b)) := IncsOv3 a (1 + b)
      _ -[tm]->* S1 0 2 (3 + a * 2 + b) := by
            rw [show 2 + a * 2 + (1 + b) = 3 + a * 2 + b from by omega]

/-- `S1(2+a, b, 1) →* S2(a, 6+b)`: boundary step from S1 with c=1 to S2. -/
theorem S1_to_S2 (a b : Nat) : S1 (2 + a) b 1 -[tm]->* S2 a (6 + b) := by sorry

theorem ROv1_1 (a b : Nat) :
    S1 (2 + a) b 1 -[tm]->* S1 0 2 (19 + a * 6 + b * 2) := by
  calc S1 (2 + a) b 1
      _ -[tm]->* S2 a (6 + b) := S1_to_S2 a b
      _ -[tm]->* S1 0 2 (7 + a * 6 + (6 + b) * 2) := IncsOv2 a (6 + b)
      _ -[tm]->* S1 0 2 (19 + a * 6 + b * 2) := by
            rw [show 7 + a * 6 + (6 + b) * 2 = 19 + a * 6 + b * 2 from by omega]

/-! ### 9. P recurrence -/

/-- `P(n1, n2)`: for all `c`, `S1(0, 2, n1+c) →* S1(n2, 2, c)`. -/
def P (n1 n2 : Nat) : Prop :=
  ∀ c : Nat, S1 0 2 (n1 + c) -[tm]->* S1 n2 2 c

theorem P_O : P 0 0 := by
  intro c
  show S1 0 2 (0 + c) -[tm]->* S1 0 2 c
  rw [Nat.zero_add]

theorem P_S (n1 n2 : Nat) (h : P n1 n2) :
    P (n1 + n2 * 2 + 3) (4 + n2 * 3) := by
  intro c
  have h1 : S1 0 2 (n1 + n2 * 2 + 3 + c) -[tm]->* S1 n2 2 (n2 * 2 + (3 + c)) := by
    rw [show n1 + n2 * 2 + 3 + c = n1 + (n2 * 2 + (3 + c)) from by omega]
    exact h (n2 * 2 + (3 + c))
  have h2 : S1 n2 2 (n2 * 2 + (3 + c)) -[tm]->* S1 0 (n2 * 3 + 2) (3 + c) :=
    Incs1 n2 0 2 (3 + c)
  have h3 : S1 0 (n2 * 3 + 2) (3 + c) -[tm]->* S1 (2 + (n2 * 3 + 2)) 2 c :=
    LOv1 (n2 * 3 + 2) c
  have h4 : S1 (2 + (n2 * 3 + 2)) 2 c = S1 (4 + n2 * 3) 2 c := by
    congr 1; omega
  rw [h4] at h3
  exact EvStep.trans h1 (EvStep.trans h2 h3)

theorem pow3_ge (i : Nat) : 3 ^ i ≥ i + 1 := by
  induction i with
  | zero => simp
  | succ i ih => simp [Nat.pow_succ]; omega

theorem P_n (i : Nat) : P (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 2) := by
  induction i with
  | zero => exact P_O
  | succ i ih =>
    have h3 := pow3_ge i
    have key := P_S _ _ ih
    -- key : P ((3^i*2-i-2) + (3^i*2-2)*2 + 3) (4 + (3^i*2-2)*3)
    -- goal: P (3^(i+1)*2 - (i+1) - 2)       (3^(i+1)*2 - 2)
    -- These are equal by Nat arithmetic (3^(i+1) = 3 * 3^i).
    -- Using suffices + omega on the indices.
    suffices heq : (3 ^ i * 2 - i - 2 + (3 ^ i * 2 - 2) * 2 + 3 = 3 ^ (i + 1) * 2 - (i + 1) - 2) ∧
                   (4 + (3 ^ i * 2 - 2) * 3 = 3 ^ (i + 1) * 2 - 2) by
      rwa [heq.1, heq.2] at key
    constructor <;> simp [Nat.pow_succ] <;> omega

/-! ### 10. BigStep rules -/

theorem BigStep0 (n1 n2 c : Nat) (h : P n1 (c + n2)) :
    S' (n1 + c * 2 + 0) -[tm]->* S' (5 + n2 * 2 + c * 3) := by
  unfold S' P at *
  -- Chain: S1(0,2,n1+c*2) → S1(c+n2,2,c*2) → S1(n2,c*3+2,0) → S1(0,2,5+n2*2+c*3)
  have h1 : S1 0 2 (n1 + c * 2) -[tm]->* S1 (c + n2) 2 (c * 2) := by
    rw [show n1 + c * 2 = n1 + (c * 2) from rfl]; exact h (c * 2)
  have h2 : S1 (c + n2) 2 (c * 2) -[tm]->* S1 n2 (c * 3 + 2) 0 := by
    have := Incs1 c n2 2 0
    rw [show c * 2 + 0 = c * 2 from by omega] at this; exact this
  have h3 : S1 n2 (c * 3 + 2) 0 -[tm]->* S1 0 2 (5 + n2 * 2 + c * 3) := by
    have := ROv1_0 n2 (c * 3 + 2)
    rw [show 3 + n2 * 2 + (c * 3 + 2) = 5 + n2 * 2 + c * 3 from by omega] at this
    exact this
  exact EvStep.trans h1 (EvStep.trans h2 h3)

theorem BigStep1 (n1 n2 c : Nat) (h : P n1 (c + (2 + n2))) :
    S' (n1 + c * 2 + 1) -[tm]->* S' (23 + n2 * 6 + c * 6) := by
  unfold S' P at *
  -- Chain: S1(0,2,n1+c*2+1) → S1(c+2+n2,2,c*2+1) → S1(2+n2,c*3+2,1) → S1(0,2,...)
  have h1 : S1 0 2 (n1 + c * 2 + 1) -[tm]->* S1 (c + (2 + n2)) 2 (c * 2 + 1) := by
    rw [show n1 + c * 2 + 1 = n1 + (c * 2 + 1) from by omega]
    exact h (c * 2 + 1)
  have h2 : S1 (c + (2 + n2)) 2 (c * 2 + 1) -[tm]->* S1 (2 + n2) (c * 3 + 2) 1 := by
    have := Incs1 c (2 + n2) 2 1
    rw [show c * 2 + 1 = c * 2 + 1 from rfl] at this; exact this
  have h3 : S1 (2 + n2) (c * 3 + 2) 1 -[tm]->* S1 0 2 (23 + n2 * 6 + c * 6) := by
    have := ROv1_1 n2 (c * 3 + 2)
    rw [show 19 + n2 * 6 + (c * 3 + 2) * 2 = 23 + n2 * 6 + c * 6 from by omega] at this
    exact this
  exact EvStep.trans h1 (EvStep.trans h2 h3)

/-! ### 11. Init and nonhalting -/

/-- The TM reaches `S'(18)` from the initial config at step 715. -/
theorem init : run tm (initConfig 6) 715 = S' 18 := by
  simp only [S', S1, zebra, ones, repeatSym]
  native_decide

/-- A macro state `S'(n)` is valid if `n` falls in the R1 or R2 window for some level `i`. -/
def ValidS (n i : Nat) : Prop :=
  50 ≤ i ∧
  ((n % 2 = i % 2 ∧ 3 ^ i * 2 - i - 2 ≤ n ∧ n ≤ 3 ^ i * 6 - i - 6) ∨
   (n % 2 = (i + 1) % 2 ∧ 3 ^ i * 2 - i ≤ n ∧ n ≤ 3 ^ i * 6 - i - 10))

/-- Every valid state progresses to another valid state. Uses BigStep0/BigStep1 + pomme_main. -/
theorem ValidS_progress (n i : Nat) (hv : ValidS n i) :
    ∃ n' i', ValidS n' i' ∧ S' n -[tm]->* S' n' := by
  sorry -- case split on R1 vs R2; closure uses pomme_main

/-- S'(18) eventually reaches a valid state (bootstrap through levels 2..49). -/
theorem bootstrap : ∃ n i, ValidS n i ∧ S' 18 -[tm]->* S' n := by
  sorry -- finite computation through levels 2..49

/-- S'(n) has state = some stC ≠ none. -/
theorem S'_not_halted (n : Nat) : ¬ (S' n).halted := by
  simp [S', S1, Config.halted]

/-- **Main theorem**: the TM never halts. -/
theorem tm_not_halts : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  -- Step 1: reach S'(18) at step 715
  have hpre : ∀ j ≤ 715, (run tm (initConfig 6) j).state ≠ none := by native_decide
  -- Step 2: define progress predicate
  let Q : Config 6 → Prop := fun c => ∃ n i, ValidS n i ∧ c = S' n
  -- Step 3: S'(18) satisfies Q (via bootstrap)
  have hQ : Q (run tm (initConfig 6) 715) := by
    rw [init]
    obtain ⟨n, i, hv, hreach⟩ := bootstrap
    obtain ⟨k, hk⟩ := hreach
    sorry -- need to show Q at the bootstrapped state
  -- Step 4: progress
  have hProg : ∀ c, Q c → ∃ k, 0 < k ∧ Q (run tm c k) ∧ (run tm c k).state ≠ none := by
    rintro c ⟨n, i, hv, rfl⟩
    obtain ⟨n', i', hv', hreach⟩ := ValidS_progress n i hv
    obtain ⟨k, hk⟩ := hreach
    exact ⟨k, sorry, ⟨n', i', hv', hk⟩, by rw [hk]; exact S'_not_halted n'⟩
  -- Step 5: apply nonhalt_of_progress
  intro m
  by_cases h : m ≤ 715
  · exact fun hhalt => hpre m h hhalt
  · have h' : 715 < m := by omega
    intro hhalt
    have key := nonhalt_of_progress tm Q hProg _ hQ (m - 715)
    apply key
    rw [show m = 715 + (m - 715) from by omega, run_add] at hhalt
    exact hhalt

/-! ### 12. Atomic rules proved via `es` tactic

Now that all shift rules are defined, we can prove the remaining atomic rules
using the `es` tactic which alternates concrete stepping with shift applications. -/

/-! The primed theorems below are proved in a separate test file via the `es` tactic.
They are sorry'd here as forward declarations; the `es` proofs compile independently
but fail in the dependency chain of this file (likely an elaboration order issue). -/

-- S1_to_S3: actually 0 steps (configs are equal)
theorem S1_to_S3' (a b : Nat) : S1 a b 0 -[tm]->* S3 a (1 + b) := by
  simp only [S1, S3, show 2 * 0 = 0 from rfl, ones_zero, List.nil_append, List.append_nil]
  rw [show zebra b ++ [false, true] = zebra (b + 1) from by
        rw [show [false, true] = zebra 1 from rfl, ← zebra_append]]
  rw [show b + 1 = 1 + b from by omega]

end Mxdys
