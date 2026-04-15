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

/-- Machine-specific `tape_norm` lemmas for folding `rev_zebra` prefixes. -/
@[tape_norm] theorem rev_zebra_fold_cons (k : Nat) :
    true :: false :: rev_zebra k = rev_zebra (k + 1) := rfl

@[tape_norm] theorem rev_zebra_fold_cons_app (k : Nat) (R : List Sym) :
    true :: false :: (rev_zebra k ++ R) = rev_zebra (k + 1) ++ R := by
  show true :: false :: rev_zebra k ++ R = rev_zebra (k + 1) ++ R
  rfl

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
    rcases this with rfl | rfl <;> simp [run, step, listHead, listTail, rev_zebra, ones, repeatSym]
  | succ k ih =>
    intro m hm
    by_cases hm2 : m < 2
    · have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;>
        simp [run, step, listHead, listTail, rev_zebra, ones, repeatSym, List.cons_append]
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
      · simp [run, step, listHead, listTail, zebra_succ, List.cons_append]
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
        simp [run, step, listHead, listTail, ones, repeatSym, List.cons_append] <;>
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
        simp [run, step, listHead, listTail, ones, repeatSym] <;>
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

/-- **BED terminal**: 3 steps B→E→D→C with right tail. -/
theorem BED_terminal (L T : List Sym) :
    run tm { state := some stB, left := L, head := true,
             right := true :: true :: true :: T } 3 =
    { state := some stC, left := true :: L, head := false,
      right := false :: true :: T } := rfl

/-- **CD final with left ones**: 2 steps with right tail. -/
theorem cd_final_ones (k : Nat) (T : List Sym) :
    run tm { state := some stC, left := true :: true :: ones k, head := false,
             right := false :: true :: T } 2 =
    { state := some stC, left := ones k, head := true,
      right := false :: true :: false :: true :: T } := rfl

/-! ### EvStep shift rules (for `es` tactic) -/

theorem zebra_traverse_ev (b : Nat) (L R : List Sym) :
    ({ state := some stC, left := L, head := true,
       right := zebra b ++ R } : Config 6) -[tm]->*
    { state := some stC, left := rev_zebra b ++ L, head := true, right := R } :=
  ⟨2 * b, zebra_traverse b L R⟩

/-- `nil`-trailing variant of `zebra_traverse_ev`: matches goals whose right
    tape is exactly `zebra b` (no `++ R`).

    Obsolete since `esTryShift` Stage 1 (Phase 1) automatically retries with
    `?R := []`. Kept for reference. -/
theorem zebra_traverse_ev_nil (b : Nat) (L : List Sym) :
    ({ state := some stC, left := L, head := true,
       right := zebra b } : Config 6) -[tm]->*
    { state := some stC, left := rev_zebra b ++ L, head := true, right := [] } := by
  have h := zebra_traverse_ev b L []
  simp only [List.append_nil] at h
  exact h

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

/-- Variant of `cd_retreat_ev_left` with the cons form expected after `Meta.reduce`. -/
theorem cd_retreat_ev_left_cons (k : Nat) (L R : List Sym) :
    ({ state := some stC, left := rev_zebra k ++ (true :: true :: L), head := false,
       right := R } : Config 6) -[tm]->*
    { state := some stC, left := L, head := true, right := zebra (k + 1) ++ R } := by
  have h := cd_retreat_ev_left k L R
  have heq : (rev_zebra k ++ (ones 2) ++ L : List Sym) = rev_zebra k ++ (true :: true :: L) := by
    show rev_zebra k ++ [true, true] ++ L = rev_zebra k ++ (true :: true :: L)
    rw [List.append_assoc]; rfl
  rw [← heq]
  exact h

/-- Generalized `cd_retreat`: handles `rev_zebra k ++ ones (2 + m)` on the left,
    leaving `ones m` on the left after the retreat. This avoids needing tape
    splitting in the `es` tactic when the goal has merged-ones form. -/
theorem cd_retreat_ev_keep_ones (k m : Nat) (R : List Sym) :
    ({ state := some stC, left := rev_zebra k ++ ones (2 + m), head := false,
       right := R } : Config 6) -[tm]->*
    { state := some stC, left := ones m, head := true, right := zebra (k + 1) ++ R } := by
  have h := cd_retreat_ev_left k (ones m) R
  have heq : (rev_zebra k ++ ones 2 ++ ones m : List Sym) = rev_zebra k ++ ones (2 + m) := by
    rw [List.append_assoc, ones_append]
  rw [← heq]
  exact h

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

/-- EvStep shift for `ones_process` (4 steps processing the 4-ones boundary). -/
theorem ones_process_ev (L T : List Sym) :
    ({ state := some stC, left := L, head := true,
       right := ones 4 ++ T } : Config 6) -[tm]->*
    { state := some stC, left := true :: false :: L, head := false,
      right := zebra 1 ++ T } :=
  ⟨4, ones_process L T⟩

/-! ### 6b. Atomic rules proved via `es` tactic

The es tactic uses Meta.reduce to take concrete TM steps in MetaM, then applies
shift rules to absorb sweep phases. Currently works for simple single-shift cases;
Inc2 etc. need additional algebraic normalization (e.g., `ones (2*(1+m)) = ones 2 ++ ones (2*m)`)
which is not yet automated. -/

-- Test: simplest case — apply one shift rule, no concrete stepping needed.
example (b : Nat) :
    ({ state := some stC, left := [], head := true,
       right := zebra b ++ [true] } : Config 6) -[tm]->*
    { state := some stC, left := rev_zebra b, head := true, right := [true] } := by
  es tm [zebra_traverse_ev]

/-- **Inc2 boundary**: 20 TM steps from `{C, L, true, [1]}` produce
    `{C, [1,0,1,0]++L, false, [1]}`. Independent of `L`.
    Split into 4 chunks of 5 steps for kernel reduction speed. -/
theorem Inc2_boundary (L : List Sym) :
    run tm { state := some stC, left := L, head := true, right := [true] } 20 =
    { state := some stC, left := (true :: false :: true :: false :: L),
      head := false, right := [true] } := by
  rw [show (20 : Nat) = 5 + 5 + 5 + 5 from rfl, run_add, run_add, run_add]
  have h1 : run tm { state := some stC, left := L, head := true, right := [true] } 5 =
            { state := some stC, left := (true :: false :: false :: true :: false :: L),
              head := false, right := [] } := rfl
  rw [h1]
  have h2 : run tm ({ state := some stC, left := (true :: false :: false :: true :: false :: L), head := false, right := [] } : Config 6) 5 =
            { state := some stA, left := L, head := false,
              right := [true, true, true, false, true] } := rfl
  rw [h2]
  have h3 : run tm ({ state := some stA, left := L, head := false, right := [true, true, true, false, true] } : Config 6) 5 =
            { state := some stD, left := (true :: L), head := true,
              right := [true, false, false, true] } := rfl
  rw [h3]
  have h4 : run tm ({ state := some stD, left := (true :: L), head := true, right := [true, false, false, true] } : Config 6) 5 =
            { state := some stC, left := (true :: false :: true :: false :: L),
              head := false, right := [true] } := rfl
  exact h4

/-- EvStep shift rule for `Inc2_boundary`. -/
theorem Inc2_boundary_ev (L : List Sym) :
    ({ state := some stC, left := L, head := true, right := [true] } : Config 6) -[tm]->*
    { state := some stC, left := (true :: false :: true :: false :: L),
      head := false, right := [true] } :=
  ⟨20, Inc2_boundary L⟩

/-- Test 1: single shift via `Inc2_boundary_ev`. -/
example (L : List Sym) :
    ({ state := some stC, left := L, head := true, right := [true] } : Config 6) -[tm]->*
    { state := some stC, left := (true :: false :: true :: false :: L),
      head := false, right := [true] } := by
  es tm [Inc2_boundary_ev]

/-- Test 2: chain zebra_traverse + Inc2_boundary. After traverse, left is
    `rev_zebra b ++ L`, which matches `Inc2_boundary_ev`'s generic `L`. -/
example (b : Nat) (L : List Sym) :
    ({ state := some stC, left := L, head := true,
       right := zebra b ++ [true] } : Config 6) -[tm]->*
    { state := some stC,
      left := (true :: false :: true :: false :: (rev_zebra b ++ L)),
      head := false, right := [true] } := by
  es tm [zebra_traverse_ev, Inc2_boundary_ev]

/-- Test 3: full 3-shift chain to the Inc2 core base target. Requires tape_norm
    folding of the `true::false::` cons prefix into `rev_zebra` after boundary. -/
example (b : Nat) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b ++ [true] } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true,
      right := zebra (b + 3) ++ [true] } := by
  es tm [zebra_traverse_ev, Inc2_boundary_ev, cd_retreat_ev]

/-- Test 4: same as Test 3 but with target `zebra (3 + b)` (non-canonical commutation).
    This requires `esFinish` to handle `Nat.add_comm`-style arithmetic on indices. -/
example (b : Nat) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b ++ [true] } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true,
      right := zebra (3 + b) ++ [true] } := by
  es tm [zebra_traverse_ev, Inc2_boundary_ev, cd_retreat_ev]

/-- Test 5 (esx): trivial halt — state F with head 1 halts in 1 step. -/
example : ∃ k, (run tm ({state := some stF, left := [], head := true,
                         right := []} : Config 6) k).halted := by
  esx tm []

/-- **Inc2 core base, EvStep version** — proved in one `es` line, replacing
    the ~30-line manual phase decomposition of `Inc2_core_base` below. -/
theorem Inc2_core_base_ev (b : Nat) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b ++ [true] } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true,
      right := zebra (3 + b) ++ [true] } := by
  es tm [zebra_traverse_ev, Inc2_boundary_ev, cd_retreat_ev]

/-- EvStep variant of `Inc3_boundary` for the `right := []` case. -/
theorem Inc3_boundary_ev (L : List Sym) :
    ({ state := some stC, left := L, head := true, right := [] } : Config 6) -[tm]->*
    { state := some stC, left := true :: false :: L, head := false, right := [] } :=
  ⟨2, Inc3_boundary L⟩

/-- `nil`-trailing variant of `cd_retreat_ev`: ends with `right := zebra (k+1)`
    rather than `right := zebra (k+1) ++ R`. -/
theorem cd_retreat_ev_nil (k : Nat) :
    ({ state := some stC, left := rev_zebra k ++ ones 2, head := false,
       right := [] } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true, right := zebra (k + 1) } := by
  have h := cd_retreat_ev k []
  simp only [List.append_nil] at h
  exact h

/-- **Inc3 core base, EvStep version** — proved in one `es` line.
    Uses standard `_ev` shifts (no `_nil` variants) thanks to Stage 1 of
    `esTryShift` which retries with `List Sym` parameters assigned to `[]`. -/
theorem Inc3_core_base_ev (b : Nat) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true, right := zebra (2 + b) } := by
  es tm [zebra_traverse_ev, Inc3_boundary_ev, cd_retreat_ev]

/-- **Inc1 core base, EvStep version** — proved in one `es` line, demonstrating
    that with the existing shifts plus Phase 1 (Stages 1+3), `es` can handle
    the variable trailing context `T`. Uses `cd_retreat_ev_keep_ones` to absorb
    the `ones (4+2c)` boundary processing. -/
theorem Inc1_core_base_ev (b : Nat) (T : List Sym) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b ++ (ones 4 ++ T) } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true, right := zebra (3 + b) ++ T } := by
  es tm [zebra_traverse_ev, ones_process_ev, cd_retreat_ev_keep_ones, cd_retreat_ev]

/-- **Inc2 core base**: `{C, ones 2, true, zebra b ++ [true]}` →
    `{C, [], true, zebra (3+b) ++ [true]}` in `4b + 26` steps.
    3 phases: zebra_traverse + boundary + cd_retreat. -/
private theorem Inc2_core_base (b : Nat) :
    run tm { state := some stC, left := ones 2, head := true,
             right := zebra b ++ [true] } (4 * b + 26) =
    { state := some stC, left := [], head := true,
      right := zebra (3 + b) ++ [true] } := by
  -- 4*b + 26 = 2*b + (20 + 2*(b + 2 + 1))
  rw [show 4 * b + 26 = 2 * b + (20 + 2 * (b + 2 + 1)) from by omega, run_add]
  -- Phase 1: zebra_traverse b (ones 2) [true]
  rw [zebra_traverse b (ones 2) [true]]
  -- After phase 1: {C, rev_zebra b ++ ones 2, true, [true]}
  rw [run_add]
  -- Phase 2: Inc2_boundary on left = rev_zebra b ++ ones 2
  rw [Inc2_boundary (rev_zebra b ++ ones 2)]
  -- After phase 2: {C, [t,f,t,f] ++ rev_zebra b ++ ones 2, false, [true]}
  -- = {C, rev_zebra (b+2) ++ ones 2, false, [true]}
  rw [show (true :: false :: true :: false :: (rev_zebra b ++ ones 2) : List Sym) =
          rev_zebra (b + 2) ++ ones 2 from by
        simp [rev_zebra, List.cons_append]]
  -- Phase 3: cd_retreat (b+2) [true]
  rw [cd_retreat (b + 2) [true]]
  -- Result: {C, [], true, zebra (b+3) ++ [true]} = {C, [], true, zebra (3+b) ++ [true]}
  congr 1
  rw [show b + 2 + 1 = 3 + b from by omega]

/-- Chunk 1 of Inc2 boundary: 5 steps from `{C, L, true, [t]}`. -/
private theorem Inc2_b_c1 (L : List Sym) :
    run tm { state := some stC, left := L, head := true, right := [true] } 5 =
    { state := some stC, left := (true :: false :: false :: true :: false :: L),
      head := false, right := [] } := rfl

/-- Chunk 2 of Inc2 boundary: next 5 steps. -/
private theorem Inc2_b_c2 (L : List Sym) :
    run tm ({ state := some stC, left := (true :: false :: false :: true :: false :: L),
              head := false, right := [] } : Config 6) 5 =
    { state := some stA, left := L, head := false,
      right := [true, true, true, false, true] } := rfl

/-- Chunk 3 of Inc2 boundary: next 5 steps. -/
private theorem Inc2_b_c3 (L : List Sym) :
    run tm ({ state := some stA, left := L, head := false,
              right := [true, true, true, false, true] } : Config 6) 5 =
    { state := some stD, left := (true :: L), head := true,
      right := [true, false, false, true] } := rfl

/-- Chunk 4 of Inc2 boundary: final 5 steps. -/
private theorem Inc2_b_c4 (L : List Sym) :
    run tm ({ state := some stD, left := (true :: L), head := true,
              right := [true, false, false, true] } : Config 6) 5 =
    { state := some stC, left := (true :: false :: true :: false :: L),
      head := false, right := [true] } := rfl

/-- Helper: during the 20-step Inc2 boundary, left is nonempty at every intermediate step. -/
private theorem Inc2_boundary_left_ne (L : List Sym) (hL : L ≠ []) :
    ∀ k, k < 20 →
      (run tm { state := some stC, left := L, head := true, right := [true] } k).left ≠ [] := by
  intro k hk
  -- Decompose k into chunk index q (0..3) and offset r (0..4)
  by_cases h0 : k < 5
  · -- Chunk 0: k ∈ [0,5). Left starts as L (k=0), grows in cons form (k=1..4).
    have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases this with rfl|rfl|rfl|rfl|rfl
    · exact hL
    · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
    · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
    · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
    · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
  · by_cases h1 : k < 10
    · -- Chunk 1: k ∈ [5,10). Use Inc2_b_c1 to jump to step 5.
      rw [show k = 5 + (k - 5) from by omega, run_add, Inc2_b_c1]
      have : k - 5 = 0 ∨ k - 5 = 1 ∨ k - 5 = 2 ∨ k - 5 = 3 ∨ k - 5 = 4 := by omega
      rcases this with h|h|h|h|h <;> rw [h]
      · (try simp only [run]); exact List.cons_ne_nil _ _
      · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
      · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
      · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
      · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
    · by_cases h2 : k < 15
      · -- Chunk 2: k ∈ [10,15). Use Inc2_b_c1 + Inc2_b_c2.
        rw [show k = 5 + 5 + (k - 10) from by omega, run_add, run_add, Inc2_b_c1, Inc2_b_c2]
        have : k - 10 = 0 ∨ k - 10 = 1 ∨ k - 10 = 2 ∨ k - 10 = 3 ∨ k - 10 = 4 := by omega
        rcases this with h|h|h|h|h <;> rw [h]
        · exact hL  -- step 10: left = L
        · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
        · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
        · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
        · (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
      · -- Chunk 3: k ∈ [15,20). Use chunks 1, 2, 3.
        rw [show k = 5 + 5 + 5 + (k - 15) from by omega, run_add, run_add, run_add,
            Inc2_b_c1, Inc2_b_c2, Inc2_b_c3]
        have : k - 15 = 0 ∨ k - 15 = 1 ∨ k - 15 = 2 ∨ k - 15 = 3 ∨ k - 15 = 4 := by omega
        rcases this with h|h|h|h|h <;> rw [h]
        · -- step 15: left = t :: L
          (try simp only [run]); exact List.cons_ne_nil _ _
        · -- step 16: left = L (back to L)
          (try simp only [run, step, listHead, listTail]); exact hL
        · -- step 17: left = f :: L
          (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
        · -- step 18: left = t :: f :: L
          (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _
        · -- step 19: left = f :: t :: f :: L
          (try simp only [run, step, listHead, listTail]); exact List.cons_ne_nil _ _

/-- **Inc2 left nonemptiness**: left tape stays nonempty during the `4b+26` steps. -/
private theorem Inc2_left_ne (b : Nat) :
    ∀ m, m < 4 * b + 26 →
      (run tm { state := some stC, left := ones 2, head := true,
                right := zebra b ++ [true] } m).left ≠ [] := by
  intro m hm
  by_cases hm1 : m < 2 * b
  · exact zebra_traverse_left_ne b (ones 2) [true]
      (by simp [ones, repeatSym]) m hm1
  · by_cases hm2 : m < 2 * b + 20
    · rw [show m = 2 * b + (m - 2 * b) from by omega, run_add]
      rw [zebra_traverse b (ones 2) [true]]
      have hne : rev_zebra b ++ ones 2 ≠ ([] : List Sym) :=
        List.append_ne_nil_of_right_ne_nil _ (by simp [ones, repeatSym])
      exact Inc2_boundary_left_ne (rev_zebra b ++ ones 2) hne (m - 2 * b) (by omega)
    · rw [show m = (2 * b + 20) + (m - (2 * b + 20)) from by omega, run_add, run_add]
      rw [zebra_traverse b (ones 2) [true]]
      rw [Inc2_boundary (rev_zebra b ++ ones 2)]
      rw [show (true :: false :: true :: false :: (rev_zebra b ++ ones 2) : List Sym) =
              rev_zebra (b + 2) ++ ones 2 from by
            simp [rev_zebra, List.cons_append]]
      exact cd_retreat_left_ne' (b + 2) [true] (m - (2 * b + 20)) (by omega)

/-- **Inc2**: `S2(1+a, b) →* S2(a, 3+b)`. Proved via `Inc2_core_base` + `run_left_append`. -/
theorem Inc2 (a b : Nat) : S2 (1 + a) b -[tm]->* S2 a (3 + b) := by
  have hcore := Inc2_core_base b
  have hne := Inc2_left_ne b
  have hleft := run_left_append tm
    { state := some stC, left := ones 2, head := true, right := zebra b ++ [true] }
    (ones (2 * a)) (4 * b + 26) hne
  rw [hcore] at hleft
  simp only [List.nil_append] at hleft
  refine ⟨4 * b + 26, ?_⟩
  show run tm (S2 (1 + a) b) (4 * b + 26) = S2 a (3 + b)
  simp only [S2]
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  exact hleft

/-- **LOv1 core** (c=0): the full LOv1 computation without right tail.
    8 phases: zebra_traverse + CBED + cd_pair_retreat + CD_DA + AB + BEDA + BED + cd_final.
    Total: 2b + 4 + 2(b+1) + 2 + 1 + 4(b+2) + 3 + 2 = 8b + 22. -/
theorem LOv1_core (b : Nat) (T : List Sym) :
    run tm { state := some stC, left := [], head := true,
             right := zebra b ++ ((ones 6) ++ T) } (22 + 8 * b) =
    { state := some stC, left := ones (4 + 2 * b), head := true,
      right := zebra 2 ++ T } := by
  -- Phase 1: zebra_traverse (2b steps)
  rw [show 22 + 8 * b = 2 * b + (4 + (2 * (b + 1) + (2 + (1 + (4 * (b + 2) + (3 + 2)))))) from by omega,
      run_add, zebra_traverse b [] ((ones 6) ++ T)]
  simp only [List.append_nil]
  -- Phase 2: CBED_forward (4 steps) — processes first 3 ones
  rw [show ((ones 6) ++ T : List Sym) = true :: true :: true :: (true :: true :: true :: T) from rfl,
      run_add, CBED_forward (rev_zebra b) (true :: true :: true :: T)]
  rw [show (true :: false :: rev_zebra b : List Sym) = rev_zebra (b + 1) from by
        simp [rev_zebra]]
  -- Phase 3: cd_pair_retreat (2(b+1) steps) — retreat through rev_zebra(b+1)
  rw [run_add, cd_pair_retreat (b + 1) (false :: true :: true :: true :: T)]
  -- After: {C, [], false, zebra(b+1) ++ [0,1,1,1,T]}
  rw [show (false :: true :: true :: true :: T : List Sym) = zebra 1 ++ (ones 2 ++ T) from rfl,
      ← List.append_assoc, zebra_append]
  -- Phase 4: CD_DA_empty (2 steps)
  rw [run_add, CD_DA_empty (zebra (b + 2) ++ (ones 2 ++ T))]
  -- Phase 5: AB_start (1 step)
  rw [run_add, AB_start (zebra (b + 2) ++ (ones 2 ++ T))]
  -- Phase 6: BEDA_traverse through zebra(b+2)
  rw [run_add, BEDA_traverse (b + 2) [true] (ones 2 ++ T)]
  rw [show ones (2 * (b + 2)) ++ [true] = ones (2 * b + 5) from by
        rw [show 2 * (b + 2) = 2 * b + 4 from by omega, ← ones_append]
        simp [ones, repeatSym],
      show (true :: (ones 2 ++ T) : List Sym) = true :: true :: true :: T from rfl]
  -- Phase 7: BED_terminal with tail T
  rw [run_add, BED_terminal (ones (2 * b + 5)) T]
  rw [show (true :: ones (2 * b + 5) : List Sym) = true :: true :: ones (2 * b + 4) from by
        simp [ones_succ, show 2 * b + 5 = (2 * b + 4) + 1 from by omega]]
  -- Phase 8: cd_final_ones with tail T
  rw [cd_final_ones (2 * b + 4) T]
  rw [show (false :: true :: false :: true :: T : List Sym) = zebra 2 ++ T from rfl,
      show 2 * b + 4 = 4 + 2 * b from by omega]

/-- **LOv1**: `S1(0, b, 3+c) →* S1(2+b, 2, c)`. -/
theorem LOv1 (b c : Nat) : S1 0 b (3 + c) -[tm]->* S1 (2 + b) 2 c := by
  -- Use LOv1_core with T = ones(2c) ++ [false, true] (no run_right_append needed)
  have hcore := LOv1_core b (ones (2 * c) ++ [false, true])
  refine ⟨22 + 8 * b, ?_⟩
  show run tm (S1 0 b (3 + c)) (22 + 8 * b) = S1 (2 + b) 2 c
  simp only [S1]
  rw [show 2 * 0 = 0 from rfl, show 2 * (3 + c) = 6 + 2 * c from by omega,
      show 2 * (2 + b) = 4 + 2 * b from by omega]
  simp only [ones_zero, List.append_assoc]
  rw [← ones_append (a := 6) (b := 2 * c)]
  exact hcore

/-- **Ov2 finalize**: 5 final steps from B with 5+ ones on left and `[t,t]` right
    yield C with 4+ ones and `[f,t,f]` right. Independent of the rest of the left tape. -/
theorem Ov2_finalize (L : List Sym) :
    run tm ({ state := some stB,
              left := (true :: true :: true :: true :: true :: L),
              head := true, right := [true, true] } : Config 6) 5 =
    { state := some stC,
      left := (true :: true :: true :: true :: L),
      head := true, right := [false, true, false] } := rfl

/-- **Ov2_raw**: `S2 0 b →* {C, ones (4+2b), true, [f,t,f]}` in `40+8b` steps.
    7-phase decomposition (similar to `LOv1_core` but with different boundary). -/
private theorem Ov2_raw (b : Nat) :
    (S2 0 b : Config 6) -[tm]->*
    { state := some stC, left := ones (4 + 2 * b), head := true,
      right := [false, true, false] } := by
  refine ⟨40 + 8 * b, ?_⟩
  show run tm (S2 0 b) (40 + 8 * b) = _
  simp only [S2]
  rw [show (2 * 0 : Nat) = 0 from rfl, ones_zero]
  -- Step count: 40 + 8b = 2*b + (20 + (2*(b+2) + (2 + (1 + (4*(b+2) + 5)))))
  rw [show 40 + 8 * b = 2 * b + (20 + (2 * (b + 2) + (2 + (1 + (4 * (b + 2) + 5))))) from by omega]
  rw [run_add]
  -- Phase 0: zebra_traverse b [] [true]
  rw [zebra_traverse b [] [true]]
  simp only [List.append_nil]
  rw [run_add]
  -- Phase 1: Inc2_boundary (rev_zebra b)
  rw [Inc2_boundary (rev_zebra b)]
  -- After phase 1: left = [t,f,t,f] ++ rev_zebra b = rev_zebra (b+2)
  rw [show (true :: false :: true :: false :: rev_zebra b : List Sym) = rev_zebra (b + 2) from by
        simp [rev_zebra]]
  rw [run_add]
  -- Phase 2: cd_pair_retreat (b+2) [true]
  rw [cd_pair_retreat (b + 2) [true]]
  rw [run_add]
  -- Phase 3: CD_DA_empty (zebra (b+2) ++ [true])
  rw [CD_DA_empty (zebra (b + 2) ++ [true])]
  rw [run_add]
  -- Phase 4: AB_start (zebra (b+2) ++ [true])
  -- The right is now `true :: true :: zebra (b+2) ++ [true]`, AB_start expects this form
  rw [AB_start (zebra (b + 2) ++ [true])]
  rw [run_add]
  -- Phase 5: BEDA_traverse (b+2) [true] [true]
  -- After AB_start: {B, [true], true, true :: zebra (b+2) ++ [true]}
  -- BEDA_traverse expects: {B, L, true, true :: zebra n ++ R}
  rw [BEDA_traverse (b + 2) [true] [true]]
  -- After BEDA_traverse: {B, ones (2*(b+2)) ++ [true], true, true :: [true]}
  -- = {B, ones (4+2b) ++ [true], true, [true, true]}
  -- Rewrite ones (4+2b) ++ [true] as ones (5+2b) for finalize lemma
  rw [show (ones (2 * (b + 2)) ++ [true] : List Sym) =
          true :: true :: true :: true :: true :: ones (2 * b) from by
        rw [show ([true] : List Sym) = ones 1 from rfl, ones_append]
        rw [show 2 * (b + 2) + 1 = 5 + 2 * b from by omega]
        show ones (5 + 2 * b) = _
        rw [show (5 + 2 * b : Nat) = 2 * b + 1 + 1 + 1 + 1 + 1 from by omega]
        simp [ones_succ]]
  -- Phase 6: Ov2_finalize (ones (2*b))
  rw [Ov2_finalize (ones (2 * b))]
  -- After phase 6: {C, [t,t,t,t] ++ ones (2*b), true, [f,t,f]}
  -- = {C, ones (4 + 2*b), true, [f,t,f]}
  congr 1
  show (true :: true :: true :: true :: ones (2 * b) : List Sym) = ones (4 + 2 * b)
  rw [show (4 + 2 * b : Nat) = 4 + 2 * b from rfl]
  simp [ones_succ, show 4 + 2 * b = (((2 * b + 1) + 1) + 1) + 1 from by omega]

/-- Boundary step for Inc3_absorb: like `Inc3_boundary` but with `[false]` on right.
    Two steps: C reads true (writes 0, moves R), then B reads false (writes 1, moves R). -/
theorem Inc3_absorb_boundary (L : List Sym) :
    run tm { state := some stC, left := L, head := true, right := [false] } 2 =
    { state := some stC, left := true :: false :: L, head := false, right := [] } := rfl

/-- EvStep variant of `Inc3_absorb_boundary`. -/
theorem Inc3_absorb_boundary_ev (L : List Sym) :
    ({ state := some stC, left := L, head := true, right := [false] } : Config 6) -[tm]->*
    { state := some stC, left := true :: false :: L, head := false, right := [] } :=
  ⟨2, Inc3_absorb_boundary L⟩

/-- **Inc3_absorb core base, EvStep version** — proved in one `es` line. -/
theorem Inc3_absorb_core_base_ev (b : Nat) :
    ({ state := some stC, left := ones 2, head := true,
       right := zebra b ++ [false] } : Config 6) -[tm]->*
    { state := some stC, left := [], head := true, right := zebra (2 + b) } := by
  es tm [zebra_traverse_ev, Inc3_absorb_boundary_ev, cd_retreat_ev]

/-- Inc3_absorb core (a=0): `{C, ones 2, true, zebra b ++ [false]}` → `{C, [], true, zebra (2+b)}`
    in `4b + 6` steps. Same count as Inc3, with [false] absorbed by the boundary. -/
theorem Inc3_absorb_core_base (b : Nat) :
    run tm { state := some stC, left := (ones 2), head := true,
             right := zebra b ++ [false] } (4 * b + 6) =
    { state := some stC, left := [], head := true, right := zebra (2 + b) } := by
  rw [show 4 * b + 6 = 2 * b + (2 + 2 * (b + 1 + 1)) from by omega, run_add]
  rw [zebra_traverse b (ones 2) [false]]
  rw [run_add]
  rw [Inc3_absorb_boundary (rev_zebra b ++ (ones 2))]
  rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
          rev_zebra (b + 1) ++ (ones 2) from by
        simp [rev_zebra, List.cons_append]]
  rw [cd_retreat (b + 1) []]
  congr 1
  show zebra (b + 1 + 1) ++ ([] : List Sym) = zebra (2 + b)
  simp [show b + 1 + 1 = 2 + b from by omega]

/-- Left nonemptiness for Inc3_absorb core. -/
private theorem Inc3_absorb_left_ne (b : Nat) :
    ∀ m, m < 4 * b + 6 →
      (run tm { state := some stC, left := (ones 2), head := true,
                right := zebra b ++ [false] } m).left ≠ [] := by
  intro m hm
  by_cases hm1 : m < 2 * b
  · exact zebra_traverse_left_ne b (ones 2) [false] (by simp [ones, repeatSym]) m hm1
  · by_cases hm2 : m < 2 * b + 2
    · -- Phase 2: Inc3_absorb_boundary (2 steps). Left grows.
      rw [show m = 2 * b + (m - 2 * b) from by omega, run_add]
      rw [zebra_traverse b (ones 2) [false]]
      have : m - 2 * b = 0 ∨ m - 2 * b = 1 := by omega
      rcases this with h | h <;> rw [h] <;>
        simp [run, step, listHead, listTail, ones, repeatSym] <;>
        exact List.cons_ne_nil _ _
    · -- Phase 3: cd_retreat on rev_zebra(b+1) ++ ones(2).
      rw [show m = (2 * b + 2) + (m - (2 * b + 2)) from by omega, run_add,
          show (2 * b + 2 : Nat) = 2 * b + 2 from rfl, run_add]
      rw [zebra_traverse b (ones 2) [false]]
      rw [Inc3_absorb_boundary (rev_zebra b ++ (ones 2))]
      rw [show (true :: false :: (rev_zebra b ++ (ones 2)) : List Sym) =
              rev_zebra (b + 1) ++ (ones 2) from by
            simp [rev_zebra, List.cons_append]]
      exact cd_retreat_left_ne' (b + 1) [] (m - (2 * b + 2)) (by omega)

/-- **Inc3_absorb**: lifts Inc3_absorb_core_base via run_left_append. -/
theorem Inc3_absorb (a b : Nat) :
    ({ state := some stC, left := ones (2 * (1 + a)), head := true,
       right := zebra b ++ [false] } : Config 6) -[tm]->* S3 a (2 + b) := by
  have hcore := Inc3_absorb_core_base b
  have hne := Inc3_absorb_left_ne b
  have hleft := run_left_append tm
    { state := some stC, left := ones 2, head := true, right := zebra b ++ [false] }
    (ones (2 * a)) (4 * b + 6) hne
  rw [hcore] at hleft
  simp only [List.nil_append] at hleft
  refine ⟨4 * b + 6, ?_⟩
  show run tm { state := some stC, left := ones (2 * (1 + a)), head := true,
                right := zebra b ++ [false] } (4 * b + 6) = S3 a (2 + b)
  simp only [S3]
  rw [show 2 * (1 + a) = 2 + 2 * a from by omega, ← ones_append]
  exact hleft

/-! ### Helper lemmas for Ov3 -/

/-- 2-step `Ov3_grow_rev`: `{C, rev_zebra k, t, []}` → `{C, rev_zebra (k+1), f, []}`. -/
theorem Ov3_grow_rev (k : Nat) :
    run tm ({state := some stC, left := rev_zebra k, head := true, right := []} : Config 6) 2 =
    {state := some stC, left := rev_zebra (k+1), head := false, right := []} := rfl

/-- 4-step `BED1`: `{B, L, t, [t]}` → `{B, [t,t]++L, t, []}`. -/
theorem BED1 (L : List Sym) :
    run tm ({state := some stB, left := L, head := true, right := [true]} : Config 6) 4 =
    {state := some stB, left := (true :: true :: L), head := true, right := []} := rfl

/-- 4-step `BEFC`: `{B, L, t, []}` → `{C, [t,f,f,t]++L, f, []}`. -/
theorem BEFC (L : List Sym) :
    run tm ({state := some stB, left := L, head := true, right := []} : Config 6) 4 =
    {state := some stC, left := (true :: false :: false :: true :: L), head := false, right := []} := rfl

/-- 4-step `CDA_4step`: `{C, [t,f,f,t]++L, f, []}` → `{A, L, head=listHead L false, [t,t,f,t]}`,
    only if listHead L false has the expected value (depends on L's first element).
    Specialized for L = ones n with n > 0: head = true. -/
theorem CDA_4step_ones (n : Nat) :
    run tm ({state := some stC, left := (true :: false :: false :: true :: ones (n+1)),
             head := false, right := []} : Config 6) 4 =
    {state := some stA, left := ones (n+1), head := true, right := [true, true, false, true]} := rfl

/-- 6-step `Ov3_finalize`: combines (A,f)→(B,1,R) + 5-step BED→C cleanup.
    Generic form independent of remaining tape. -/
theorem Ov3_finalize (R : List Sym) :
    run tm ({state := some stA, left := [], head := false,
             right := [true, true, true, true, true] ++ R} : Config 6) 6 =
    {state := some stC, left := [], head := true,
     right := [false, true, false, true, true] ++ R} := rfl

/-- **Ov3**: `S3 0 b →* S1 0 2 (2+b)` in `35 + 10b` steps. 13-phase decomposition. -/
theorem Ov3 (b : Nat) : S3 0 b -[tm]->* S1 0 2 (2 + b) := by
  refine ⟨35 + 10 * b, ?_⟩
  show run tm (S3 0 b) (35 + 10 * b) = S1 0 2 (2 + b)
  -- Set up explicit start and end forms
  have hS3 : (S3 0 b : Config 6) = ⟨some stC, [], true, zebra b⟩ := by simp [S3]
  have hS1 : (S1 0 2 (2 + b) : Config 6) =
             ⟨some stC, [], true, zebra 2 ++ ones (4 + 2 * b) ++ [false, true]⟩ := by
    simp [S1]; congr 1; rw [show 2 * (2 + b) = 4 + 2 * b from by omega]
  rw [hS3, hS1]
  -- Total step count decomposition
  have hcount : 35 + 10 * b =
    2 * b + (2 + ((2 * b + 2) + (2 + (1 + (4 + (4 * b + (4 + (4 + (4 + ((2 * b + 6) + 6))))))))))
    := by omega
  rw [hcount]
  -- Phase 0: zebra_traverse b [] []
  rw [run_add, show (zebra b : List Sym) = zebra b ++ [] from by simp,
      zebra_traverse b [] [], show (rev_zebra b ++ ([] : List Sym)) = rev_zebra b from by simp]
  -- Phase 1: Ov3_grow_rev b
  rw [run_add, Ov3_grow_rev b]
  -- Phase 2: cd_pair_retreat (b+1) []
  rw [run_add, show (2 * b + 2 : Nat) = 2 * (b + 1) from by omega]
  rw [cd_pair_retreat (b + 1) [],
      show (zebra (b + 1) ++ ([] : List Sym)) = zebra (b + 1) from by simp]
  -- Phase 3: CD_DA_empty (zebra (b+1))
  rw [run_add, CD_DA_empty (zebra (b + 1))]
  -- Phase 4: AB_start (zebra (b+1))
  rw [run_add, AB_start (zebra (b + 1))]
  -- Phase 5: BEDA_pair [t] (zebra b)
  -- Need: t :: zebra (b+1) = t :: f :: t :: zebra b
  rw [run_add, show (true :: zebra (b + 1) : List Sym) = true :: false :: true :: zebra b from rfl]
  rw [BEDA_pair [true] (zebra b)]
  -- Phase 6: BEDA_traverse b [t,t,t] []
  rw [run_add, show (true :: true :: ([true] : List Sym)) = [true, true, true] from rfl,
      show (true :: zebra b : List Sym) = true :: (zebra b ++ []) from by simp]
  rw [BEDA_traverse b [true, true, true] []]
  -- Phase 7: BED1 (ones (2b+3))
  rw [run_add, show (ones (2 * b) ++ [true, true, true] : List Sym) = ones (2 * b + 3) from by
        rw [show ([true, true, true] : List Sym) = ones 3 from rfl, ones_append],
      show (true :: ([] : List Sym)) = [true] from rfl]
  rw [BED1 (ones (2 * b + 3))]
  -- Phase 8: BEFC. Need {B, ones (2b+5), t, []}
  rw [run_add, show (true :: true :: ones (2 * b + 3) : List Sym) = ones (2 * b + 5) from rfl]
  rw [BEFC (ones (2 * b + 5))]
  -- Phase 9: CDA_4step_ones (2b+4) — needs ones ((2b+4)+1) = ones (2b+5)
  rw [run_add, show (true :: false :: false :: true :: ones (2 * b + 5) : List Sym) =
                 (true :: false :: false :: true :: ones ((2 * b + 4) + 1)) from rfl]
  rw [CDA_4step_ones (2 * b + 4)]
  -- Phase 10: A_shift (2b+5) [] [t,t,f,t]
  -- A_shift signature: A_shift k L R: {A, ones k ++ L, t, R} (k+1) → {A, listTail L, listHead L false, ones (k+1) ++ R}
  -- We have {A, ones ((2*b+4)+1), t, [t,t,f,t]} = {A, ones (2*b+5), t, [t,t,f,t]}
  -- which is {A, ones (2*b+5) ++ [], t, [t,t,f,t]}
  rw [run_add, show (ones ((2 * b + 4) + 1) : List Sym) = ones (2 * b + 5) ++ [] from by simp]
  rw [A_shift (2 * b + 5) [] [true, true, false, true]]
  simp only [listTail, listHead]
  -- After A_shift: {A, [], false, ones (2b+5+1) ++ [t,t,f,t]} = {A, [], false, ones (2b+6) ++ [t,t,f,t]}
  -- For Ov3_finalize R, need right = [t,t,t,t,t] ++ R'.
  -- ones (2*b+6) ++ [t,t,f,t] = ones 5 ++ ones (2*b+1) ++ [t,t,f,t] = [t,t,t,t,t] ++ (ones (2*b+1) ++ [t,t,f,t])
  rw [show (ones (2 * b + 5 + 1) ++ [true, true, false, true] : List Sym) =
          [true, true, true, true, true] ++ (ones (2 * b + 1) ++ [true, true, false, true]) from by
        rw [show 2 * b + 5 + 1 = 5 + (2 * b + 1) from by omega, ← ones_append]
        rw [show (ones 5 : List Sym) = [true, true, true, true, true] from rfl, List.append_assoc]]
  rw [Ov3_finalize (ones (2 * b + 1) ++ [true, true, false, true])]
  -- Result: {C, [], t, [f,t,f,t,t] ++ (ones (2b+1) ++ [t,t,f,t])}
  -- Need: {C, [], t, zebra 2 ++ ones (4+2b) ++ [f,t]}
  congr 1
  -- Prove list equality via ones algebra
  show ([false, true, false, true, true] ++ (ones (2 * b + 1) ++ [true, true, false, true]) : List Sym) =
       zebra 2 ++ ones (4 + 2 * b) ++ [false, true]
  rw [show ([false, true, false, true, true] : List Sym) = zebra 2 ++ ones 1 from rfl,
      show ([true, true, false, true] : List Sym) = ones 2 ++ [false, true] from rfl]
  rw [show (zebra 2 ++ ones 1 ++ (ones (2 * b + 1) ++ (ones 2 ++ [false, true])) : List Sym) =
          zebra 2 ++ (ones 1 ++ ones (2 * b + 1) ++ ones 2) ++ [false, true] from by
        simp]
  rw [ones_append, ones_append]
  rw [show (1 + (2 * b + 1) + 2 : Nat) = 4 + 2 * b from by omega]

/-! ### Phase decomposition for `ROv1_1_0_halts`

The halting trajectory of `S1(0, b, 1)` is `64 + 8*b` TM steps. We decompose:

  1. **`zebra_traverse(b)`** — `2b` steps. Uses the existing lemma.
  2. **`phase_a_boundary`** — fixed `22` steps that process the right boundary
     `[t, t, f, t]` regardless of the underlying left tape `L`. Built via
     `run_left_append` from a 21-step concrete base.
  3. **`phase_b_step1`** — `6` generic steps (`:= rfl`).
  4. **`phase_b_step2`** — `14` generic steps (`5 + 9` chunks).
  5. **`rev_zebra_consume`** — `2b` steps via `shift_rule_L_lift` (Phase 1
     tactic work): lifts a trivial 2-step 1-iteration `{C, [t,f]++L, f, R} →{2}
     {C, L, f, [f,t]++R}` (provable by `rfl`) to `2b` steps that consume all
     `rev_zebra b` from the left.
  6. **`phase_b_setup`** — `4` generic steps (`rfl`).
  7. **`zebra_consume_R`** — `4b` steps via `shift_rule_R_lift`: lifts a
     trivial 4-step 1-iteration on the right.
  8. **`phase_b_tail`** — `18` steps via `run_left_append` from a
     `decide`-based concrete base.

Total: `2b + 22 + 6 + 14 + 2b + 4 + 4b + 18 = 64 + 8b`. ✓
-/

/-- 21-step base case for `phase_a_boundary`: from `{B, [f], t, [t, f, t]}`
    reach `{A, [], f, ones 7 ++ [f, t]}`. Proved by `decide`. -/
private theorem phase_a_base :
    run tm ({state := some stB, left := [false], head := true,
             right := [true, false, true]} : Config 6) 21 =
    { state := some stA, left := [], head := false,
      right := [true, true, true, true, true, true, true, false, true] } := by
  decide

/-- Left stays non-empty during the 21-step `phase_a_base` trajectory. Proved
    by `decide` (Lean's `Nat.decBallLT` handles bounded `∀ m, m < 21 → ...`
    decidably for each concrete-config step result). -/
private theorem phase_a_base_left_ne :
    ∀ m, m < 21 →
      (run tm ({state := some stB, left := [false], head := true,
                right := [true, false, true]} : Config 6) m).left ≠ [] := by
  decide

/-- Lifted version of `phase_a_base` with arbitrary tail `L` appended to the left. -/
private theorem phase_a_lift (L : List Sym) :
    run tm ({state := some stB, left := [false] ++ L, head := true,
             right := [true, false, true]} : Config 6) 21 =
    { state := some stA, left := L, head := false,
      right := [true, true, true, true, true, true, true, false, true] } := by
  have h := run_left_append tm
    ({state := some stB, left := [false], head := true,
      right := [true, false, true]} : Config 6) L 21 phase_a_base_left_ne
  rw [phase_a_base] at h
  simp only [List.nil_append] at h
  exact h

/-- First step of `phase_a_boundary`: `{C, L, t, [t,t,f,t]}` advances to
    `{B, f::L, t, [t,f,t]}` in one step. Generic over `L`. -/
private theorem phase_a_step1 (L : List Sym) :
    step tm ({state := some stC, left := L, head := true,
              right := [true, true, false, true]} : Config 6) =
    { state := some stB, left := [false] ++ L, head := true, right := [true, false, true] } :=
  rfl

/-- **Phase A boundary**: 22 fixed steps from `{C, L, t, [t, t, f, t]}` to
    `{A, L, f, ones 7 ++ [f, t]}`, generic over `L`. Combines `phase_a_step1`
    (1 step) + `phase_a_lift` (21 steps via `run_left_append`). -/
theorem phase_a_boundary (L : List Sym) :
    run tm ({state := some stC, left := L, head := true,
             right := [true, true, false, true]} : Config 6) 22 =
    { state := some stA, left := L, head := false,
      right := [true, true, true, true, true, true, true, false, true] } := by
  rw [show (22 : Nat) = 1 + 21 from rfl, run_add, run_one tm]
  rw [phase_a_step1 L]
  exact phase_a_lift L

/-- Combine `zebra_traverse` and `phase_a_boundary` into the full Phase A
    of ROv1: `(2b + 22)` steps from `S1(0, b, 1)` to
    `{A, rev_zebra b, f, ones 7 ++ [f, t]}`. -/
theorem ROv1_phase_a (b : Nat) :
    run tm (S1 0 b 1) (2 * b + 22) =
    { state := some stA, left := rev_zebra b, head := false,
      right := [true, true, true, true, true, true, true, false, true] } := by
  rw [show (S1 0 b 1) =
        ({state := some stC, left := [], head := true,
          right := zebra b ++ [true, true, false, true]} : Config 6) from by
        simp [S1, ones, repeatSym]]
  rw [run_add]
  rw [zebra_traverse b [] [true, true, false, true]]
  simp only [List.append_nil]
  exact phase_a_boundary (rev_zebra b)

/-- **Phase B step 1**: 6 fixed steps from `{A, L, f, ones 7 ++ [f, t]}`
    (the Phase A end state) to `{C, L, t, [f, t, f, t, t, t, t, f, t]}`.
    Generic over `L`. The 6 steps include both R and L direction operations,
    but all `listHead` reads come from cells written during the trajectory,
    so `L` is preserved at the bottom. Provable by `:= rfl`. -/
theorem phase_b_step1 (L : List Sym) :
    run tm ({state := some stA, left := L, head := false,
             right := [true, true, true, true, true, true, true, false, true]} : Config 6) 6 =
    { state := some stC, left := L, head := true,
      right := [false, true, false, true, true, true, true, false, true] } := rfl

/-- **Phase B step 2**: 14 more fixed steps from `{C, L, t, [f, t, f, t, t, t, t, f, t]}`
    (the result of `phase_b_step1`) to `{C, L, f, [f, t, f, t, f, t, f, f, t]}`.
    Generic over `L`. Proved by splitting into two sub-chunks of 5 and 9 steps
    (both `:= rfl` chunks) to avoid kernel timeouts on large single-step runs. -/
theorem phase_b_step2 (L : List Sym) :
    run tm ({state := some stC, left := L, head := true,
             right := [false, true, false, true, true, true, true, false, true]} : Config 6) 14 =
    { state := some stC, left := L, head := false,
      right := [false, true, false, true, false, true, false, false, true] } := by
  rw [show (14 : Nat) = 5 + 9 from rfl, run_add]
  have h1 : run tm ({state := some stC, left := L, head := true, right := [false, true, false, true, true, true, true, false, true]} : Config 6) 5 = ({state := some stB, left := (false :: true :: false :: true :: false :: L), head := true, right := [true, true, false, true]} : Config 6) := rfl
  rw [h1]
  have h2 : run tm ({state := some stB, left := (false :: true :: false :: true :: false :: L), head := true, right := [true, true, false, true]} : Config 6) 9 = ({state := some stC, left := L, head := false, right := [false, true, false, true, false, true, false, false, true]} : Config 6) := rfl
  exact h2

/-- Combined Phase A + Phase B steps 1 and 2: `2b + 42` steps from `S1(0, b, 1)`
    to `{C, rev_zebra b, f, [f, t, f, t, f, t, f, f, t]}`. This is the longest
    L-preserving sub-trajectory of ROv1; after this point the trajectory
    diverges based on the specific value of `b` because the subsequent
    L-direction steps would need to read into `rev_zebra b`. -/
theorem ROv1_pre_divergence (b : Nat) :
    run tm (S1 0 b 1) (2 * b + 42) =
    { state := some stC, left := rev_zebra b, head := false,
      right := [false, true, false, true, false, true, false, false, true] } := by
  rw [show 2 * b + 42 = (2 * b + 22) + (6 + 14) from by omega, run_add, ROv1_phase_a]
  rw [run_add, phase_b_step1 (rev_zebra b)]
  exact phase_b_step2 (rev_zebra b)

/-! ### Post-divergence phase B using `shift_rule_L_lift` / `shift_rule_R_lift`

The pre-divergence trajectory preserves `rev_zebra b` at the bottom of the
left. The post-divergence part consumes it via two successive shift-rule
applications:

1. **`rev_zebra_consume`** (`2b` steps, via `shift_rule_L_lift`):
   `{C, rev_zebra b, f, R} → {C, [], f, zebra b ++ R}`

2. **Setup** (4 concrete steps):
   `{C, [], f, zebra b ++ R} → {E, ones 2, t, zebra b ++ R}`

3. **`zebra_consume_R`** (`4b` steps, via `shift_rule_R_lift`):
   `{E, ones 2, t, zebra b ++ R} → {E, ones (2+2b), t, R}`

4. **Final tail** (18 steps, via `run_left_append` from a `decide`d base):
   `{E, ones (2+2b), t, R₀} → halted`

Total: `2b + 42` (pre-divergence) `+ 2b + 4 + 4b + 18 = 6b + 22` (post-divergence)
     = `64 + 8b` as expected. -/

/-- `rev_zebra b = listPow [true, false] b`. -/
theorem rev_zebra_eq_listPow (b : Nat) : rev_zebra b = listPow [true, false] b := by
  induction b with
  | zero => rfl
  | succ b ih => show true :: false :: rev_zebra b = [true, false] ++ listPow [true, false] b
                 rw [ih]; rfl

/-- `zebra b = listPow [false, true] b`. -/
theorem zebra_eq_listPow (b : Nat) : zebra b = listPow [false, true] b := by
  induction b with
  | zero => rfl
  | succ b ih => show false :: true :: zebra b = [false, true] ++ listPow [false, true] b
                 rw [ih]; rfl

/-- `listPow [true, true] b = ones (2*b)`. -/
theorem listPow_tt_eq_ones (b : Nat) : listPow [true, true] b = ones (2 * b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show [true, true] ++ listPow [true, true] b = ones (2 * (b + 1))
    rw [ih]
    show true :: true :: ones (2 * b) = ones (2 * (b + 1))
    rw [show 2 * (b + 1) = 2 * b + 1 + 1 from by omega]
    rfl

/-- **Rev-zebra consumption shift** (the main post-divergence lifting): from
    `{C, rev_zebra b, f, R}` we reach `{C, [], f, zebra b ++ R}` in `2b` TM
    steps. Derived from a trivial 1-iteration `{C, [t,f] ++ L, f, R} →{2}
    {C, L, f, [f,t] ++ R}` via `shift_rule_L_lift`. -/
theorem rev_zebra_consume (R : List Sym) (b : Nat) :
    ({ state := some stC, left := rev_zebra b, head := false, right := R } : Config 6) -[tm]->*
    { state := some stC, left := [], head := false, right := zebra b ++ R } := by
  rw [rev_zebra_eq_listPow, zebra_eq_listPow]
  have h : ∀ L' R' : List Sym,
      ({ state := some stC, left := [true, false] ++ L', head := false, right := R' } : Config 6)
        -[tm]->*
      { state := some stC, left := L', head := false, right := [false, true] ++ R' } := by
    intro L' R'; refine ⟨2, ?_⟩; show run tm _ 2 = _; rfl
  have := shift_rule_L_lift tm (some stC) false [true, false] [false, true] h [] R b
  simp only [List.append_nil] at this
  exact this

/-- **4-step setup** between `rev_zebra_consume` and `zebra_consume_R`:
    `{C, [], f, R} → {E, [t, t], t, R}`. Generic in `R` — the intermediate
    steps only write and move, without reading from the right beyond the
    first two cells, both of which get written before they're read. -/
theorem phase_b_setup (R : List Sym) :
    run tm ({ state := some stC, left := [], head := false, right := R } : Config 6) 4 =
    { state := some stE, left := [true, true], head := true, right := R } := rfl

/-- **Zebra consumption shift** on the right: from `{E, L, t, zebra b ++ R}`
    we reach `{E, ones (2*b) ++ L, t, R}` in `4b` TM steps. Derived from a
    1-iteration `{E, L, t, [f,t] ++ R} →{4} {E, [t,t] ++ L, t, R}` via
    `shift_rule_R_lift`. -/
theorem zebra_consume_R (L R : List Sym) (b : Nat) :
    ({ state := some stE, left := L, head := true, right := zebra b ++ R } : Config 6) -[tm]->*
    { state := some stE, left := ones (2 * b) ++ L, head := true, right := R } := by
  rw [zebra_eq_listPow, ← listPow_tt_eq_ones]
  exact shift_rule_R_lift tm (some stE) true [false, true] [true, true]
    (fun L' R' => ⟨4, by show run tm _ 4 = _; rfl⟩) L R b

/-- **18-step halting tail base case**: concrete trajectory from
    `{E, ones 2, t, [f,t,f,t,f,t,f,f,t]}` to halt in 18 steps. Proved by `decide`. -/
private theorem phase_b_tail_base :
    run tm ({state := some stE, left := [true, true], head := true,
             right := [false, true, false, true, false, true, false, false, true]} : Config 6) 18 =
    {state := none, left := [false, true, true, true, true, true, true, true, true, true, true],
     head := true, right := []} := by decide

/-- Left non-empty during `phase_b_tail_base` (needed for `run_left_append`).
    Checked by `Nat.decBallLT`. -/
private theorem phase_b_tail_base_left_ne : ∀ m, m < 18 →
    (run tm ({state := some stE, left := [true, true], head := true,
              right := [false, true, false, true, false, true, false, false, true]} : Config 6)
             m).left ≠ [] := by
  decide

/-- **Phase B halting tail** (generic over a left suffix `L`): `18` TM steps
    from `{E, [t, t] ++ L, t, [f,t,f,t,f,t,f,f,t]}` to the halted state
    `{none, [f, t, t, t, t, t, t, t, t, t, t] ++ L, t, []}`. Lifted via
    `run_left_append` from the concrete `L = []` case. -/
theorem phase_b_tail (L : List Sym) :
    run tm ({state := some stE, left := [true, true] ++ L, head := true,
             right := [false, true, false, true, false, true, false, false, true]} : Config 6) 18 =
    {state := none,
     left := [false, true, true, true, true, true, true, true, true, true, true] ++ L,
     head := true, right := []} := by
  have h := run_left_append tm
    ({state := some stE, left := [true, true], head := true,
      right := [false, true, false, true, false, true, false, false, true]} : Config 6)
    L 18 phase_b_tail_base_left_ne
  rw [phase_b_tail_base] at h
  exact h

/-- **`S1(0, b, 1)` halts** — full proof of the dangerous case avoided by
    Pomme, via phase decomposition and `shift_rule_L_lift` / `shift_rule_R_lift`.

    Chain the 8 phases as `EvStep`s: pre-divergence (`2b + 42` steps, known),
    then rev-zebra consumption (via `shift_rule_L_lift`), then a 4-step setup,
    then zebra consumption via `shift_rule_R_lift`, then an 18-step halting
    tail lifted from a `decide`d base. -/
theorem ROv1_1_0_halts (b : Nat) : ∃ k, (run tm (S1 0 b 1) k).halted := by
  -- Chain EvSteps from S1 0 b 1 down to a halted config.
  have h_pre : (S1 0 b 1 : Config 6) -[tm]->*
      ({state := some stC, left := rev_zebra b, head := false,
        right := [false, true, false, true, false, true, false, false, true]} : Config 6) :=
    ⟨2 * b + 42, ROv1_pre_divergence b⟩
  have h_revzebra := rev_zebra_consume
    [false, true, false, true, false, true, false, false, true] b
  have h_setup : ({state := some stC, left := [], head := false,
                   right := zebra b ++ [false, true, false, true, false, true, false, false, true]}
                   : Config 6) -[tm]->*
      ({state := some stE, left := [true, true], head := true,
        right := zebra b ++ [false, true, false, true, false, true, false, false, true]}
        : Config 6) :=
    ⟨4, phase_b_setup _⟩
  have h_zebracons := zebra_consume_R [true, true]
    [false, true, false, true, false, true, false, false, true] b
  -- `zebra_consume_R` produces left = `ones (2*b) ++ [t, t]`; `phase_b_tail`
  -- wants `[t, t] ++ L`. Rewrite via `ones_append` + `List.append_assoc` to
  -- bridge the two forms (both are `ones (2 + 2*b)`).
  have h_left_eq : ones (2 * b) ++ [true, true] = [true, true] ++ ones (2 * b) := by
    show ones (2 * b) ++ ones 2 = ones 2 ++ ones (2 * b)
    rw [ones_append, ones_append]; congr 1; omega
  rw [h_left_eq] at h_zebracons
  have h_tail := phase_b_tail (ones (2 * b))
  have h_tail_ev : ({state := some stE, left := [true, true] ++ ones (2 * b), head := true,
                     right := [false, true, false, true, false, true, false, false, true]}
                     : Config 6) -[tm]->*
      ({state := none,
        left := [false, true, true, true, true, true, true, true, true, true, true]
                ++ ones (2 * b),
        head := true, right := []} : Config 6) :=
    ⟨18, h_tail⟩
  -- Compose: S1 0 b 1 →* halted
  have h_full : (S1 0 b 1 : Config 6) -[tm]->*
      ({state := none,
        left := [false, true, true, true, true, true, true, true, true, true, true]
                ++ ones (2 * b),
        head := true, right := []} : Config 6) :=
    h_pre.trans (h_revzebra.trans (h_setup.trans (h_zebracons.trans h_tail_ev)))
  obtain ⟨k, hk⟩ := h_full
  exact ⟨k, by rw [hk]; rfl⟩

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
  -- Chain: Incs2 → Ov2_raw → Inc3_absorb → IncsOv3
  -- S2 a b → S2 0 (a*3+b) → raw form → S3 (1+a*3+b) 3 → S1 0 2 (7+a*6+b*2)
  have step1 : S2 a b -[tm]->* S2 0 (a * 3 + b) := Incs2 a b
  have step2 : (S2 0 (a * 3 + b) : Config 6) -[tm]->*
               { state := some stC, left := ones (4 + 2 * (a * 3 + b)), head := true,
                 right := [false, true, false] } := Ov2_raw (a * 3 + b)
  -- The raw form matches Inc3_absorb's input with a' = 1 + (a*3+b), b' = 1
  -- ones (4 + 2*(a*3+b)) = ones (2*(2+a*3+b)) = ones (2*(1+(1+a*3+b)))
  -- right [f,t,f] = zebra 1 ++ [false]
  have step3 : (⟨some stC, ones (4 + 2 * (a * 3 + b)), true, [false, true, false]⟩ : Config 6)
               -[tm]->* S3 (1 + (a * 3 + b)) 3 := by
    have h := Inc3_absorb (1 + (a * 3 + b)) 1
    -- Need to match the form
    have heq_left : ones (2 * (1 + (1 + (a * 3 + b)))) = ones (4 + 2 * (a * 3 + b)) := by
      congr 1; omega
    have heq_right : (zebra 1 ++ [false] : List Sym) = [false, true, false] := rfl
    have heq_target : S3 (1 + (a * 3 + b)) (2 + 1) = S3 (1 + (a * 3 + b)) 3 := rfl
    rw [heq_left, heq_right] at h
    rw [heq_target] at h
    exact h
  have step4 : S3 (1 + (a * 3 + b)) 3 -[tm]->* S1 0 2 (2 + (1 + (a * 3 + b)) * 2 + 3) :=
    IncsOv3 (1 + (a * 3 + b)) 3
  have step5 : S1 0 2 (2 + (1 + (a * 3 + b)) * 2 + 3) = S1 0 2 (7 + a * 6 + b * 2) := by
    congr 1; omega
  rw [step5] at step4
  exact step1.trans (step2.trans (step3.trans step4))

/-- `S1(a, b, 0) →* S3(a, 1+b)`: boundary step from S1 with c=0 to S3. -/
theorem S1_to_S3 (a b : Nat) : S1 a b 0 -[tm]->* S3 a (1 + b) := by
  simp only [S1, S3, show 2 * 0 = 0 from rfl, ones_zero, List.append_nil]
  rw [show zebra b ++ [false, true] = zebra (b + 1) from by
        rw [show [false, true] = zebra 1 from rfl, ← zebra_append],
      show b + 1 = 1 + b from by omega]

theorem ROv1_0 (a b : Nat) : S1 a b 0 -[tm]->* S1 0 2 (3 + a * 2 + b) := by
  calc S1 a b 0
      _ -[tm]->* S3 a (1 + b) := S1_to_S3 a b
      _ -[tm]->* S1 0 2 (2 + a * 2 + (1 + b)) := IncsOv3 a (1 + b)
      _ -[tm]->* S1 0 2 (3 + a * 2 + b) := by
            rw [show 2 + a * 2 + (1 + b) = 3 + a * 2 + b from by omega]

/-! #### S1_to_S2 helpers: generic-in-L boundary transitions

The proof of `S1_to_S2` needs three constant-size boundary steps that are
generic in the surrounding left tape `L`. Each is provable by kernel reduction
(`rfl`); the 28-step phase 2 boundary is split into 4×7 chunks to keep kernel
reduction within heartbeat budget. -/

/-- Phase 2: 28-step boundary from `{C, L, t, [t,t,f,t]}` to
    `{C, L, t, [f,t,f,t,t,t,t,f,t]}`. Left unchanged, right tape replaced.
    Generic in `L`. -/
private theorem S1_to_S2_phase2 (L : List Sym) :
    run tm ({state := some stC, left := L, head := true,
             right := [true, true, false, true]} : Config 6) 28 =
    {state := some stC, left := L, head := true,
     right := [false, true, false, true, true, true, true, false, true]} := by
  rw [show (28:Nat) = 7 + 7 + 7 + 7 from rfl, run_add, run_add, run_add]
  have h1 : run tm ({state := some stC, left := L, head := true,
                     right := [true, true, false, true]} : Config 6) 7 =
            {state := some stD, left := [false, true, true, true, false] ++ L,
             head := false, right := []} := rfl
  rw [h1]
  have h2 : run tm ({state := some stD, left := [false, true, true, true, false] ++ L,
                     head := false, right := []} : Config 6) 7 =
            {state := some stD,
             left := [false, false, true, true, true, true, true, false] ++ L,
             head := true, right := [true]} := rfl
  rw [h2]
  have h3 : run tm ({state := some stD,
                     left := [false, false, true, true, true, true, true, false] ++ L,
                     head := true, right := [true]} : Config 6) 7 =
            {state := some stA, left := false :: L, head := true,
             right := [true, true, true, true, true, true, false, true]} := rfl
  rw [h3]
  have h4 : run tm ({state := some stA, left := false :: L, head := true,
                     right := [true, true, true, true, true, true, false, true]} : Config 6) 7 =
            {state := some stC, left := L, head := true,
             right := [false, true, false, true, true, true, true, false, true]} := rfl
  exact h4

private theorem S1_to_S2_phase2_ev (L : List Sym) :
    ({state := some stC, left := L, head := true,
      right := [true, true, false, true]} : Config 6) -[tm]->*
    {state := some stC, left := L, head := true,
     right := [false, true, false, true, true, true, true, false, true]} :=
  ⟨28, S1_to_S2_phase2 L⟩

/-- Phase 4a: 6-step boundary, generic in `L`. -/
private theorem S1_to_S2_phase4a_ev (L : List Sym) :
    ({state := some stC, left := L, head := true,
      right := [true, true, true, false, true]} : Config 6) -[tm]->*
    {state := some stC, left := L, head := false,
     right := [false, true, false, false, true]} :=
  ⟨6, rfl⟩

/-- Phase 6a: 2-step boundary, generic in `L`. Grows left by `[t,f]`. -/
private theorem S1_to_S2_phase6a_ev (L : List Sym) :
    ({state := some stC, left := L, head := true,
      right := [false, false, true]} : Config 6) -[tm]->*
    {state := some stC, left := true :: false :: L, head := false,
     right := [true]} :=
  ⟨2, rfl⟩

/-- `S1(2+a, b, 1) →* S2(a, 6+b)`: boundary step from S1 with c=1 to S2.
    Decomposition (`66 + 8*b` steps, independent of `a`):
    1. `zebra_traverse b` (2b steps) consumes `zebra b` on right.
    2. Phase 2: 28-step fixed boundary processes `[t,t,f,t]` tail.
    3. `zebra_traverse 2` (4 steps) consumes 2 more zebra pairs.
    4. Phase 4a: 6-step boundary flips head `t→f`.
    5. `cd_retreat_ev_keep_ones (b+2) (2+2a)`: consumes `rev_zebra (b+2)` from left.
    6. `zebra_traverse (b+4)` (2(b+4) steps) consumes zebras from right.
    7. Phase 6a: 2-step boundary growing left by `[t,f]`.
    8. `cd_retreat_ev_keep_ones (b+5) (2a)`: final retreat. -/
theorem S1_to_S2 (a b : Nat) : S1 (2 + a) b 1 -[tm]->* S2 a (6 + b) := by
  show (S1 (2 + a) b 1 : Config 6) -[tm]->* S2 a (6 + b)
  simp only [S1, S2]
  rw [show 2 * (2 + a) = 4 + 2 * a from by omega,
      show 2 * 1 = 2 from rfl,
      show (zebra b ++ ones 2 ++ ([false, true] : List Sym)) =
          zebra b ++ [true, true, false, true] from by
        rw [List.append_assoc]; rfl]
  -- Phase 1: zebra_traverse b
  refine (zebra_traverse_ev b (ones (4 + 2 * a)) [true, true, false, true]).trans ?_
  -- Phase 2: 28-step boundary
  refine (S1_to_S2_phase2_ev (rev_zebra b ++ ones (4 + 2 * a))).trans ?_
  -- Phase 3: zebra_traverse 2 (after rewriting right as `zebra 2 ++ [t,t,t,f,t]`)
  rw [show ([false, true, false, true, true, true, true, false, true] : List Sym) =
          zebra 2 ++ [true, true, true, false, true] from rfl]
  refine (zebra_traverse_ev 2 (rev_zebra b ++ ones (4 + 2 * a))
            [true, true, true, false, true]).trans ?_
  -- Combine `rev_zebra 2 ++ rev_zebra b = rev_zebra (b + 2)`
  rw [show (rev_zebra 2 ++ (rev_zebra b ++ ones (4 + 2 * a)) : List Sym) =
          rev_zebra (b + 2) ++ ones (2 + (2 + 2 * a)) from by
        rw [← List.append_assoc, rev_zebra_append,
            show (4 + 2 * a : Nat) = 2 + (2 + 2 * a) from by omega]
        congr 2; omega]
  -- Phase 4a: 6-step boundary
  refine (S1_to_S2_phase4a_ev _).trans ?_
  -- Phase 4b: cd_retreat_ev_keep_ones (k=b+2, m=2+2a)
  refine (cd_retreat_ev_keep_ones (b + 2) (2 + 2 * a)
            [false, true, false, false, true]).trans ?_
  -- Rewrite right: `zebra (b + 2 + 1) ++ [f,t,f,f,t] = zebra (b + 4) ++ [f,f,t]`
  rw [show (zebra (b + 2 + 1) ++ [false, true, false, false, true] : List Sym) =
          zebra (b + 4) ++ [false, false, true] from by
        rw [show ([false, true, false, false, true] : List Sym) =
                [false, true] ++ [false, false, true] from rfl,
            ← List.append_assoc,
            show ([false, true] : List Sym) = zebra 1 from rfl,
            zebra_append,
            show b + 2 + 1 + 1 = b + 4 from by omega]]
  -- Phase 5: zebra_traverse (b + 4)
  refine (zebra_traverse_ev (b + 4) (ones (2 + 2 * a)) [false, false, true]).trans ?_
  -- Phase 6a: 2-step boundary
  refine (S1_to_S2_phase6a_ev _).trans ?_
  -- Combine `[t, f] :: rev_zebra (b + 4) = rev_zebra (b + 5)`
  rw [show (true :: false :: (rev_zebra (b + 4) ++ ones (2 + 2 * a)) : List Sym) =
          rev_zebra (b + 5) ++ ones (2 + 2 * a) from by
        show rev_zebra 1 ++ rev_zebra (b + 4) ++ ones (2 + 2 * a) = _
        rw [rev_zebra_append]
        congr 2; omega]
  -- Phase 6b: cd_retreat_ev_keep_ones (k=b+5, m=2a), right = [t]
  have hfin := cd_retreat_ev_keep_ones (b + 5) (2 * a) [true]
  -- Match shape: `ones (2 + 2*a) = ones (2 + 2*a)` already, target `zebra (6+b) ++ [t]`
  rw [show (ones (2 + 2 * a) : List Sym) = ones (2 + 2 * a) from rfl]
  -- `zebra (b + 5 + 1) = zebra (6 + b)` via commutativity
  have hz : zebra (b + 5 + 1) = zebra (6 + b) := by congr 1; omega
  rw [hz] at hfin
  exact hfin

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

/-! ### 11. Init (nonhalting proof moved to `Bootstrap.lean`) -/

/-- The TM reaches `S'(18)` from the initial config at step 715. -/
theorem init : run tm (initConfig 6) 715 = S' 18 := by
  simp only [S', S1, zebra, ones, repeatSym]
  native_decide

/-! `ValidS`, `ValidS_progress`, `bootstrap`, and `tm_not_halts` live in
`Bootstrap.lean` to keep `machine.lean` focused on atomic rules and macro
compositions. They depend on `BigStep0`/`BigStep1` and `Hensel.pomme_main`. -/

/-! ### 12. Atomic rules proved via `es` tactic

Now that all shift rules are defined, we can prove the remaining atomic rules
using the `es` tactic which alternates concrete stepping with shift applications. -/

/-! The primed theorems below are proved in a separate test file via the `es` tactic.
They are sorry'd here as forward declarations; the `es` proofs compile independently
but fail in the dependency chain of this file (likely an elaboration order issue). -/

-- S1_to_S3: actually 0 steps (configs are equal)
theorem S1_to_S3' (a b : Nat) : S1 a b 0 -[tm]->* S3 a (1 + b) := by
  simp only [S1, S3, show 2 * 0 = 0 from rfl, ones_zero, List.append_nil]
  rw [show zebra b ++ [false, true] = zebra (b + 1) from by
        rw [show [false, true] = zebra 1 from rfl, ← zebra_append]]
  rw [show b + 1 = 1 + b from by omega]

end Mxdys
