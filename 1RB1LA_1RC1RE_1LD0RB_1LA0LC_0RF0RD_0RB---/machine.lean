import BusyLean

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
def tm : TM 6 := tm! "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

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
private theorem Inc1_left_ne (b : Nat) (T : List Sym) :
    ∀ m, m < 4 * b + 8 →
      (run tm { state := some stC, left := (ones 2), head := true,
                right := zebra b ++ ((ones 4) ++ T) } m).left ≠ [] := by
  sorry -- TODO: track left through zebra_traverse + ones_process + cd_retreat phases

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

/-! ### 6. Other atomic rules (TODO) -/

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
  sorry -- TODO: same structure as Inc1_left_ne

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
theorem LOv1 (b c : Nat) : S1 0 b (3 + c) -[tm]->* S1 (2 + b) 2 c := by sorry

/-- Ov2 produces S3 with a trailing false (absorbed by Inc3). -/
theorem Ov2_raw (b : Nat) :
    ∃ k, run tm (S2 0 b) k =
      { state := some stC, left := ones (2 * (2 + b)), head := true,
        right := zebra 1 ++ [false] } := by sorry

/-- Inc3 absorbs trailing false: S3_fat → S3_clean. -/
theorem Inc3_absorb (a b : Nat) :
    ∃ k, run tm { state := some stC, left := ones (2 * (1 + a)), head := true,
                  right := zebra b ++ [false] } k = S3 a (2 + b) := by sorry

theorem Ov3 (b : Nat) : S3 0 b -[tm]->* S1 0 2 (2 + b) := by sorry

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
  sorry -- Chain: Incs2 + Ov2_raw + Inc3_absorb + IncsOv3

theorem ROv1_0 (a b : Nat) : S1 a b 0 -[tm]->* S1 0 2 (3 + a * 2 + b) := by
  sorry -- S1(a,b,0) → S3(a, 1+b) → IncsOv3

theorem ROv1_1 (a b : Nat) :
    S1 (2 + a) b 1 -[tm]->* S1 0 2 (19 + a * 6 + b * 2) := by
  sorry -- S1(2+a,b,1) → S2(a, 6+b) → IncsOv2

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
  sorry

theorem BigStep1 (n1 n2 c : Nat) (h : P n1 (c + (2 + n2))) :
    S' (n1 + c * 2 + 1) -[tm]->* S' (23 + n2 * 6 + c * 6) := by
  sorry

/-! ### 11. Init and nonhalting -/

/-- The TM reaches S'(18) from the initial config. -/
theorem init : ∃ k, run tm (initConfig 6) k = S' 18 := by
  sorry -- by decide or tm_chain

/-- **Main theorem**: the TM never halts. -/
theorem tm_not_halts : ∀ m, ¬ (run tm (initConfig 6) m).halted := by
  sorry -- progress argument using P_n + pomme_main

end Mxdys
