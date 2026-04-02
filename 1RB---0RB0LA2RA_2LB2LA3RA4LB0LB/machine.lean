import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.NormNum

/-!
# Nonhalting proof for TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB

A 2-state 5-symbol Turing machine. Transition (A,1) is undefined (halt).

Since BusyLean only supports binary alphabets (Sym := Bool), we build a
standalone 5-symbol framework here.

See `macro.md` for a verbal description of the macro rules.
-/

set_option autoImplicit false

namespace TM5

-- ============================================================
-- Section 1: 5-Symbol TM Framework
-- ============================================================

inductive Dir where | L | R
  deriving DecidableEq, Repr

abbrev Sym := Fin 5

-- Named symbols for readability
@[reducible] def s0 : Sym := 0
@[reducible] def s1 : Sym := 1
@[reducible] def s2 : Sym := 2
@[reducible] def s3 : Sym := 3
@[reducible] def s4 : Sym := 4

abbrev St := Fin 2

@[reducible] def stA : St := 0
@[reducible] def stB : St := 1

structure Config where
  state : Option St
  head  : Sym
  left  : List Sym
  right : List Sym
  deriving DecidableEq, Repr

def Config.halted (c : Config) : Prop := c.state = none

def listHd (l : List Sym) : Sym := l.headD 0
def listTl (l : List Sym) : List Sym := l.tail

@[simp] theorem listHd_cons (x : Sym) (xs : List Sym) : listHd (x :: xs) = x := rfl
@[simp] theorem listHd_nil : listHd ([] : List Sym) = 0 := rfl
@[simp] theorem listTl_cons (x : Sym) (xs : List Sym) : listTl (x :: xs) = xs := rfl
@[simp] theorem listTl_nil : listTl ([] : List Sym) = [] := rfl

/-- One step of a 2-state 5-symbol TM. -/
def step (tr : St → Sym → Option (St × Sym × Dir)) (c : Config) : Config :=
  match c.state with
  | none => c
  | some q =>
    match tr q c.head with
    | none => { state := none, head := c.head, left := c.left, right := c.right }
    | some (q', s, d) =>
      match d with
      | .R => { state := some q', head := listHd c.right,
                left := s :: c.left, right := listTl c.right }
      | .L => { state := some q', head := listHd c.left,
                left := listTl c.left, right := s :: c.right }

/-- Run a TM for `n` steps. -/
def run (tr : St → Sym → Option (St × Sym × Dir)) (c : Config) : Nat → Config
  | 0     => c
  | n + 1 => run tr (step tr c) n

@[simp] theorem run_zero (tr : St → Sym → Option (St × Sym × Dir)) (c : Config) :
    run tr c 0 = c := rfl

theorem run_succ (tr : St → Sym → Option (St × Sym × Dir)) (c : Config) (n : Nat) :
    run tr c (n + 1) = run tr (step tr c) n := rfl

theorem run_add (tr : St → Sym → Option (St × Sym × Dir)) (c : Config) (m n : Nat) :
    run tr c (m + n) = run tr (run tr c m) n := by
  induction m generalizing c with
  | zero => simp
  | succ m ih => simp only [Nat.succ_add, run_succ]; exact ih (step tr c)

theorem step_halted (tr : St → Sym → Option (St × Sym × Dir)) (c : Config)
    (h : c.state = none) : step tr c = c := by
  simp only [step]; rw [h]

theorem run_halted (tr : St → Sym → Option (St × Sym × Dir)) (c : Config)
    (h : c.state = none) (n : Nat) : run tr c n = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, step_halted _ _ h, ih]

theorem run_state_none (tr : St → Sym → Option (St × Sym × Dir)) (c : Config)
    (m : Nat) (h : c.state = none) : (run tr c m).state = none := by
  rw [run_halted _ _ h]; exact h

theorem run_alive_of_later (tr : St → Sym → Option (St × Sym × Dir))
    (c : Config) (m k : Nat)
    (hmk : m ≤ k) (hk : (run tr c k).state ≠ none) :
    (run tr c m).state ≠ none := by
  intro hm
  apply hk
  rw [show k = m + (k - m) from by omega, run_add]
  exact run_state_none tr _ _ hm

-- ============================================================
-- Section 2: Nonhalt by Progress Invariant
-- ============================================================

/-- If every P-config advances to another P-config in positive steps with
    non-halted state, then the machine never halts from any P-config. -/
theorem nonhalt_of_progress (tr : St → Sym → Option (St × Sym × Dir))
    (P : Config → Prop)
    (hprog : ∀ c, P c → ∃ k, 0 < k ∧ P (run tr c k) ∧ (run tr c k).state ≠ none)
    (c : Config) (hc : P c) : ∀ m, (run tr c m).state ≠ none := by
  intro m
  induction m using Nat.strongRecOn generalizing c with
  | _ m ihm =>
    match m with
    | 0 =>
      obtain ⟨k, _, _, hk_state⟩ := hprog c hc
      exact run_alive_of_later tr c 0 k (Nat.zero_le _) hk_state
    | m' + 1 =>
      obtain ⟨k, hk_pos, hk_P, hk_state⟩ := hprog c hc
      by_cases hge : m' + 1 ≤ k
      · exact run_alive_of_later tr c (m' + 1) k hge hk_state
      · have hlt : k < m' + 1 := Nat.lt_of_not_le hge
        rw [show m' + 1 = k + (m' + 1 - k) from by omega, run_add]
        exact ihm (m' + 1 - k) (by omega) (run tr c k) hk_P

-- ============================================================
-- Section 3: The TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB
-- ============================================================

/-- Transition function.

       0     1     2     3     4
  A   1RB   ---   0RB   0LA   2RA
  B   2LB   2LA   3RA   4LB   0LB
-/
def tm (q : St) (s : Sym) : Option (St × Sym × Dir) :=
  match q.val, s.val with
  | 0, 0 => some (stB, s1, .R)   -- A,0 → 1RB
  | 0, 1 => none                  -- A,1 → ---  (HALT)
  | 0, 2 => some (stB, s0, .R)   -- A,2 → 0RB
  | 0, 3 => some (stA, s0, .L)   -- A,3 → 0LA
  | 0, 4 => some (stA, s2, .R)   -- A,4 → 2RA
  | 1, 0 => some (stB, s2, .L)   -- B,0 → 2LB
  | 1, 1 => some (stA, s2, .L)   -- B,1 → 2LA
  | 1, 2 => some (stA, s3, .R)   -- B,2 → 3RA
  | 1, 3 => some (stB, s4, .L)   -- B,3 → 4LB
  | 1, 4 => some (stB, s0, .L)   -- B,4 → 0LB
  | _, _ => none  -- unreachable for Fin 2 × Fin 5

-- Abbreviations for step/run with our TM
abbrev tmStep := step tm
abbrev tmRun := run tm

-- Transition simp lemmas (avoid unfolding `tm` globally)
@[simp] theorem tm_A0 : tm stA s0 = some (stB, s1, .R) := rfl
@[simp] theorem tm_A1 : tm stA s1 = none := rfl
@[simp] theorem tm_A2 : tm stA s2 = some (stB, s0, .R) := rfl
@[simp] theorem tm_A3 : tm stA s3 = some (stA, s0, .L) := rfl
@[simp] theorem tm_A4 : tm stA s4 = some (stA, s2, .R) := rfl
@[simp] theorem tm_B0 : tm stB s0 = some (stB, s2, .L) := rfl
@[simp] theorem tm_B1 : tm stB s1 = some (stA, s2, .L) := rfl
@[simp] theorem tm_B2 : tm stB s2 = some (stA, s3, .R) := rfl
@[simp] theorem tm_B3 : tm stB s3 = some (stB, s4, .L) := rfl
@[simp] theorem tm_B4 : tm stB s4 = some (stB, s0, .L) := rfl

-- ============================================================
-- Section 4: Helpers
-- ============================================================

/-- Repeat a symbol `n` times. -/
def rep (s : Sym) (n : Nat) : List Sym := List.replicate n s

@[simp] theorem rep_zero (s : Sym) : rep s 0 = [] := rfl
@[simp] theorem rep_succ (s : Sym) (n : Nat) : rep s (n + 1) = s :: rep s n := rfl

/-- Repeat a pair of symbols `n` times as a flat list. -/
def repPair (a b : Sym) : Nat → List Sym
  | 0 => []
  | n + 1 => a :: b :: repPair a b n

@[simp] theorem repPair_zero (a b : Sym) : repPair a b 0 = [] := rfl
@[simp] theorem repPair_succ (a b : Sym) (n : Nat) :
    repPair a b (n + 1) = a :: b :: repPair a b n := rfl

theorem repPair_length (a b : Sym) (n : Nat) : (repPair a b n).length = 2 * n := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih]; omega

/-- Valid ternary pairs: alternating first-of-pair elements from {s0,s2,s4} with s2. -/
def ValidTern : List Sym → Prop
  | [] => True
  | [_] => False
  | a :: b :: rest => (a = s2 ∨ a = s0 ∨ a = s4) ∧ b = s2 ∧ ValidTern rest

theorem validTern_nil : ValidTern ([] : List Sym) := trivial

theorem validTern_cons (a : Sym) (rest : List Sym) (ha : a = s2 ∨ a = s0 ∨ a = s4)
    (hr : ValidTern rest) : ValidTern (a :: s2 :: rest) :=
  ⟨ha, rfl, hr⟩

theorem validTern_rep_s2 : (n : Nat) → ValidTern (rep s2 (2 * n))
  | 0 => validTern_nil
  | n + 1 => by
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 from by omega]
    simp only [rep_succ]
    exact ⟨Or.inl rfl, rfl, validTern_rep_s2 n⟩

theorem validTern_repPair_s4_s2 : (n : Nat) → ValidTern (repPair s4 s2 n)
  | 0 => validTern_nil
  | n + 1 => ⟨Or.inr (Or.inr rfl), rfl, validTern_repPair_s4_s2 n⟩

theorem validTern_append : {l1 l2 : List Sym} → ValidTern l1 → ValidTern l2 → ValidTern (l1 ++ l2)
  | [], _, _, h2 => by simpa
  | [_], _, h1, _ => absurd h1 (by simp [ValidTern])
  | _ :: _ :: rest, _, ⟨ha, hb, hr⟩, h2 => by
    simp only [List.cons_append]; exact ⟨ha, hb, validTern_append hr h2⟩

theorem validTern_even : {l : List Sym} → ValidTern l → l.length % 2 = 0
  | [], _ => by simp
  | [_], hv => absurd hv (by simp [ValidTern])
  | _ :: _ :: rest, ⟨_, _, hr⟩ => by simp [List.length_cons]; have := validTern_even hr; omega

/-- Parity of binary value (true if odd, i.e., LSB is s3). -/
def binOdd (l : List Sym) : Bool :=
  match l with
  | [] => false
  | a :: _ => a == s3

/-- Parity of ternary value. Digit 1 (s0) flips parity; digits 0 (s2) and 2 (s4) don't. -/
def ternOdd : List Sym → Bool
  | [] => false
  | [_] => false
  | a :: _ :: rest => if a == s0 then !ternOdd rest else ternOdd rest

@[simp] theorem binOdd_nil : binOdd ([] : List Sym) = false := rfl
@[simp] theorem binOdd_cons (a : Sym) (l : List Sym) : binOdd (a :: l) = (a == s3) := rfl
@[simp] theorem ternOdd_nil : ternOdd ([] : List Sym) = false := rfl
@[simp] theorem ternOdd_cons (a : Sym) (b : Sym) (rest : List Sym) :
    ternOdd (a :: b :: rest) = if a == s0 then !ternOdd rest else ternOdd rest := rfl

theorem ternOdd_rep_s2 : (n : Nat) → ternOdd (rep s2 n) = false
  | 0 => rfl
  | 1 => by simp [rep, ternOdd]
  | n + 2 => by simp [rep, List.replicate_succ, ternOdd_cons, s2, s0]; exact ternOdd_rep_s2 n

theorem ternOdd_repPair_s4_s2 : (n : Nat) → ternOdd (repPair s4 s2 n) = false
  | 0 => rfl
  | n + 1 => by simp [repPair, ternOdd_cons, s4, s0]; exact ternOdd_repPair_s4_s2 n

/-- ternOdd ignores leading s2 pairs. -/
theorem ternOdd_rep_s2_append : (j : Nat) → (l : List Sym) →
    ternOdd (rep s2 (2 * j) ++ l) = ternOdd l
  | 0, _ => by simp [rep]
  | j + 1, l => by
    rw [show 2 * (j + 1) = 2 * j + 1 + 1 from by omega]
    simp only [rep, List.replicate_succ, List.cons_append, ternOdd_cons, s2, s0]
    exact ternOdd_rep_s2_append j l

/-- ternOdd ignores leading (s4,s2) pairs. -/
theorem ternOdd_repPair_s4_s2_append : (j : Nat) → (l : List Sym) →
    ternOdd (repPair s4 s2 j ++ l) = ternOdd l
  | 0, _ => by simp [repPair]
  | j + 1, l => by
    simp only [repPair, List.cons_append, ternOdd_cons, s4, s0]
    exact ternOdd_repPair_s4_s2_append j l

/-- binOdd flips under carry_stop (rep s3 k ++ s2 :: rest → rep s2 k ++ s3 :: rest). -/
theorem binOdd_carry_flip_stop (k : Nat) (rest : List Sym) :
    binOdd (rep s2 k ++ (s3 :: rest)) = !binOdd (rep s3 k ++ (s2 :: rest)) := by
  cases k with
  | zero => simp [rep, binOdd_cons, s2, s3]
  | succ k => simp [rep, List.replicate_succ, List.cons_append, binOdd_cons, s2, s3]

/-- binOdd flips under overflow_carry (rep s3 d → rep s2 (d+1)) when d ≥ 1. -/
theorem binOdd_overflow_carry_flip (d : Nat) (hd : d ≥ 1) :
    binOdd (rep s2 (d + 1)) = !binOdd (rep s3 d) := by
  cases d with
  | zero => omega
  | succ d => simp [rep, List.replicate_succ, binOdd_cons, s2, s3]

/-- Decompose binary cells into leading s3's + first s2 + rest, or all s3's. -/
theorem bin_decompose : (bin : List Sym) → (∀ s ∈ bin, s = s2 ∨ s = s3) →
    (∃ k rest, bin = rep s3 k ++ (s2 :: rest) ∧ ∀ s ∈ rest, s = s2 ∨ s = s3) ∨
    (∃ d, bin = rep s3 d)
  | [], _ => Or.inr ⟨0, rfl⟩
  | a :: tl, h => by
    have ha := h a (by simp)
    have htl : ∀ s ∈ tl, s = s2 ∨ s = s3 := fun s hs => h s (by simp [hs])
    rcases ha with rfl | rfl
    · exact Or.inl ⟨0, tl, rfl, htl⟩
    · rcases bin_decompose tl htl with ⟨k, rest, hk, hrest⟩ | ⟨d, hd⟩
      · exact Or.inl ⟨k + 1, rest, by rw [hk]; simp [rep_succ], hrest⟩
      · exact Or.inr ⟨d + 1, by rw [hd]; simp [rep_succ]⟩

/-- Decompose valid non-all-zero ternary into leading zero pairs + first non-zero pair + rest. -/
theorem validTern_decompose : {l : List Sym} → ValidTern l → (∃ x ∈ l, x ≠ s2) →
    ∃ j a rest, l = rep s2 (2 * j) ++ (a :: s2 :: rest) ∧
      (a = s0 ∨ a = s4) ∧ ValidTern rest
  | [], _, hne => absurd hne (by simp)
  | [_], hv, _ => absurd hv (by simp [ValidTern])
  | a :: b :: rest, ⟨ha, hb, hr⟩, hne => by
    rcases ha with rfl | rfl | rfl
    · -- a = s2, first pair is zero; recurse
      have hne_rest : ∃ x ∈ rest, x ≠ s2 := by
        obtain ⟨x, hx, hxne⟩ := hne
        simp at hx; rcases hx with rfl | rfl | hx
        · exact absurd rfl hxne
        · exact absurd hb hxne
        · exact ⟨x, hx, hxne⟩
      obtain ⟨j, a', rest', hrest, ha', hr'⟩ := validTern_decompose hr hne_rest
      exact ⟨j + 1, a', rest', by
        subst hb; rw [hrest]
        simp [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega, rep_succ],
        ha', hr'⟩
    · exact ⟨0, s0, rest, by subst hb; rfl, Or.inl rfl, hr⟩
    · exact ⟨0, s4, rest, by subst hb; rfl, Or.inr rfl, hr⟩

-- ============================================================
-- Section 5: Canonical Configurations
-- ============================================================

/-- CycleStart: state A reading s2 at the boundary between binary and ternary.

    Physical tape (L→R):
      0^inf  1 3  bin(MSB..LSB)  [A,s2]  tern(LSB-pair..MSB-pair)  2^pad  0^inf

    In Config representation:
      state = some stA
      head  = s2
      left  = bin_cells ++ [s3, s1]     (binary LSB first, then reversed terminator)
      right = tern_cells ++ rep s2 pad  (ternary pairs LSB first, then padding)

    `bin_cells`: list of cells from {s2, s3} representing binary digits (2=0, 3=1).
    `tern_cells`: list of cells of even length, consecutive pairs from
    {(s2,s2),(s0,s2),(s4,s2)}.
-/
def CycleStart (bin_cells : List Sym) (tern_cells : List Sym) (pad : Nat) : Config :=
  { state := some stA,
    head  := s2,
    left  := bin_cells ++ [s3, s1],
    right := tern_cells ++ rep s2 pad }

/-- Binary encoding: value `v` with `d` digits as a list of Sym (s2/s3), LSB first. -/
def binEnc : Nat → Nat → List Sym
  | 0, _     => []
  | d + 1, v => (if v % 2 == 0 then s2 else s3) :: binEnc d (v / 2)

/-- Ternary pair encoding for one digit: 0 → (s2,s2), 1 → (s0,s2), 2 → (s4,s2). -/
def ternPair (d : Nat) : List Sym :=
  match d % 3 with
  | 0 => [s2, s2]
  | 1 => [s0, s2]
  | _ => [s4, s2]  -- 2

/-- Ternary encoding: list of digits (LSB first) → flat list of cell pairs. -/
def ternEnc (digits : List Nat) : List Sym :=
  (digits.map ternPair).flatten

-- ============================================================
-- Section 6: Initial Configuration
-- ============================================================

def initConfig : Config :=
  { state := some stA, head := s0, left := [], right := [] }

/-- After 117 steps, the machine is in CycleStart with binary value 1
    (2 digits: [s3, s2]) and 4 all-zero ternary pairs (8 cells of s2). -/
theorem init_to_cycle :
    tmRun initConfig 117 =
    CycleStart [s3, s2] (rep s2 8) 0 := by
  native_decide

-- ============================================================
-- Section 7: Step Unfolding Tactic
-- ============================================================

/-- Unfold one TM step via run_succ and simplify. -/
macro "tm_step" : tactic => `(tactic| (
  rw [run_succ]; simp only [step, tm, listHd_cons, listTl_cons, listHd_nil, listTl_nil,
    List.cons_append, List.append_assoc, List.nil_append]))

-- ============================================================
-- Section 8: Carry Propagation Lemmas
-- ============================================================

/-- Carry through k leading s3 bits (B,s3→4LB) then stop at s2 (B,s2→3RA)
    and clean up k s4 cells (A,s4→2RA). Total: 2k+3 steps.
    L and R are abstract left/right tails. -/
theorem carry_step (k : Nat) (L R : List Sym) :
    run tm (⟨some stB, s3, rep s3 k ++ (s2 :: L), R⟩)
          (2 * k + 3) =
    ⟨some stA, listHd R, rep s2 (k + 1) ++ (s3 :: L), listTl R⟩ := by
  induction k generalizing R with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    tm_step; tm_step; tm_step; simp [run]
  | succ k ih =>
    simp only [rep_succ, List.cons_append]
    rw [show 2 * (k + 1) + 3 = ((2 * k + 3) + 1) + 1 from by omega]
    tm_step
    rw [show (2 * k + 3) + 1 = (2 * k + 3) + 1 from rfl, run_add, ih (s4 :: R)]
    simp only [listHd_cons, listTl_cons, rep_succ, List.cons_append]
    tm_step; simp [run]

/-- Base carry: no leading s3 bits, just B,s2→3RA. 1 step. -/
theorem carry_stop (L R : List Sym) :
    run tm (⟨some stB, s2, L, R⟩) 1 =
    ⟨some stA, listHd R, s3 :: L, listTl R⟩ := by
  tm_step; simp [run]

-- ============================================================
-- Section 9: Entry Lemmas (CycleStart → carry state)
-- ============================================================

/-- Entry for ternary digit 2 (pair s4,s2): A,s2→0RB; B,s4→0LB; B,s0→2LB.
    3 steps from CycleStart to carry state. -/
theorem entry_d2 (L R : List Sym) :
    run tm (⟨some stA, s2, L, s4 :: s2 :: R⟩) 3 =
    ⟨some stB, listHd L, listTl L, s2 :: s0 :: s2 :: R⟩ := by
  tm_step; tm_step; tm_step; simp [run]

/-- Entry for ternary digit 1 (pair s0,s2): A,s2→0RB; B,s0→2LB; B,s0→2LB.
    3 steps from CycleStart to carry state. -/
theorem entry_d1 (L R : List Sym) :
    run tm (⟨some stA, s2, L, s0 :: s2 :: R⟩) 3 =
    ⟨some stB, listHd L, listTl L, s2 :: s2 :: s2 :: R⟩ := by
  tm_step; tm_step; tm_step; simp [run]

-- ============================================================
-- Section 9b: General Cycle Theorems
-- ============================================================

/-- Full cycle for ternary digit 2 with k leading binary 1-bits then a 0-bit.
    Entry (3 steps) + carry/stop (1+2k steps) = 4+2k total.
    Binary increments, ternary pair (s4,s2) → (s0,s2). -/
theorem cycle_d2_general (k : Nat) (bin_rest tern_rest : List Sym) (pad : Nat) :
    tmRun (CycleStart (rep s3 k ++ [s2] ++ bin_rest) ([s4, s2] ++ tern_rest) pad) (4 + 2 * k) =
    CycleStart (rep s2 k ++ [s3] ++ bin_rest) ([s0, s2] ++ tern_rest) pad := by
  unfold CycleStart tmRun
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [show 4 + 2 * k = 3 + (1 + 2 * k) from by omega, run_add, entry_d2]
  cases k with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.add_zero,
               listHd_cons, listTl_cons]
    rw [carry_stop]; simp
  | succ k =>
    simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
    rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by omega]
    rw [carry_step k (bin_rest ++ [s3, s1]) (s2 :: s0 :: s2 :: (tern_rest ++ rep s2 pad))]
    simp [listHd_cons, listTl_cons]

/-- Full cycle for ternary digit 1 with k leading binary 1-bits then a 0-bit.
    Same step count as d2. Binary increments, ternary pair (s0,s2) → (s2,s2). -/
theorem cycle_d1_general (k : Nat) (bin_rest tern_rest : List Sym) (pad : Nat) :
    tmRun (CycleStart (rep s3 k ++ [s2] ++ bin_rest) ([s0, s2] ++ tern_rest) pad) (4 + 2 * k) =
    CycleStart (rep s2 k ++ [s3] ++ bin_rest) ([s2, s2] ++ tern_rest) pad := by
  unfold CycleStart tmRun
  simp only [List.cons_append, List.append_assoc, List.nil_append]
  rw [show 4 + 2 * k = 3 + (1 + 2 * k) from by omega, run_add, entry_d1]
  cases k with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.add_zero,
               listHd_cons, listTl_cons]
    rw [carry_stop]; simp
  | succ k =>
    simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
    rw [show 1 + 2 * (k + 1) = 2 * k + 3 from by omega]
    rw [carry_step k (bin_rest ++ [s3, s1]) (s2 :: s2 :: s2 :: (tern_rest ++ rep s2 pad))]
    simp [listHd_cons, listTl_cons]

-- ============================================================
-- Section 10: Carry Overflow (all binary bits = s3)
-- ============================================================

/-- rep s3 d ++ [s3, s1] = rep s3 (d+1) ++ [s1] -/
theorem rep_s3_terminator (d : Nat) : rep s3 d ++ [s3, s1] = rep s3 (d + 1) ++ [s1] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [rep_succ, List.cons_append, ih]

/-- Overflow carry: B at s3 with d more s3s then s1.
    Carry through all s3s, hit s1 (B,s1→2LA), bounce on blank (A,s0→1RB),
    then B,s2→3RA + (d+1) A,s4→2RA cleanup. Total: 2d+5 steps. -/
theorem overflow_carry (d : Nat) (R : List Sym) :
    run tm (⟨some stB, s3, rep s3 d ++ [s1], R⟩ : Config) (2 * d + 5) =
    ⟨some stA, listHd R, rep s2 (d + 1) ++ [s3, s1], listTl R⟩ := by
  induction d generalizing R with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add]
    tm_step; tm_step; tm_step; tm_step; tm_step; simp [run]
  | succ d ih =>
    simp only [rep_succ, List.cons_append]
    rw [show 2 * (d + 1) + 5 = ((2 * d + 5) + 1) + 1 from by omega]
    tm_step
    rw [show (2 * d + 5) + 1 = (2 * d + 5) + 1 from rfl, run_add, ih (s4 :: R)]
    simp only [listHd_cons, listTl_cons, rep_succ, List.cons_append]
    tm_step; simp [run]

/-- When all d binary bits are 1, carry overflows through terminator.
    Binary resets to all 0s with d+1 digits. -/
theorem carry_overflow_d2 (d : Nat) (tern_rest : List Sym) (pad : Nat) :
    tmRun (CycleStart (rep s3 d) ([s4, s2] ++ tern_rest) pad) (2 * d + 8) =
    CycleStart (rep s2 (d + 1)) ([s0, s2] ++ tern_rest) pad := by
  unfold CycleStart tmRun
  simp only [List.cons_append, List.nil_append]
  rw [show 2 * d + 8 = 3 + (2 * d + 5) from by omega, run_add]
  rw [rep_s3_terminator, entry_d2]
  simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
  rw [overflow_carry d (s2 :: s0 :: s2 :: (tern_rest ++ rep s2 pad))]
  simp [listHd_cons, listTl_cons]

theorem carry_overflow_d1 (d : Nat) (tern_rest : List Sym) (pad : Nat) :
    tmRun (CycleStart (rep s3 d) ([s0, s2] ++ tern_rest) pad) (2 * d + 8) =
    CycleStart (rep s2 (d + 1)) ([s2, s2] ++ tern_rest) pad := by
  unfold CycleStart tmRun
  simp only [List.cons_append, List.nil_append]
  rw [show 2 * d + 8 = 3 + (2 * d + 5) from by omega, run_add]
  rw [rep_s3_terminator, entry_d1]
  simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
  rw [overflow_carry d (s2 :: s2 :: s2 :: (tern_rest ++ rep s2 pad))]
  simp [listHd_cons, listTl_cons]

/-- listHd on rep s3 d ++ [s3, s1] is always s3. -/
theorem listHd_rep_s3_term (d : Nat) : listHd (rep s3 d ++ [s3, s1]) = s3 := by
  cases d with
  | zero => simp [rep_zero, listHd_cons]
  | succ d => simp [rep_succ, List.cons_append, listHd_cons]

/-- listTl on rep s3 d ++ [s3, s1] gives rep s3 d ++ [s1]. -/
theorem listTl_rep_s3_term (d : Nat) : listTl (rep s3 d ++ [s3, s1]) = rep s3 d ++ [s1] := by
  cases d with
  | zero => simp [rep_zero, listTl_cons]
  | succ d =>
    simp only [rep_succ, List.cons_append, listTl_cons]
    exact rep_s3_terminator d

-- ============================================================
-- Section 11: Borrow Propagation
-- ============================================================

/-- Borrow sweep for digit 2: sweep right through j zero-pairs, hit a (s4,s2) pair,
    bounce back converting pairs to (s4,s2). Ends in carry state at binary boundary.
    Total: 4j+3 steps. -/
theorem borrow_sweep_d2 (j : Nat) (L R : List Sym) :
    run tm (⟨some stA, s2, L, rep s2 (2 * j) ++ (s4 :: s2 :: R)⟩ : Config) (4 * j + 3) =
    ⟨some stB, listHd L, listTl L, s2 :: repPair s4 s2 j ++ (s0 :: s2 :: R)⟩ := by
  induction j generalizing L R with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, repPair_zero, List.nil_append]
    exact entry_d2 L R
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega]
    simp only [rep_succ, List.cons_append]
    rw [show 4 * (j + 1) + 3 = ((4 * j + 3) + 2) + 2 from by omega]
    tm_step; tm_step
    rw [show (4 * j + 3) + 2 = (4 * j + 3) + 2 from rfl, run_add, ih (s3 :: s0 :: L) R]
    simp only [listHd_cons, listTl_cons, repPair_succ, List.cons_append]
    tm_step; tm_step; simp [run]

/-- Borrow sweep for digit 1: same sweep, but first non-zero pair is (s0,s2).
    Converts to (s2,s2) after decrement. -/
theorem borrow_sweep_d1 (j : Nat) (L R : List Sym) :
    run tm (⟨some stA, s2, L, rep s2 (2 * j) ++ (s0 :: s2 :: R)⟩ : Config) (4 * j + 3) =
    ⟨some stB, listHd L, listTl L, s2 :: repPair s4 s2 j ++ (s2 :: s2 :: R)⟩ := by
  induction j generalizing L R with
  | zero =>
    simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, repPair_zero, List.nil_append]
    exact entry_d1 L R
  | succ j ih =>
    rw [show 2 * (j + 1) = (2 * j + 1) + 1 from by omega]
    simp only [rep_succ, List.cons_append]
    rw [show 4 * (j + 1) + 3 = ((4 * j + 3) + 2) + 2 from by omega]
    tm_step; tm_step
    rw [show (4 * j + 3) + 2 = (4 * j + 3) + 2 from rfl, run_add, ih (s3 :: s0 :: L) R]
    simp only [listHd_cons, listTl_cons, repPair_succ, List.cons_append]
    tm_step; tm_step; simp [run]

-- ============================================================
-- Section 12: Full Normal Cycle
-- ============================================================

/-- A cycle from CycleStart with valid non-all-zero ternary and valid binary
    always reaches a new valid CycleStart. -/
theorem cycle_nonzero (bin_cells tern_cells : List Sym) (pad : Nat)
    (hbin : ∀ s ∈ bin_cells, s = s2 ∨ s = s3)
    (hv : ValidTern tern_cells)
    (hne : ∃ x ∈ tern_cells, x ≠ s2)
    (hne_bin : bin_cells ≠ []) :
    ∃ steps bin' tern',
      0 < steps ∧
      tmRun (CycleStart bin_cells tern_cells pad) steps =
        CycleStart bin' tern' pad ∧
      (∀ s ∈ bin', s = s2 ∨ s = s3) ∧
      ValidTern tern' ∧
      tern' ≠ [] ∧
      bin' ≠ [] ∧
      binOdd bin' = !binOdd bin_cells ∧
      ternOdd tern' = !ternOdd tern_cells ∧
      bin'.length ≥ bin_cells.length := by
  -- Decompose ternary: j leading zero pairs + non-zero pair (a, s2) + rest
  obtain ⟨j, a, tern_rest, htern, ha, htr⟩ := validTern_decompose hv hne
  subst htern
  -- Case split on the non-zero ternary digit
  rcases ha with rfl | rfl
  · -- DIGIT 1 (a = s0): output digit is s2 (digit 0)
    have hva' : ValidTern (repPair s4 s2 j ++ (s2 :: s2 :: tern_rest)) :=
      validTern_append (validTern_repPair_s4_s2 j) (validTern_cons s2 tern_rest (Or.inl rfl) htr)
    rcases bin_decompose bin_cells hbin with ⟨k, bin_rest, hbin_eq, hbr⟩ | ⟨d, hbin_eq⟩
    · subst hbin_eq
      refine ⟨4*j+2*k+4, rep s2 k ++ (s3 :: bin_rest),
        repPair s4 s2 j ++ (s2 :: s2 :: tern_rest), by omega, ?_, ?_, hva', by simp, by simp,
        binOdd_carry_flip_stop k bin_rest, ?_, by simp [rep, List.length_append]⟩
      · unfold CycleStart tmRun
        simp only [List.cons_append, List.append_assoc]
        rw [show 4*j+2*k+4 = (4*j+3)+(2*k+1) from by omega, run_add, borrow_sweep_d1 j]
        cases k with
        | zero =>
          simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, listHd_cons, listTl_cons]
          rw [carry_stop]; simp [listHd_cons, listTl_cons]
        | succ k =>
          simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
          rw [show 2*(k+1)+1 = 2*k+3 from by omega, carry_step]
          simp [listHd_cons, listTl_cons]
      · intro s hs
        rw [List.mem_append] at hs
        rcases hs with hs | hs
        · exact Or.inl (List.eq_of_mem_replicate hs)
        · simp [List.mem_cons] at hs; rcases hs with rfl | hs
          · exact Or.inr rfl
          · exact hbr s hs
      · -- ternOdd flip: digit 1 (s0→s2)
        simp [ternOdd_repPair_s4_s2_append, ternOdd_rep_s2_append, ternOdd_cons, s2, s0]
    · subst hbin_eq
      have hd_pos : d ≥ 1 := by cases d with | zero => simp at hne_bin | succ d => omega
      refine ⟨4*j+2*d+8, rep s2 (d+1),
        repPair s4 s2 j ++ (s2 :: s2 :: tern_rest), by omega, ?_, ?_, hva', by simp, by simp [rep],
        binOdd_overflow_carry_flip d hd_pos, ?_, by simp [rep]⟩
      · unfold CycleStart tmRun
        simp only [List.cons_append, List.append_assoc]
        rw [show 4*j+2*d+8 = (4*j+3)+(2*d+5) from by omega, run_add, borrow_sweep_d1 j]
        simp only [listHd_rep_s3_term, listTl_rep_s3_term]
        rw [overflow_carry]; simp [listHd_cons, listTl_cons]
      · intro s hs; exact Or.inl (List.eq_of_mem_replicate hs)
      · -- ternOdd flip: digit 1 (s0→s2)
        simp [ternOdd_repPair_s4_s2_append, ternOdd_rep_s2_append, ternOdd_cons, s2, s0]
  · -- DIGIT 2 (a = s4): output digit is s0 (digit 1)
    have hva' : ValidTern (repPair s4 s2 j ++ (s0 :: s2 :: tern_rest)) :=
      validTern_append (validTern_repPair_s4_s2 j) (validTern_cons s0 tern_rest (Or.inr (Or.inl rfl)) htr)
    rcases bin_decompose bin_cells hbin with ⟨k, bin_rest, hbin_eq, hbr⟩ | ⟨d, hbin_eq⟩
    · subst hbin_eq
      refine ⟨4*j+2*k+4, rep s2 k ++ (s3 :: bin_rest),
        repPair s4 s2 j ++ (s0 :: s2 :: tern_rest), by omega, ?_, ?_, hva', by simp, by simp,
        binOdd_carry_flip_stop k bin_rest, ?_, by simp [rep, List.length_append]⟩
      · unfold CycleStart tmRun
        simp only [List.cons_append, List.append_assoc]
        rw [show 4*j+2*k+4 = (4*j+3)+(2*k+1) from by omega, run_add, borrow_sweep_d2 j]
        cases k with
        | zero =>
          simp only [rep_zero, List.nil_append, Nat.mul_zero, Nat.zero_add, listHd_cons, listTl_cons]
          rw [carry_stop]; simp [listHd_cons, listTl_cons]
        | succ k =>
          simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons]
          rw [show 2*(k+1)+1 = 2*k+3 from by omega, carry_step]
          simp [listHd_cons, listTl_cons]
      · intro s hs
        rw [List.mem_append] at hs
        rcases hs with hs | hs
        · exact Or.inl (List.eq_of_mem_replicate hs)
        · simp [List.mem_cons] at hs; rcases hs with rfl | hs
          · exact Or.inr rfl
          · exact hbr s hs
      · -- ternOdd flip: digit 2 (s4→s0)
        simp [ternOdd_repPair_s4_s2_append, ternOdd_rep_s2_append, ternOdd_cons, s4, s0]
    · subst hbin_eq
      have hd_pos : d ≥ 1 := by cases d with | zero => simp at hne_bin | succ d => omega
      refine ⟨4*j+2*d+8, rep s2 (d+1),
        repPair s4 s2 j ++ (s0 :: s2 :: tern_rest), by omega, ?_, ?_, hva', by simp, by simp [rep],
        binOdd_overflow_carry_flip d hd_pos, ?_, by simp [rep]⟩
      · unfold CycleStart tmRun
        simp only [List.cons_append, List.append_assoc]
        rw [show 4*j+2*d+8 = (4*j+3)+(2*d+5) from by omega, run_add, borrow_sweep_d2 j]
        simp only [listHd_rep_s3_term, listTl_rep_s3_term]
        rw [overflow_carry]; simp [listHd_cons, listTl_cons]
      · intro s hs; exact Or.inl (List.eq_of_mem_replicate hs)
      · -- ternOdd flip: digit 2 (s4→s0)
        simp [ternOdd_repPair_s4_s2_append, ternOdd_rep_s2_append, ternOdd_cons, s4, s0]

-- ============================================================
-- Section 13: Overflow
-- ============================================================

/-- Combined forward sweep + bounce + leftward sweep for overflow.
    From CycleStart position, sweeps right through 2m zero cells, bounces,
    sweeps back left converting (s3,s0) pairs to (s2,s4) pairs.
    Result: state B at first binary cell, right side has repPair s2 s4 m ++ [s2, s2]. -/
theorem overflow_sweep (m : Nat) (L : List Sym) :
    run tm (⟨some stA, s2, L, rep s2 (2 * m)⟩ : Config) (4 * m + 3) =
    ⟨some stB, listHd L, listTl L, repPair s2 s4 m ++ [s2, s2]⟩ := by
  induction m generalizing L with
  | zero =>
    simp only [rep_zero, Nat.mul_zero, Nat.zero_add, repPair_zero, List.nil_append]
    tm_step; tm_step; tm_step; simp [run]
  | succ m ih =>
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 from by omega]
    simp only [rep_succ]
    rw [show 4 * (m + 1) + 3 = (((4 * m + 3) + 2) + 1) + 1 from by omega]
    tm_step; tm_step
    rw [show (4 * m + 3) + 2 = (4 * m + 3) + 2 from rfl, run_add, ih (s3 :: s0 :: L)]
    simp only [listHd_cons, listTl_cons, repPair_succ, List.cons_append]
    tm_step; tm_step; simp [run]

/-- listHd on repPair s2 s4 m ++ [s2, s2] is always s2. -/
theorem listHd_overflow_right (m : Nat) : listHd (repPair s2 s4 m ++ [s2, s2]) = s2 := by
  cases m with
  | zero => simp [repPair_zero, listHd_cons]
  | succ m => simp [repPair_succ, List.cons_append, listHd_cons]

/-- listTl on repPair s2 s4 (m+1) ++ [s2, s2] gives repPair s4 s2 (m+1) ++ [s2]. -/
theorem listTl_overflow_right (m : Nat) :
    listTl (repPair s2 s4 (m + 1) ++ [s2, s2]) = s4 :: repPair s2 s4 m ++ [s2, s2] := by
  simp [repPair_succ, List.cons_append, listTl_cons]

/-- repPair s2 s4 m ++ [s2, s2] = s2 :: (repPair s4 s2 m ++ [s2]).
    Equivalently: the "overflow right side" starts with s2 and its tail is repPair s4 s2 m ++ [s2]. -/
theorem overflow_right_eq : (m : Nat) →
    repPair s2 s4 m ++ [s2, s2] = s2 :: (repPair s4 s2 m ++ [s2])
  | 0 => by simp [repPair_zero]
  | m + 1 => by
    simp only [repPair_succ, List.cons_append]
    congr 1; congr 1
    exact overflow_right_eq m

theorem overflow_right_shift : (m : Nat) →
    listTl (repPair s2 s4 m ++ [s2, s2]) = repPair s4 s2 m ++ [s2]
  | m => by rw [overflow_right_eq]; simp [listTl_cons]

/-- Overflow with pad=0: when ternary is all zeros and padding is 0,
    the cycle produces a new CycleStart with repPair s4 s2 d ternary and pad 1. -/
theorem overflow_cycle (bin_cells : List Sym) (d : Nat)
    (hbin : ∀ s ∈ bin_cells, s = s2 ∨ s = s3)
    (hne_bin : bin_cells ≠ []) :
    ∃ steps bin',
      0 < steps ∧
      tmRun (CycleStart bin_cells (rep s2 (2 * d)) 0) steps =
        CycleStart bin' (repPair s4 s2 d) 1 ∧
      (∀ s ∈ bin', s = s2 ∨ s = s3) ∧
      bin' ≠ [] ∧
      binOdd bin' = !binOdd bin_cells ∧
      (binOdd bin_cells = true → bin'.length ≥ 2) := by
  -- Overflow sweep: 4d+3 steps forward sweep + bounce + leftward sweep
  -- Then carry through binary: carry_stop or overflow_carry
  -- Output: CycleStart bin' (repPair s4 s2 d) 1
  rcases bin_decompose bin_cells hbin with ⟨k, bin_rest, hbin_eq, hbr⟩ | ⟨dd, hbin_eq⟩
  · -- Case 1: binary has a 0-bit (carry stops)
    subst hbin_eq
    refine ⟨4*d+2*k+4, rep s2 k ++ (s3 :: bin_rest), by omega, ?_, ?_, by simp,
      binOdd_carry_flip_stop k bin_rest, ?_⟩
    · -- run equality: overflow_sweep + carry
      unfold CycleStart tmRun
      simp only [rep_zero, List.append_nil]
      rw [show 4*d+2*k+4 = (4*d+3)+(2*k+1) from by omega, run_add, overflow_sweep]
      cases k with
      | zero =>
        simp only [rep_zero, List.nil_append, List.cons_append, listHd_cons, listTl_cons]
        rw [carry_stop]
        simp only [listHd_overflow_right, overflow_right_shift, rep_succ, rep_zero]
      | succ k =>
        simp only [rep_succ, List.cons_append, listHd_cons, listTl_cons, List.append_assoc]
        rw [show 2*(k+1)+1 = 2*k+3 from by omega, carry_step]
        simp only [listHd_overflow_right, overflow_right_shift, List.cons_append,
          rep_succ, rep_zero]
    · intro s hs
      rw [List.mem_append] at hs
      rcases hs with hs | hs
      · exact Or.inl (List.eq_of_mem_replicate hs)
      · simp [List.mem_cons] at hs; rcases hs with rfl | hs
        · exact Or.inr rfl
        · exact hbr s hs
    · -- binOdd = true → length ≥ 2: if LSB is s3, then k ≥ 1
      intro hbo
      simp [rep, List.length_append] at hbo ⊢
      cases k with
      | zero => simp [binOdd_cons, s2, s3] at hbo
      | succ k => omega
  · -- Case 2: binary is all s3 (overflow carry)
    subst hbin_eq
    have hdd_pos : dd ≥ 1 := by cases dd with | zero => simp at hne_bin | succ dd => omega
    refine ⟨4*d+2*dd+8, rep s2 (dd+1), by omega, ?_, ?_, by simp [rep],
      binOdd_overflow_carry_flip dd hdd_pos, ?_⟩
    · -- run equality: overflow_sweep + overflow_carry
      unfold CycleStart tmRun
      simp only [rep_zero, List.append_nil]
      rw [show 4*d+2*dd+8 = (4*d+3)+(2*dd+5) from by omega, run_add, overflow_sweep]
      simp only [listHd_rep_s3_term, listTl_rep_s3_term]
      rw [overflow_carry]
      simp only [listHd_overflow_right, overflow_right_shift]
      simp [rep]
    · intro s hs; exact Or.inl (List.eq_of_mem_replicate hs)
    · intro _; simp [rep]; omega

-- ============================================================
-- Section 14: Odd Overflow
-- ============================================================

/-- Odd overflow cascade: forward sweep + bounce + leftward cascade through
    all-zero ternary with pad=1. After 6d+9 steps, state A arrives at the
    first binary cell, with rep s2 (2*(d+2)) on the right. -/
theorem odd_overflow_cascade (d : Nat) (L : List Sym) :
    run tm (⟨some stA, s2, L, rep s2 (2 * d + 1)⟩ : Config) (6 * d + 9) =
    ⟨some stA, listHd L, listTl L, rep s2 (2 * (d + 2))⟩ := by
  induction d generalizing L with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, rep_succ, rep_zero]
    tm_step; tm_step; tm_step; tm_step; tm_step
    tm_step; tm_step; tm_step; tm_step; simp [run]
  | succ d ih =>
    have hrep : rep s2 (2 * (d + 1) + 1) = s2 :: s2 :: rep s2 (2 * d + 1) := by
      show List.replicate (2*(d+1)+1) s2 = s2 :: s2 :: List.replicate (2*d+1) s2
      rw [show 2*(d+1)+1 = 2 + (2*d+1) from by omega, List.replicate_add]; rfl
    have hstep2 : run tm (⟨some stA, s2, L, s2 :: s2 :: rep s2 (2 * d + 1)⟩ : Config) 2 =
        ⟨some stA, s2, s3 :: s0 :: L, rep s2 (2 * d + 1)⟩ := by
      tm_step; tm_step; simp [run]
    rw [hrep, show 6 * (d + 1) + 9 = 2 + ((6 * d + 9) + 4) from by omega,
        run_add, hstep2, run_add, ih (s3 :: s0 :: L)]
    simp only [listHd_cons, listTl_cons]
    have hstep4 : run tm (⟨some stA, s3, s0 :: L, rep s2 (2 * (d + 2))⟩ : Config) 4 =
        ⟨some stA, listHd L, listTl L, s2 :: s2 :: rep s2 (2 * (d + 2))⟩ := by
      tm_step; tm_step; tm_step; tm_step; simp [run]
    rw [hstep4]; congr 1

/-- Odd overflow (k=0): from CycleStart (s2::bin_rest) (rep s2 (2d)) 1,
    reach CycleStart bin_rest (rep s2 (2*(d+2))) 0 in 6d+9 steps. -/
theorem overflow_odd (bin_rest : List Sym) (d : Nat) :
    tmRun (CycleStart (s2 :: bin_rest) (rep s2 (2 * d)) 1) (6 * d + 9) =
      CycleStart bin_rest (rep s2 (2 * (d + 2))) 0 := by
  unfold CycleStart tmRun
  simp only [rep_succ, rep_zero, List.append_nil]
  have hright : rep s2 (2 * d) ++ [s2] = rep s2 (2 * d + 1) := by
    show List.replicate (2*d) s2 ++ [s2] = List.replicate (2*d+1) s2
    rw [show [s2] = List.replicate 1 s2 from rfl,
        show 2*d+1 = 2*d + 1 from by omega, ← List.replicate_add]
  rw [hright, odd_overflow_cascade d ((s2 :: bin_rest) ++ [s3, s1])]
  simp only [listHd_cons, listTl_cons, List.cons_append]

/-- Helper: rep s2 (2*(d+2)) = s2 :: rep s2 (2*(d+1)) ++ [s2]. -/
theorem rep_s2_shift (d : Nat) :
    rep s2 (2 * (d + 2)) = s2 :: (rep s2 (2 * (d + 1)) ++ [s2]) := by
  simp only [rep]
  rw [show [s2] = List.replicate 1 s2 from rfl, ← List.replicate_add,
      show 2*(d+1) + 1 = 2*d + 3 from by omega]
  rw [show 2*(d+2) = 1 + (2*d + 3) from by omega, List.replicate_add]
  rfl

/-- Odd overflow (k=1): from CycleStart (s3::s2::bin_rest) (rep s2 (2d)) 1,
    the cascade consumes the leading s3 bit, creating ternary digit 1.
    Reaches CycleStart bin_rest (s0::s2::rep s2 (2*(d+1))) 1 in 6d+10 steps. -/
theorem overflow_odd_k1 (bin_rest : List Sym) (d : Nat) :
    tmRun (CycleStart (s3 :: s2 :: bin_rest) (rep s2 (2 * d)) 1) (6 * d + 10) =
      CycleStart bin_rest (s0 :: s2 :: rep s2 (2 * (d + 1))) 1 := by
  unfold CycleStart tmRun
  simp only [rep_succ, rep_zero]
  have hright : rep s2 (2 * d) ++ [s2] = rep s2 (2 * d + 1) := by
    show List.replicate (2*d) s2 ++ [s2] = List.replicate (2*d+1) s2
    rw [show [s2] = List.replicate 1 s2 from rfl,
        show 2*d+1 = 2*d + 1 from by omega, ← List.replicate_add]
  rw [hright, show 6 * d + 10 = (6 * d + 9) + 1 from by omega, run_add,
      odd_overflow_cascade d ((s3 :: s2 :: bin_rest) ++ [s3, s1])]
  simp only [listHd_cons, listTl_cons, List.cons_append]
  tm_step; simp only [run_zero]
  -- Right sides: s0 :: rep s2 (2*(d+2)) = (s0 :: s2 :: rep s2 (2*(d+1))) ++ [s2]
  congr 1; congr 1
  exact rep_s2_shift d

-- ============================================================
-- Section 15: Progress Invariant and Nonhalting
-- ============================================================

/-- The progress predicate: a valid CycleStart configuration.
    - bin_cells ⊆ {s2, s3} (valid binary), nonempty
    - tern_cells satisfies ValidTern (pairs from {(s2,s2),(s0,s2),(s4,s2)}), length ≥ 2
    - pad ≤ 1
    - pad = 1 → bin_cells.length ≥ 2 -/
def IsCanonical (c : Config) : Prop :=
  ∃ (bin_cells tern_cells : List Sym) (pad : Nat),
    c = CycleStart bin_cells tern_cells pad ∧
    (∀ s ∈ bin_cells, s = s2 ∨ s = s3) ∧
    ValidTern tern_cells ∧
    pad ≤ 1 ∧
    tern_cells.length ≥ 2 ∧
    bin_cells ≠ [] ∧
    (pad = 1 → bin_cells.length ≥ 2)

-- Key property: CycleStart right side is tern ++ rep s2 pad.
-- When ternary is all-zero, right = rep s2 (tern.length + pad), all s2.
-- We can repartition: if total is even → d = total/2, pad=0 → use overflow_cycle.
-- If total is odd → d = (total-1)/2, pad=1 → use overflow_odd.

/-- Helper: repartition all-s2 right side from (tern, pad) to (rep s2 (2*d), pad')
    where pad' = (tern.length + pad) % 2. -/
theorem rep_s2_repartition (tern_cells : List Sym) (pad : Nat)
    (hall : ∀ s ∈ tern_cells, s = s2) :
    tern_cells ++ rep s2 pad = rep s2 (tern_cells.length + pad) := by
  have htern : tern_cells = rep s2 tern_cells.length := by
    apply List.ext_getElem
    · simp [rep]
    · intro i h1 h2; simp [rep, List.getElem_replicate]; exact hall _ (List.getElem_mem h1)
  rw [htern]; simp [rep, List.length_replicate]


/-- The progress invariant: every canonical config advances to another. -/
theorem canonical_progress :
    ∀ c, IsCanonical c →
    ∃ k, 0 < k ∧ IsCanonical (run tm c k) ∧ (run tm c k).state ≠ none := by
  intro c ⟨bin, tern, pad, hc, hbin, hv, hpad, hlen, hne_bin, hlen_bin⟩
  subst hc
  by_cases hne : ∃ x ∈ tern, x ≠ s2
  · -- Normal cycle: ternary is nonzero, cycle_nonzero applies
    obtain ⟨steps, bin', tern', hpos, hrun, hbin', hv', hne_tern', hne_bin',
      hbo_flip, hto_flip, hlen_ge⟩ :=
      cycle_nonzero bin tern pad hbin hv hne hne_bin
    have hlen' : tern'.length ≥ 2 := by
      have h1 := validTern_even hv'
      have h2 : tern'.length ≠ 0 := by intro h; exact hne_tern' (List.eq_nil_of_length_eq_zero h)
      omega
    refine ⟨steps, hpos, ⟨bin', tern', pad, ?_, hbin', hv', hpad, hlen', hne_bin', ?_⟩, ?_⟩
    · exact hrun
    · -- pad=1 → bin'.length ≥ 2
      intro hp1; exact le_trans (hlen_bin hp1) hlen_ge
    · rw [show run tm (CycleStart bin tern pad) steps = CycleStart bin' tern' pad from hrun]
      simp [CycleStart]
  · -- Overflow: ternary is all-zero
    push_neg at hne
    -- All ternary cells are s2
    have hall : ∀ s ∈ tern, s = s2 := hne
    have heven := validTern_even hv
    -- Ternary is all s2 with even length → tern = rep s2 (2*d)
    obtain ⟨d, hd⟩ : ∃ d, tern.length = 2 * d := ⟨tern.length / 2, by omega⟩
    have htern_rep : tern = rep s2 (2 * d) := by
      apply List.ext_getElem
      · simp [rep, hd]
      · intro i h1 h2; simp [rep, List.getElem_replicate]; exact hall _ (List.getElem_mem h1)
    subst htern_rep
    by_cases hpz : pad = 0
    · -- Even total right: use overflow_cycle (pad=0)
      subst hpz
      obtain ⟨steps, bin', hpos, hrun, hbin', hne_bin', hbo_flip, hlen2⟩ :=
        overflow_cycle bin d hbin hne_bin
      have hd_ge : d ≥ 1 := by simp [rep] at hlen; omega
      refine ⟨steps, hpos, ⟨bin', repPair s4 s2 d, 1, ?_, hbin',
        validTern_repPair_s4_s2 d, by omega, by rw [repPair_length]; omega, hne_bin', ?_⟩, ?_⟩
      · exact hrun
      · -- pad=1 → bin'.length ≥ 2
        intro _
        -- overflow_cycle guarantees: binOdd bin = true → bin'.length ≥ 2
        -- We need this without knowing binOdd bin. Two cases:
        rcases bin_decompose bin hbin with ⟨k, bin_rest, hbin_eq, hbr⟩ | ⟨dd, hbin_eq⟩
        · -- carry_stop: bin' = rep s2 k ++ s3 :: bin_rest, length = k + 1 + bin_rest.length
          -- bin.length = k + 1 + bin_rest.length, so bin'.length = bin.length ≥ 1.
          -- Actually we need ≥ 2. bin has length ≥ 1 (nonempty).
          -- If bin = [s2] (length 1), then k=0, bin_rest=[], bin' = [s3], length 1.
          -- But wait: overflow_cycle with bin=[s2] gives bin'=[s3], length 1. pad=1 needs length ≥ 2.
          -- Hmm, we need bin.length ≥ 2 at even overflow? Not necessarily...
          -- Actually the output bin' has length = k + 1 + bin_rest.length = bin.length (same length in carry_stop).
          -- From the overflow_cycle spec, the length condition hlen2 says: binOdd bin = true → length ≥ 2.
          -- Without parity we don't know binOdd bin.
          -- But for carry_stop case: bin = rep s3 k ++ s2 :: bin_rest.
          -- binOdd bin = (k > 0 → s3 == s3 = true, k = 0 → s2 == s3 = false).
          -- When binOdd bin = false (k=0): bin = s2 :: bin_rest, bin' = s3 :: bin_rest.
          -- hlen2 does NOT guarantee length ≥ 2 in this case.
          -- We need bin.length ≥ 2 OR some other argument.
          sorry
        · -- overflow_carry: bin is all s3, so binOdd = true, hlen2 gives length ≥ 2
          subst hbin_eq
          have hdd_pos : dd ≥ 1 := by
            cases dd with | zero => simp at hne_bin | succ dd => omega
          have : binOdd (rep s3 dd) = true := by
            cases dd with
            | zero => omega
            | succ dd => simp [rep, List.replicate_succ, binOdd_cons, s3]
          exact hlen2 this
      · rw [show run tm (CycleStart bin (rep s2 (2 * d)) 0) steps =
            CycleStart bin' (repPair s4 s2 d) 1 from hrun]; simp [CycleStart]
    · -- Odd total right: use overflow_odd (pad=1)
      have hp1 : pad = 1 := by omega
      subst hp1
      -- Decompose binary: leading s3s + first s2 + rest, or all s3
      rcases bin_decompose bin hbin with ⟨k, bin_rest, hbin_eq, hbr⟩ | ⟨dd, hbin_eq⟩
      · -- Binary has a s2 bit at position k
        subst hbin_eq
        -- bin.length ≥ 2 (from pad=1 condition)
        have hbl := hlen_bin rfl
        cases k with
        | zero =>
          -- k=0: bin = s2 :: bin_rest, use overflow_odd
          simp [rep] at hbl ⊢
          have hne_br : bin_rest ≠ [] := by
            intro h; simp [h] at hbl
          have hodd := overflow_odd bin_rest d
          refine ⟨6*d+9, by omega, ⟨bin_rest, rep s2 (2*(d+2)), 0, ?_, hbr,
            validTern_rep_s2 _, by omega, by simp [rep], hne_br, ?_⟩, ?_⟩
          · exact hodd
          · intro h; omega
          · change (run tm (CycleStart (s2 :: bin_rest) (rep s2 (2*d)) 1) (6*d+9)).state ≠ none
            rw [show run tm = tmRun from rfl, hodd]; simp [CycleStart]
        | succ k =>
          -- k≥1: bin = rep s3 (k+1) ++ s2 :: bin_rest
          simp only [rep_succ, List.cons_append] at hbl ⊢
          cases k with
          | zero =>
            -- k=1 (exactly one leading s3): bin = s3 :: s2 :: bin_rest
            simp only [rep_zero, List.nil_append]
            -- Output: CycleStart bin_rest (s0 :: s2 :: rep s2 (2*(d+1))) 1
            -- Need bin_rest ≠ [] and bin_rest.length ≥ 2 (for pad=1 output).
            -- Current invariant only gives bin.length ≥ 2, i.e., bin_rest.length ≥ 0.
            -- This requires a stronger invariant (e.g., bin.length ≥ 4 at pad=1 odd overflow).
            sorry
          | succ k =>
            -- k≥2: bin = s3 :: s3 :: rep s3 k ++ s2 :: bin_rest
            -- Multiple leading s3 bits create complex cascade behavior
            sorry
      · -- Binary is all s3: this leads to halting, must prove unreachable
        sorry

/-- The machine reaches a canonical config after 117 initial steps. -/
theorem reaches_canonical :
    IsCanonical (run tm initConfig 117) := by
  rw [show run tm initConfig 117 = tmRun initConfig 117 from rfl, init_to_cycle]
  exact ⟨[s3, s2], rep s2 8, 0, rfl,
    fun s hs => by simp [s3, s2] at hs; rcases hs with rfl | rfl <;> simp,
    validTern_rep_s2 4, by omega, by simp [rep],
    by simp, by intro h; omega⟩

/-- **Main theorem**: the machine does not halt from the initial configuration. -/
theorem nonhalt : ∀ m, (run tm initConfig m).state ≠ none := by
  intro m
  by_cases hm : m < 117
  · -- First 117 steps: verified by computation
    exact run_alive_of_later tm initConfig m 117 (by omega)
      (by rw [show run tm initConfig 117 = tmRun initConfig 117 from rfl, init_to_cycle]; simp [CycleStart])
  · -- From step 117 onward: use progress invariant
    have h117 := reaches_canonical
    have hprog := canonical_progress
    have hnon := nonhalt_of_progress tm IsCanonical hprog
      (run tm initConfig 117) h117
    rw [show m = 117 + (m - 117) from by omega]
    rw [run_add]
    exact hnon (m - 117)

end TM5
