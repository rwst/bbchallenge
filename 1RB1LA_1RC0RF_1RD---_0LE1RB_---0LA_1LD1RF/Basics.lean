/-!
# Mathematical Framework for TM 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

## 1. The Dynamical System

The TM's behavior, after an initial transient of 19 steps, is captured by a
deterministic dynamical system T on a state space S of run-length encoded
configurations:

  S = { M(L, c, R) | L, R ∈ ℕ*, c ∈ ℕ⁺ }  ∪  { M₀(L, R) | L, R ∈ ℕ* }

where ℕ* denotes finite sequences of natural numbers.  Each element of L or R
records the length of a run (a maximal block of consecutive 1-cells between
zero-markers on the tape).  The cursor c counts the 1-cells under and to the
right of the head in the current run.

**Initial state:**  s₀ = M([], 6, [])

## 2. Transition Rules (Macro-Step Function)

The transition function T : S → S ∪ {HALT} is:

### From M(L, c, R):

  (S1)  c ≥ 3, L = a∷L', R = d∷R'  →  M(a+1∷L', c−2, d+1∷R')
  (S2)  c = 2, L = a∷L', R = d∷R'  →  M₀(a+1∷L', d+1∷R')
  (S3)  c ≥ 3, L = [], R = []       →  M([1], c−2, [1])
  (S4)  c = 2, L = [], R = []       →  M₀([1], [1])
  (S5)  c ≥ 3, L = [], R = d∷R'     →  M([1], c−2, d+1∷R')
  (S6)  c = 2, L = [], R = d∷R'     →  M₀([1], d+1∷R')
  (S7)  c ≥ 3, L = a∷L', R = []     →  M(a+1∷L', c−2, [1])
  (S8)  c = 2, L = a∷L', R = []     →  M₀(a+1∷L', [1])
  (SH)  c = 1, L = a+1∷L'           →  M(L', a+1, 1∷d∷R)

### From M₀(a∷L, R):

  (B1)  R = [1]                      →  M(L, a+6, [])           "era complete"
  (B2)  R = [2]                      →  M(L, a+3, [1])
  (B3)  R = [3]                      →  M₀(a+4∷L, [1])
  (B4)  R = [z+4]                    →  M(a+4∷L, z+1, [1])      "bounce"
  (B5)  R = 2∷d∷R'                   →  M(L, a+3, d+1∷R')
  (B6)  R = r₁∷⋯∷rₙ, r₁≥3, n≥2     →  multi-run bounce (see §2a)
  (H)   R = 1∷(z+1)∷R'              →  HALT

### §2a. Multi-run bounce (B6)

  Input:   M₀(a∷L, [r₁, r₂, …, rₙ]) with r₁ ≥ 3, n ≥ 2

  Output L = [rₙ₋₁, …, r₂, r₁−2, a+4] ++ L    (reversed interior, then r₁−2, then a+4)
  Output cursor = rₙ − 1
  Output R = [1]

  If rₙ ≥ 2:  M(output_L, rₙ−1, [1])
  If rₙ = 1:  M₀(output_L, [1])   (which immediately triggers B1: era complete)

## 3. The Halting Equation

**Theorem (verified, not yet fully formalized).**  The machine halts if and
only if the orbit {Tⁿ(s₀)}ₙ₌₀^∞ visits the HALT rule (H).

Rule (H) fires when M₀(L, R) has R = 1∷(z+1)∷R'.  But:

  • M₀ configs with |R| ≥ 2 arise ONLY from rules (S2), (S6):
      M(…, 2, d∷R') → M₀(…, (d+1)∷R')

  • For this to match (H), we need  d+1 = 1,  i.e.  d = 0.

  • A run value d = 0 means two consecutive zero-markers with no 1-cells
    between them — a "degenerate run."

**The halting equation is therefore:**

    HALT  ⟺  ∃ n : ℕ, ∃ L c R' d,
              Tⁿ(s₀) = M(L, 2, d∷R')  ∧  d = 0

    equivalently:  ∃ n, Tⁿ(s₀) contains a zero-valued run.

## 4. Why Zero-Valued Runs Never Appear (Invariant Argument)

**Claim.**  If all runs in state s are ≥ 1 (the "AllGe1 invariant"), then
all runs in T(s) are also ≥ 1.  Proof by case analysis on T:

### Rules that only INCREMENT runs:
  (S1–S8):  Output runs are  a+1  or  d+1  (from inputs)  or  [1]  (new).
            Since a, d are naturals,  a+1 ≥ 1  and  d+1 ≥ 1.   ✓

### Rules that create NEW runs:
  (SH):     Creates run of value 1.    ✓
  (S3–S8):  Create [1].               ✓

### Rules that SUBTRACT from runs:
  (B4):     Input R = [z+4], output cursor = z+1 ≥ 1.   ✓
  (B6):     Output has r₁−2.  Since r₁ ≥ 3, we get r₁−2 ≥ 1.   ✓
            Output cursor = rₙ−1.  If rₙ ≥ 2, then rₙ−1 ≥ 1.   ✓
            If rₙ = 1, cursor = 0, produces M₀ (no cursor).      ✓

### Rules that AGGREGATE:
  (B1):     Output cursor = a+6 ≥ 6.   ✓
  (B2):     Output cursor = a+3 ≥ 3.   ✓
  (B3):     Output L has a+4 ≥ 4.      ✓
  (B5):     Output cursor = a+3, run d+1 ≥ 1.   ✓

### Initial state:
  M([], 6, []) has no runs (vacuously AllGe1) and cursor 6 ≥ 1.   ✓

**Conclusion:**  The AllGe1 invariant holds at every step.  Therefore d ≥ 1
in every M(L, 2, d∷R'), so d+1 ≥ 2, and rule (H) (which needs d+1 = 1)
never fires.   ∎

## 5. Where Is the "Random" Process?

Despite the clean invariant, the system exhibits pseudorandom behavior in
several observables.  These are the candidates for a probabilistic analysis:

### 5a. Cursor parity sequence

After each structural transition (shift, bounce, era complete), the new
cursor value is:

  • After shift (SH):        c_new = a + 1    (from leftmost L element)
  • After era complete (B1):  c_new = a + 6
  • After bounce (B4):        c_new = z + 1
  • After zero-two (B2,B5):   c_new = a + 3
  • After multi-bounce (B6):  c_new = rₙ − 1

The PARITY of c_new determines the subsequent branching:
  • c even → sweep phase ends with sweep_to_zero (S2) → M₀ processing
  • c odd  → sweep phase ends with shift (SH) → cursor moves left

This parity sequence {p₀, p₁, p₂, …} where pₖ = c_k mod 2 appears
pseudorandom and determines the "shape" of the computation tree.

### 5b. Run-value growth rates

Each run starts at 1 (from shift or boundary creation) and grows by 1
per sweep cycle it survives.  It may be consumed by a bounce (losing 2)
or by era completion (absorbed entirely).  The growth/consumption pattern
produces sequences that pass standard randomness tests.

### 5c. Era lengths

The number of macro-steps per "era" (between consecutive era-complete
events) grows roughly geometrically.  The exact growth factor depends
on the internal dynamics and has no known closed form.

## 6. Probabilistic Framing (If Randomness Were Provable)

Suppose we could prove that the cursor parity sequence {pₖ} is
indistinguishable from a fair coin flip (in some complexity-theoretic
sense).  Then:

### 6a. Random walk model

Model each run value as a random process:
  • Born at value 1
  • Incremented (+1) at each sweep it participates in
  • With probability ~1/k (where k is the number of active runs),
    selected for a bounce (−2)

This is a random walk with POSITIVE DRIFT:  E[Δ] = 1 − 2/k > 0 for k ≥ 3.
The probability of ever reaching 0 from initial value 1 is:

    P(hit 0) ≈ (p_down / p_up)^1 ≈ (1/k)^1

which is small and decreasing as the system grows.

### 6b. Union bound over all runs

The total number of runs created in the first N macro-steps is O(N).
The probability that ANY run ever hits 0:

    P(any halt) ≤ ∑_{k=1}^{N} P(run k hits 0) → 0  as N → ∞

if the individual probabilities decay fast enough (which they do under
the positive-drift model since runs are born into larger and larger
systems).

### 6c. Why this doesn't constitute a proof

Even if the above analysis shows P(halt) = 0:
  1. The system is DETERMINISTIC — there is no actual randomness.
  2. Pseudorandomness ≠ randomness.  The specific orbit could be the
     measure-zero exception.
  3. No known framework converts "P(halt)=0 under randomness assumption"
     into "the specific TM doesn't halt."

The gap between probabilistic and deterministic is fundamental.  For THIS
machine, the deterministic invariant argument (§4) actually closes the gap:
every rule algebraically guarantees runs ≥ 1, regardless of the specific
orbit.

## 7. What Would Make a Probabilistic Proof Work?

For a TM where the invariant argument fails (i.e., where some rules CAN
produce zero-valued runs but empirically never do), a probabilistic
approach would need:

  (a) A formal model of the "random" process (e.g., cursor parities
      are pairwise independent),
  (b) A proof that the model correctly describes the TM's statistics
      (this is the hard part — it requires understanding the correlations
      in the deterministic dynamics),
  (c) A 0-1 law:  if the probability of halting is 0 under the model,
      and the model captures enough of the dynamics, then halting is
      actually impossible.

Step (c) doesn't exist in current mathematics.  The closest results are:
  • Furstenberg's correspondence principle (ergodic theory ↔ combinatorics)
  • Algorithmic randomness (Martin-Löf random reals avoid c.e. measure-zero sets)
  • But TM orbits are NOT algorithmically random — they're computable!

## 8. Summary

For this specific TM:

  SYSTEM:     Piecewise-affine map T on run-length sequences
  EQUATION:   Halt ⟺ ∃n, Tⁿ(s₀) contains a zero-valued run
  RANDOMNESS: Cursor parity sequence appears pseudorandom
  PROOF:      Deterministic invariant (AllGe1) suffices — no probabilistic
              argument needed.  The proof reduces to: every rule's output
              has all runs ≥ 1 when inputs have all runs ≥ 1.

The Lean formalization challenge is:
  1. Proving the multi-run bounce rule (B6) — needs induction on |R|
  2. Connecting macro-level invariant to TM-level non-halting
  3. The individual rule proofs (S1–S8, B1–B5) are DONE in machine.lean

## 9. Multi-Run Bounce Rule (B6) — Detailed Proof Plan

### 9a. What needs to be proved

  M₀(a∷L, r₁∷r₂∷⋯∷rₙ)  with r₁ ≥ 3, n ≥ 2
  ──────────────────────────────────────────────
  ⟹ M(rev[rₙ₋₁,…,r₂, r₁−2, a+4] ++ L,  rₙ−1,  [1])     if rₙ ≥ 2
  ⟹ M₀(rev[rₙ₋₁,…,r₂, r₁−2, a+4] ++ L,  [1])            if rₙ = 1

### 9b. Available building blocks (all proven in machine.lean)

  (i)   a0_to_b :  A,0 → B  (1 step)
  (ii)  b1_to_f :  B,1 → F  (1 step)
  (iii) d1_to_b :  D,1 → B  (1 step)
  (iv)  F_shift(k, L, R) :  F sweeps right through k ones  (k+1 steps)
  (v)   f_bounce_interior(k, L, R) :  F hits interior zero, bounces  (3 steps)
        Input:  F, head=false, left = ones(k+1) ++ L, right = R
        Output: F, head=listHead R, left = [false] ++ ones(k+1) ++ L,
                right = listTail R
  (vi)  f0_d0_to_e(L, R) :  F,0 → D,0 → E  (2 steps)
  (vii) bcd_extension(k, L, p) :  B at right edge extends tape  (5 steps)

### 9c. What happens at the TM level during multi-run bounce

Starting from M₀(a∷L, [r₁, r₂, …, rₙ]) with r₁ ≥ 3:

The raw TM config (via M0_Config_cons) is:
  state = A,  head = false,
  left  = runs(a∷L),
  right = false :: false :: runs(r₁ ∷ r₂ ∷ ⋯ ∷ rₙ)

#### Phase 0: Initial BCD (5 steps)
  A,0 → B (1 step)       — a0_to_b
  B reads first element of right tape.
  Right tape = false :: false :: ones(r₁) ++ [false] ++ runs(r₂∷⋯)
  B reads false → C,0 → D,0 → E,1 → A,1 → ...

  Wait — this isn't right.  Let me re-derive.

  Actually, looking at the existing macro_zero_bounce proof (line 862):
  The sequence for M₀(a∷L, [z+4]) is:
    A,0 → B          (a0_to_b, 1 step)
    B,0 → C          (1 step, simp)
    C,0 → D          (1 step, simp)
    D,1 → B          (d1_to_b, 1 step)
    B,1 → F          (b1_to_f, 1 step)
    F_shift(z+1, ...)  (z+2 steps)
    f_bounce_interior  (3 steps)
    f0_d0_to_e         (2 steps)
    E,1 → A           (1 step)

  Total: 5 + (z+2) + 3 + 2 + 1 = z + 13 steps for R = [z+4].

  For multi-run R = [r₁, r₂, …, rₙ]:
  The first 5 steps are the SAME (A→B→C→D→B→F) since they only
  depend on r₁ ≥ 3.  After these 5 steps:

    state = F,  head = listHead(ones(r₁−3) ++ ...),
    left  = ones(2) ++ false :: true :: runs(a∷L)
          = [true, true, false, true] ++ runs(a∷L),
    right = ones(r₁−3) ++ [false] ++ runs(r₂∷⋯∷rₙ)

  Wait, I need to be more precise.  Let me trace carefully.

  Starting config:
    A, head=false, left=runs(a∷L), right=false::false::runs(r₁∷r₂∷⋯∷rₙ)

  Since r₁ ≥ 3 and n ≥ 2:
    runs(r₁∷r₂∷⋯∷rₙ) = ones(r₁) ++ [false] ++ runs(r₂∷⋯∷rₙ)

  So right = false :: false :: ones(r₁) ++ [false] ++ runs(r₂∷⋯∷rₙ)

  Step 1 (a0_to_b): B, head=false, left=true::runs(a∷L),
                     right = false :: ones(r₁) ++ [false] ++ runs(r₂∷⋯)

  Step 2 (B,0→C): C, head=false, left=true::true::runs(a∷L),
                   right = ones(r₁) ++ [false] ++ runs(r₂∷⋯)

  Step 3 (C,0→D): D, head=true, left=true::true::true::runs(a∷L),
                   right = ones(r₁−1) ++ [false] ++ runs(r₂∷⋯)
    (C reads 0, writes 1, moves R. D reads first of ones(r₁).)
    Wait — ones(r₁) starts with true (since r₁ ≥ 3, ones(r₁) = true :: ones(r₁−1)).
    So: C, head = true(!!), ...  C reads 1??

  Hmm, that would be C,1 = HALT!  That can't be right.

  Let me re-check.  The right tape after B,0→C is:
    right = ones(r₁) ++ [false] ++ runs(r₂∷⋯)

  No wait.  After step 1 (a0_to_b):
    B, head = listHead(right₀) where right₀ = false :: false :: runs(...)
    So B reads false (head of right₀).

  Actually a0_to_b says:
    run sweeper ⟨A, L, false, R⟩ 1 = ⟨B, true::L, listHead R false, listTail R⟩

  Starting: A, left=runs(a∷L), head=false, right=false::false::runs(r₁∷⋯)
  After a0_to_b: B, left=true::runs(a∷L), head=false, right=false::runs(r₁∷⋯)

  B reads false → sw_B0 = 1RC.  B writes 1, moves R to C.
  After B,0→C: C, left=true::true::runs(a∷L), head=listHead(false::runs(r₁∷⋯)),
               right=listTail(false::runs(r₁∷⋯))
  head = false (the first false before runs).
  right = runs(r₁∷⋯) = ones(r₁) ++ [false] ++ runs(r₂∷⋯)

  C reads false → sw_C0 = 1RD.  C writes 1, moves R to D.
  After C,0→D: D, left=true::true::true::runs(a∷L),
               head=listHead(ones(r₁) ++ ...),
               right=listTail(ones(r₁) ++ ...)
  head = true (first of ones(r₁) since r₁ ≥ 3, ones(r₁) starts with true)
  right = ones(r₁−1) ++ [false] ++ runs(r₂∷⋯)

  D reads true → sw_D1 = 1RB.  D writes 1, moves R to B.
  After D,1→B: B, left=true::true::true::true::runs(a∷L),
               head = listHead(ones(r₁−1) ++ [false] ++ ...),
               right = listTail(ones(r₁−1) ++ ...)
  Since r₁ ≥ 3, r₁−1 ≥ 2, so ones(r₁−1) starts with true.
  head = true, right = ones(r₁−2) ++ [false] ++ runs(r₂∷⋯)

  B reads true → sw_B1 = 0RF.  B writes 0, moves R to F.
  After B,1→F: F, left=false::true::true::true::true::runs(a∷L),
               head = listHead(ones(r₁−2) ++ [false] ++ ...),
               right = listTail(ones(r₁−2) ++ ...)
  Since r₁ ≥ 3, r₁−2 ≥ 1, ones(r₁−2) starts with true.
  head = true, right = ones(r₁−3) ++ [false] ++ runs(r₂∷⋯)

  So after 5 steps:
    F, head=true,
    left = false :: ones(4) ++ runs(a∷L)
         = false :: true :: true :: true :: true :: runs(a∷L)
    right = ones(r₁−3) ++ [false] ++ runs(r₂∷⋯∷rₙ)

  This matches the macro_zero_bounce pattern! The first 5 steps
  produce F sweeping right through ones(r₁−3).

#### Phase 1: F_shift through first run (r₁−3 steps + 1)

  F_shift(r₁−3, left, [false] ++ runs(r₂∷⋯)):
    F sweeps through r₁−3 ones. After r₁−3+1 = r₁−2 steps:

    F, head=false,
    left = ones(r₁−2) ++ false :: true :: true :: true :: true :: runs(a∷L),
    right = runs(r₂∷⋯∷rₙ)

  F reads false — this is the zero-marker between run r₁ and run r₂.

#### Phase 2: f_bounce_interior (3 steps)

  f_bounce_interior(r₁−2, ..., runs(r₂∷⋯)):
    F,0 → D,1 → B,1 → F.  After 3 steps:

    F, head = listHead(runs(r₂∷⋯)),
    left = false :: ones(r₁−1) ++ false :: true :: true :: true :: true :: runs(a∷L),
    right = listTail(runs(r₂∷⋯))

  Now runs(r₂∷⋯) = ones(r₂) ++ ... so head = true (since r₂ ≥ 1 under invariant).

  Wait, but we're proving the RULE, not using the invariant.  The head is
  listHead(runs(r₂∷⋯)) which is true when r₂ ≥ 1.

  Actually, for the rule statement we don't need r₂ ≥ 1 — the rule holds
  for ANY values.  The head will be whatever it is, and F will continue.

  If r₂ ≥ 1: head = true, F sweeps right through ones(r₂−1) next.
  If r₂ = 0: head = false, we'd get another f_bounce immediately
    (but this case can't arise under the invariant).

  For the GENERAL rule statement, we can handle both cases.  But for
  simplicity, let's first assume all runs ≥ 1 (which is the invariant).

  After this phase:
    F, head=true (assuming r₂ ≥ 1),
    left = false :: ones(r₁−1) ++ [false, true, true, true, true] ++ runs(a∷L)

  The left tape now encodes: [r₁−2, a+4] (reversed from the output formula).
  Specifically:
    false :: ones(r₁−1) = false :: ones(r₁ - 2 + 1) = encoding of run r₁−2
    then false (separator)
    then ones(4) ++ runs(a∷L) = encoding of run a+4 followed by original L

  Wait, let me be more careful about the left tape structure.

  Left after phase 2:
    false :: ones(r₁−1) ++ false :: true :: true :: true :: true :: runs(a∷L)
  = false :: ones(r₁−2+1) ++ false :: ones(4) ++ runs(a∷L)

  Hmm, ones(r₁−1) = ones(r₁−2) ++ [true] (since r₁ ≥ 3, r₁−1 ≥ 2).
  No, ones(r₁−1) is just r₁−1 copies of true.

  The left tape reads (from head outward):
    [false, true^{r₁−1}, false, true^4] ++ runs(a∷L)

  This is runs([r₁−2, a+4] ++ ...) when read as a run-length encoding?
  No — the left tape in M_Config format includes the cursor ones.

  Actually, the left tape will eventually become the LEFT of the output
  M_Config.  But we need to trace through all the bounces first.

#### Phase 3: Repeat for remaining runs (INDUCTION)

  After processing run r₁, F is now sweeping through run r₂.
  The pattern repeats:

    F_shift through r₂−1 ones → F hits next zero →
    f_bounce_interior → F starts on run r₃ → ...

  After processing run rₖ (for k = 2, …, n−1):
    F, head = true (start of run rₖ₊₁),
    left = [false, ones(rₖ−1), false, ones(rₖ₋₁−1), …,
            false, ones(r₁−1), false, ones(4)] ++ runs(a∷L),
    right = listTail(runs(rₖ₊₁∷⋯∷rₙ))

  Wait, this isn't quite right.  Let me think about it inductively.

  **Key inductive hypothesis:**  After processing runs r₁ through rₖ,
  the config is:

    F, head = listHead(runs(rₖ₊₁∷⋯∷rₙ)),
    left = runs_rev([rₖ−1, rₖ₋₁, …, r₂, r₁−2, a+4] ++ L)
         ??? (need to work out the exact left tape encoding)
    right = listTail(runs(rₖ₊₁∷⋯∷rₙ))

  This is where the proof gets subtle.  The left tape accumulates
  reversed runs.  Since runs are read nearest-to-head first, and
  we're building the left tape by prepending, the runs naturally
  reverse.

#### Phase 4: Final run rₙ

  After processing all interior runs, F sweeps through run rₙ.

  If rₙ ≥ 2:  F_shift through rₙ−1 ones.  F hits the end of the tape
  (right = []).  Then f_bounce_interior with R=[], followed by
  f0_d0_to_e, then E,1→A.  Result: M_Config with cursor = rₙ−1.

  If rₙ = 1:  F reads the single true, then immediately hits end.
  f_bounce with R=[] → f0_d0_to_e → E,1→A.  But cursor would be
  rₙ−1 = 0, giving M₀ config.

### 9d. Proof structure: induction on number of runs

The cleanest approach is to prove a LEMMA about what happens when F
encounters a sequence of runs:

  **Lemma (F_process_runs):**  For runs R = [r₁, r₂, …, rₙ] with
  all rᵢ ≥ 1:

    F, head=true, left=L, right=ones(r₁−1)++[false]++runs(r₂∷⋯∷rₙ)

  evolves (after some steps) to:

    Case n = 1, r₁ ≥ 2:
      F, head=false, left=ones(r₁) ++ L, right=[]
      (ready for f0_d0_to_e ending)

    Case n ≥ 2:
      F, head=true,
      left = ones(rₙ₋₁) ++ [false] ++ ⋯ ++ ones(r₁) ++ L,
      right = ones(rₙ−1) ++ ...
      (recurse on remaining runs, accumulating reversed runs in left)

  Actually, the cleanest decomposition is:

  **Step lemma (F_sweep_and_bounce):**
  F in the middle of a run, with more runs to the right:

    F, head=true,
    left = ones(k) ++ L,   (k ones accumulated so far)
    right = ones(m) ++ [false] ++ R_rest

  After m+1 (F_shift) + 3 (f_bounce_interior) = m+4 steps:

    F, head = listHead(R_rest),
    left = false :: ones(m+k+1) ++ L,
    right = listTail(R_rest)

  This is just F_shift composed with f_bounce_interior.
  It's already essentially provable from existing lemmas:
    1. F_shift(m, ones(k) ++ L, false :: R_rest)
    2. f_bounce_interior(m+k, ..., R_rest)

  **Then the multi-run bounce is:**

  Phase 0:  5 initial steps (A→B→C→D→B→F), producing:
    F, head=true,
    left = false :: ones(4) ++ runs(a∷L),
    right = ones(r₁−3) ++ [false] ++ runs(r₂∷⋯∷rₙ)

  Phase 1..n−1:  Apply F_sweep_and_bounce (n−1) times.
    After iteration k (processing run rₖ₊₁):
      left accumulates: false :: ones(rₖ₊₁ − 1 + prev) ++ ...
      right consumes one run

  Phase n:  F reaches end of tape (right = []).
    f_bounce_interior(k, L, [])
    f0_d0_to_e
    E,1 → A

### 9e. Concrete proof plan for Lean

**Step 1: Prove F_sweep_and_bounce lemma**

  theorem F_sweep_and_bounce (m k : Nat) (L R : List Sym) :
      run sweeper ⟨some stF, ones (k + 1) ++ L, true,
                   ones m ++ [false] ++ R⟩ (m + 4) =
      ⟨some stF, false :: ones (m + k + 2) ++ L,
       listHead R false, listTail R⟩

  Proof: compose F_shift(m, ones(k+1) ++ L, false :: R)
         then f_bounce_interior(m + k + 1, ..., R)

  The tricky part: after F_shift, the left tape is
    ones(m + 1) ++ ones(k + 1) ++ L = ones(m + k + 2) ++ L
  which needs ones_append: ones a ++ ones b = ones (a + b).

**Step 2: Prove multi-run bounce by induction**

  The induction is on the number of remaining runs.

  Base case (n = 1, single run):  Already proven as macro_zero_bounce.

  Inductive case:  Given M₀(a∷L, r₁∷r₂∷⋯∷rₙ) with n ≥ 2:

    Phase 0: 5 initial steps → F sweeping through first run
    Phase 1: F_sweep_and_bounce processes r₁ → F starts on r₂
    Remaining: F sweeping through r₂∷⋯∷rₙ with accumulated left

    This is now the SAME problem but with:
      - One fewer run to process
      - Updated left tape (r₁ absorbed)
      - F already in motion (no Phase 0 needed)

  So we need a SECONDARY induction lemma:

  **Lemma (F_process_remaining_runs):**

  For runs R = [r₁, …, rₙ] with n ≥ 1, starting from:
    F, head=true,
    left = ones(k) ++ L_acc,
    right = ones(r₁−1) ++ match R_tail with
                           | [] => []
                           | _ => false :: runs(R_tail)
    where R_tail = [r₂, …, rₙ]

  Result (after some steps):
    If rₙ ≥ 2:
      ⟨some stA, ones(rₙ−1) ++ L_final, true, false :: false :: [true]⟩
      = M_Config (output_L) (rₙ−1) [1]
    If rₙ = 1:
      ⟨some stA, L_final, false, false :: false :: [true]⟩
      = M₀_Config (output_L) [1]

    where L_final encodes the reversed processed runs.

  Proof by induction on n (number of remaining runs):

    Base (n = 1):
      F sweeps through r₁−1 ones → hits end → f_bounce → f0_d0_to_e → E→A.
      Uses F_shift + f_bounce_interior + f0_d0_to_e + E,1 step.

    Step (n ≥ 2):
      F sweeps through r₁−1 ones → F_sweep_and_bounce →
      now in the same situation with n−1 runs remaining.
      Apply induction hypothesis.

**Step 3: Combine Phase 0 with F_process_remaining_runs**

  theorem macro_multi_bounce (a : Nat) (L : List Nat)
      (r₁ : Nat) (R_inner : List Nat) (rₙ : Nat)
      (hr1 : r₁ ≥ 3) :
      run sweeper (M0_Config (a :: L) (r₁ :: R_inner ++ [rₙ])) steps =
      if rₙ ≥ 2 then
        M_Config (R_inner.reverse ++ [r₁ - 2, a + 4] ++ L) (rₙ - 1) [1]
      else
        M0_Config (R_inner.reverse ++ [r₁ - 2, a + 4] ++ L) [1]

  Proof:
    1. Unfold M0_Config, apply the 5 initial steps
    2. Apply F_process_remaining_runs with the full run list
    3. Match output

### 9f. Key auxiliary lemmas needed

  1. ones_append : ones a ++ ones b = ones (a + b)
     — Needed to merge ones during F_shift accumulation

  2. runs encoding/decoding lemmas for the left tape
     — The left tape accumulates runs in reverse order
     — Need: false :: ones(r) ++ false :: ones(r') ++ ... = runs_reversed(...)

  3. List.reverse properties for the output L

  4. Step count arithmetic
     — Total steps = 5 + Σᵢ (rᵢ−1+4) + final_phase
     — Messy but straightforward with omega

### 9g. Difficulty assessment

  • F_sweep_and_bounce: EASY (compose two existing lemmas + ones_append)
  • F_process_remaining_runs base case: MEDIUM (similar to macro_zero_bounce)
  • F_process_remaining_runs inductive step: MEDIUM (compose F_sweep_and_bounce
    with induction hypothesis, need careful left tape bookkeeping)
  • Phase 0 combination: MEDIUM (5 explicit steps, similar to macro_zero_bounce)
  • Left tape encoding: HARD (matching reversed runs to M_Config format)

  The HARDEST part is getting the left tape to match M_Config's expected
  format.  M_Config(L, c, R) has left = ones(c−1) ++ false :: runs(L).
  The accumulated left tape from F processing has a different structure
  that needs to be shown equal.

### 9h. Alternative: prove only invariant preservation, not full rule

  Instead of proving the EXACT output of multi-run bounce, we could prove:

  theorem multi_bounce_invariant (a : Nat) (L : List Nat) (R : List Nat)
      (hL : AllGe1 (a :: L)) (hR : AllGe1 R) (hR1 : R.head? = some r₁)
      (hr1 : r₁ ≥ 3) (hlen : R.length ≥ 2) :
      ∃ L' c R', run sweeper (M0_Config (a :: L) R) steps =
                  (M_Config L' c R' ∨ M0_Config L' R') ∧
                  AllGe1 L' ∧ (c ≥ 1) ∧ AllGe1 R'

  This is WEAKER but SUFFICIENT for the non-halting proof.
  It avoids computing the exact output (the hard part) and just shows
  the invariant is preserved.

  Proof sketch:  By the rule analysis in §4, multi-run bounce outputs
  have: L' contains r₁−2 ≥ 1, a+4 ≥ 4, and unchanged interior runs
  (≥ 1 by hypothesis).  R' = [1].  Cursor = rₙ−1.

  This might be provable WITHOUT full induction — just by arguing about
  the STRUCTURE of the rule's arithmetic.

### 9i. Recommended approach

  1. First prove ones_append and F_sweep_and_bounce (easy wins)
  2. Then prove F_process_remaining_runs by induction (the core)
  3. Wrap with Phase 0 to get the full multi-run bounce
  4. If step 2 stalls on left tape encoding, fall back to 9h
     (invariant-only approach)

  Estimated effort: 150–300 lines of Lean, 2–4 proof sessions.
-/
