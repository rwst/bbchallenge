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
-/
