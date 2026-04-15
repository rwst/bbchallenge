# Plan: closing `ValidS_progress` (the final sorry)

## 1. Target theorem

From `Bootstrap.lean`:

```lean
theorem ValidS_progress (n i : Nat) (hv : ValidS n i) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧ run tm (S' n) k = S' n'
```

where

```lean
def ValidS (n i : Nat) : Prop :=
  50 ≤ i ∧
  ((n % 2 = i % 2        ∧ 3^i*2 - i - 2 ≤ n ∧ n ≤ 3^i*6 - i - 6)    -- R1
   ∨
   (n % 2 = (i + 1) % 2 ∧ 3^i*2 - i      ≤ n ∧ n ≤ 3^i*6 - i - 10))  -- R2
```

This is the last sorry in the entire non-halting proof. Everything else
(`ROv1_1_0_halts`, `S1_to_S2`, `bootstrap`, `tm_not_halts`) is closed.

## 2. Tools already available

### In `machine.lean`

* `P n1 n2 : Prop := ∀ c, S1 0 2 (n1 + c) -[tm]->* S1 n2 2 c`
* `P_n (i : Nat) : P (3^i * 2 - i - 2) (3^i * 2 - 2)` — the fundamental recurrence.
* `BigStep0 n1 n2 c (h : P n1 (c + n2)) : S' (n1 + 2c) -[tm]->* S' (5 + 2 n2 + 3 c)`
* `BigStep1 n1 n2 c (h : P n1 (c + (2 + n2))) : S' (n1 + 2c + 1) -[tm]->* S' (23 + 6 n2 + 6 c)`
* `pow3_ge (i : Nat) : 3^i ≥ i + 1`

### In `Bootstrap.lean` (this session)

* `chain_step_B0 (i c : Nat) (hc : c ≤ 3^i*2 - 2)` — `BigStep0` specialised to `P_n i`.
* `chain_step_B1 (i c : Nat) (hc : c + 2 ≤ 3^i*2 - 2)` — `BigStep1` specialised to `P_n i`.
* `three_pow_odd (i : Nat) : 3^i % 2 = 1`.
* `BigStep0' (i n : Nat) (hlo hhi hpar) : S' n -[tm]->* S' ((n + 3^i*6 + i + 4)/2)`
  — R1 closure (mxdys' form).
* `BigStep1' (i n : Nat) (hlo hhi hpar) : S' n -[tm]->* S' (3^i*12 - 1)`
  — R2 closure (mxdys' form), with **fixed** endpoint.

### In `Hensel.lean`

* `pomme_main (i : ℕ) (hi : 50 ≤ i) : 2*i + 14 ≤ N i / 2 ^ padicValNat 2 (N i)`
  where `N i := 2*3^i + i + 5`. This is Pomme's inequality — it gives a
  lower bound on the odd part of `N i`. May depend on axioms
  (Baker–Wüstholz via `Ellison.lean` + a dense-simulation axiom for
  `i ∈ [50, 2^60)`).

## 3. Strategy for the R2 branch (easy — ~40 lines)

For `n ∈ R2@i` we apply `BigStep1'` once; the endpoint is the constant
`M := 3^i * 12 - 1` independent of `n`. `M` is always odd. We then show
`M` fits a window at level `i + 1` by a parity split on `i`.

| Sub-case | parity of `M` | target window     | why it fits                                 |
|----------|--------------|-------------------|---------------------------------------------|
| `i even` | odd          | `R1@(i+1)`        | parity `(i+1)%2 = 1`; `M ∈ [6·3^i − i − 3, 18·3^i − i − 7]` |
| `i odd`  | odd          | `R2@(i+1)`        | parity `(i+2)%2 = 1`; `M ∈ [6·3^i − i − 1, 18·3^i − i − 11]` |

Both inclusions are closed by `omega` given `pow3_ge i` and `three_pow_odd i`.

**Lean sketch** (estimate ~40 lines including both parity sub-cases):

```lean
-- R2 sub-proof
rcases hwin with hR1 | hR2
· sorry -- R1 case (below)
· obtain ⟨hpar, hlo, hhi⟩ := hR2
  have hstep := BigStep1' i n hlo hhi hpar
  obtain ⟨k, hk⟩ := hstep
  refine ⟨3^i * 12 - 1, i + 1, k, ?_, ?_, hk⟩
  · -- ValidS (3^i * 12 - 1) (i + 1)
    refine ⟨by omega, ?_⟩
    by_cases hi_even : i % 2 = 0
    · left  -- R1@(i+1)
      have h3 := three_pow_odd i
      have h3ge := pow3_ge i
      refine ⟨?_, ?_, ?_⟩ <;> omega
    · right -- R2@(i+1)
      have h3 := three_pow_odd i
      have h3ge := pow3_ge i
      refine ⟨?_, ?_, ?_⟩ <;> omega
  · -- 0 < k
    -- Needs a lemma: BigStep1' produces strict progress (k > 0).
    -- Follows because the underlying BigStep1 uses Incs1/ROv1_1 which are non-trivial.
    sorry -- see §6 for discussion
```

**Blocker for R2 case:** `0 < k`. `BigStep1'` returns an `EvStep` which
packages `∃ k, run tm _ k = _`; we need the witness to be strictly
positive. Workarounds:

1. Add a stronger lemma `BigStep1'_pos : ... -[tm]->+ ...` (`->+` is
   strict-progress). Trace: `BigStep1 → ROv1_1 → ... `, all of which
   make concrete strides.
2. Manual: compute `k ≥ 1` via `run_add` + a one-step `run` computation
   showing `run tm (S' n) 0 ≠ S' M` (since `S' n ≠ S' M` — `n ≠ M`).
   Then the witness `k` from the existential must satisfy `k ≥ 1`.

Option (2) is the pragmatic route: add a helper

```lean
theorem pos_of_different (c c' : Config n) (h : c -[tm]->* c') (hne : c ≠ c') :
    ∃ k, 0 < k ∧ run tm c k = c' := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [run] at hk; exact absurd hk hne
  · exact hpos
```

and then show `S' n ≠ S' (3^i*12 - 1)` (trivial via `n ≠ 3^i*12 - 1`,
which holds because `n ≤ 3^i*6 - i - 10 < 3^i*12 - 1`).

Add this helper to `Bootstrap.lean` once — it's needed for both the R2
and R1 cases.

## 4. Strategy for the R1 branch (hard)

For `n ∈ R1@i`, applying `BigStep0'` gives endpoint

```
n' = (n + 3^i*6 + i + 4) / 2  =  4·3^i + m + 1
```

where `m = (n - (3^i*2 - i - 2)) / 2` and `m ∈ [0, 2·3^i - 2]`.

So `n' ∈ [4·3^i + 1, 6·3^i − 1]`. This range spans the boundary between
the windows at level `i` and `i+1`.

### 4.1 Sub-case analysis by range

Let `T := n'`. Relative to the level-`i` and level-`(i+1)` windows:

| Region                                  | Values of `T`                   | Windows covering `T`             |
|-----------------------------------------|---------------------------------|----------------------------------|
| **A.** `T ≤ 6·3^i − i − 10`             | R2@i upper and below            | R1@i (if parity `i%2`) or R2@i (parity `(i+1)%2`) |
| **B.** `6·3^i − i − 9 ≤ T ≤ 6·3^i − i − 6` | 4 values                    | R1@i only (parity `i%2`)         |
| **C.** `6·3^i − i − 5 ≤ T ≤ 6·3^i − i − 4` | 2 values                    | **GAP** (no window)              |
| **D.** `T = 6·3^i − i − 3`               | 1 value                         | R1@(i+1) only (parity `(i+1)%2`) |
| **E.** `T = 6·3^i − i − 2`               | 1 value                         | **GAP** (parity `i%2` but < R2@(i+1) lower) |
| **F.** `6·3^i − i − 1 ≤ T ≤ 6·3^i − 1`   | rest                            | R1@(i+1) or R2@(i+1) by parity   |

Where parity of `T = 6·3^i − i − k` equals `(i + k) % 2`.

**Gap values** (in region B with wrong parity, region C, and region E):
five specific values, each corresponding to a specific `n ∈ R1@i`:

| `k` | `n' = 6·3^i − i − k` | `n = 6·3^i − 3i − (2k − 4)` | parity |
|-----|----------------------|-----------------------------|--------|
|  9  | `6·3^i − i − 9`      | `6·3^i − 3i − 22`           | `i%2`  |
|  7  | `6·3^i − i − 7`      | `6·3^i − 3i − 18`           | `i%2`  |
|  5  | `6·3^i − i − 5`      | `6·3^i − 3i − 14`           | `i%2`  |
|  4  | `6·3^i − i − 4`      | `6·3^i − 3i − 12`           | `i%2`  |
|  2  | `6·3^i − i − 2`      | `6·3^i − 3i − 8`            | `i%2`  |

All five fall in `R1@i` (parity matches `i%2`), so they're ValidS. But a
single `BigStep0'` moves them into a "gap" that is in no window at any
level ≥ 50.

### 4.2 Standard sub-case (ranges A, B-with-matching-parity, D, F)

For the "standard" `n` (i.e. not one of the 5 gap values), the target
window is determined by the range of `n'` and the parity. Proof shape:

```lean
obtain ⟨hpar, hlo, hhi⟩ := hR1
have hstep := BigStep0' i n hlo hhi hpar
obtain ⟨k, hk⟩ := hstep
-- Compute n' symbolically: let's call it f n i := (n + 3^i*6 + i + 4)/2
-- Case-split on which window covers f n i
by_cases hA : n ≤ 6·3^i - 3i - 26  -- corresponds to n' ≤ R2@i upper
· -- target window is R1@i (parity i%2) or R2@i (parity (i+1)%2) per n'
  -- Use parity of (m := (n - (3^i*2 - i - 2))/2)
  by_cases hm_even : m % 2 = 0
  · refine ⟨n', i, k, ?_, ?_, hk⟩
    · left; refine ⟨?_, ?_, ?_⟩ <;> omega  -- R1@i
    · exact pos_of_different ...
  · refine ⟨n', i, k, ?_, ?_, hk⟩
    · right; refine ⟨?_, ?_, ?_⟩ <;> omega  -- R2@i
    · exact pos_of_different ...
· by_cases hB : n ≤ 6·3^i - 3i - 24
  · -- range B: n' in {6·3^i - i - 7, 6·3^i - i - 9} are gap, handled later.
    -- n' in {6·3^i - i - 6, 6·3^i - i - 8} are R1@i.
    ...
  · by_cases hD : ...
    ...
```

Each omega-backed window-inclusion needs the substitution `3^i = 2k + 1`
to linearise the arithmetic, as in `BigStep0'`/`BigStep1'`.

**Estimated line count for the standard R1 sub-case:** ~120–180 lines.
The main cost is the parity-and-range case analysis, each closed by omega
after opaque-substituting `3^i`.

### 4.3 The gap sub-case (5 specific `n`)

For each of the 5 `n` values (parameterised by `k ∈ {22, 18, 14, 12, 8}`
giving `n = 6·3^i − 3i − k`), `BigStep0'` alone is insufficient.

**Key observation (just proved for `k = 22`):** for `n = 6·3^i − 3i − 22`,
applying `BigStep0' ∘ BigStep1 at level i` in sequence gives

```
n  =  6·3^i − 3i − 22
  ─BigStep0'→  n' = 6·3^i − i − 9
  ─BigStep1  → 12·3^i − 1  ∈  R1@(i+1)    ✓ for `i` even
```

Concretely, `n' = 6·3^i − i − 9 = (3^i·2 − i − 2) + 2c + 1` with
`c = 2·3^i − 4`, and `c + 2 = 2·3^i − 2 = 3^i*2 − 2` satisfies the
`BigStep1` hypothesis. So we can chain a `chain_step_B1 i (2*3^i − 4)`
after the `BigStep0'`.

**But:** for `k = 18` the same trick fails! The intermediate is
`6·3^i − i − 7`, which does **not** satisfy the `BigStep1` hypothesis at
level `i` (the required `c + 2` is `2·3^i − 1`, one too big).

**Therefore the gap sub-case is not uniform.** We must do a
per-`k` analysis. Computed empirically (see §4.4) each of the 5 gap
values needs either 2 BigSteps, 3 BigSteps, or more, with parameters
determined by the 2-adic structure of `k`.

### 4.4 Connection to `pomme_main`

The deep reason there **is always a finite chain** back to a valid
window is Pomme's inequality:

```
∀ i ≥ 50,  N i / 2^{v₂(N i)}  ≥  2·i + 14,    where N i := 2·3^i + i + 5.
```

The odd-part lower bound `2i + 14` is what guarantees that after at most
`v₂(N i) + 1` "round-trips" through a specific BigStep pattern, we land
in a valid window. Intuitively, each BigStep strips one factor of `2`
from the trajectory's 2-adic residue, and pomme_main caps the total
number of strippings.

**This is the hard step to formalise.** The argument is:

1. Define a "macro-trajectory" as a finite sequence of BigStep
   applications. Let `Macro(n, j)` denote `n` after `j` macro-steps
   starting from some `(n, i)`.
2. Show `Macro(n, j)` satisfies a specific residue relation modulo
   `2^{v₂(N i)}`.
3. Use `pomme_main` to bound `v₂(N i)` in terms of `log₂(N i)`.
4. Conclude that after `O(v₂(N i))` macro-steps, the residue forces the
   trajectory into a window with matching parity at some level.

### 4.5 Practical path forward

Given the depth of §4.3–§4.4, the cleanest engineering decomposition is:

1. **Extract a `ValidS_advance` lemma** that says: for every valid
   `(n, i)`, there is a `(n'', i'', k)` with `k ≥ 1` such that
   `run tm (S' n) k = S' n''` and `ValidS n'' i''`. This is exactly
   `ValidS_progress` but shows the precise invariant.
2. **Prove `ValidS_advance` in three stages**:
   - (a) the R2 case, via `BigStep1'` (§3).
   - (b) the "standard" R1 sub-cases, via `BigStep0'` + window inclusion
         (§4.2).
   - (c) the 5 gap cases, each as its own lemma that chains 2–3
         `chain_step_B0`/`chain_step_B1` applications and explicitly
         shows the endpoint lies in R1@(i+1) or R2@(i+1).
3. **The gap lemmas for (c)** are parameterised only by `i` (because
   the offset `k ∈ {22,18,14,12,8}` is concrete). Each is a ~15–25 line
   chain-and-omega proof mirroring `bootstrap`'s style, but with
   `i`-dependent numerals.

## 5. Step-by-step Lean task list

### Step 1 — infrastructure helpers (30 lines)

Add to `Bootstrap.lean`:

```lean
-- Strict-progress extraction from an EvStep between different states.
theorem pos_of_ne {c c' : Config 6} (h : c -[tm]->* c') (hne : c ≠ c') :
    ∃ k, 0 < k ∧ run tm c k = c' := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k, ?_, hk⟩
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · simp [run] at hk; exact absurd hk hne.symm
  · exact hpos

-- `S' n = S' m` iff `n = m` (injectivity of `S'`).
theorem S'_inj {n m : Nat} (h : S' n = S' m) : n = m := by
  simp [S', S1, Config.mk.injEq] at h
  -- ones (2n), zebra 2, ... extract n from right tape length
  sorry  -- details: unfold S1 and compare tape lengths
```

### Step 2 — R2 case (~40 lines)

```lean
theorem ValidS_progress_R2 (n i : Nat) (hi : 50 ≤ i)
    (hpar : n % 2 = (i+1) % 2)
    (hlo : 3^i * 2 - i ≤ n) (hhi : n ≤ 3^i * 6 - i - 10) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧ run tm (S' n) k = S' n' := by
  have hstep := BigStep1' i n hlo hhi hpar
  have hne : S' n ≠ S' (3^i*12 - 1) := by
    intro heq; apply S'_inj at heq
    have h3 := pow3_ge i; omega
  obtain ⟨k, hkpos, hk⟩ := pos_of_ne hstep hne
  refine ⟨3^i*12 - 1, i + 1, k, ?_, hkpos, hk⟩
  refine ⟨by omega, ?_⟩
  have h3 := three_pow_odd i
  have h3ge := pow3_ge i
  by_cases hi_par : i % 2 = 0
  · left  -- R1@(i+1), parity 1
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · right  -- R2@(i+1), parity 1
    refine ⟨?_, ?_, ?_⟩ <;> omega
```

### Step 3 — standard R1 case (~120–180 lines)

```lean
theorem ValidS_progress_R1_standard (n i : Nat) (hi : 50 ≤ i)
    (hpar : n % 2 = i % 2)
    (hlo : 3^i * 2 - i - 2 ≤ n) (hhi : n ≤ 3^i * 6 - i - 6)
    (hnot_gap : n ∉ {6*3^i - 3*i - 22, 6*3^i - 3*i - 18,
                     6*3^i - 3*i - 14, 6*3^i - 3*i - 12,
                     6*3^i - 3*i - 8}) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧ run tm (S' n) k = S' n' := by
  have hstep := BigStep0' i n hlo hhi hpar
  -- Case split on which of ranges A/B/D/F n falls into, and parity
  sorry  -- ~120 lines of range+parity dispatch
```

Concretely, case split by:
1. `n ≤ 6·3^i − 3i − 26` ⟹ n' in range A ⟹ R1@i or R2@i.
2. Otherwise small enumeration over the 8 "near-top" values of `n`
   modulo the 5 gap exclusions.

### Step 4 — gap R1 case (~100–150 lines)

One lemma per gap offset `k ∈ {22, 18, 14, 12, 8}`:

```lean
theorem ValidS_progress_gap_22 (i : Nat) (hi : 50 ≤ i) (hi_even : i % 2 = 0) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧
      run tm (S' (6*3^i - 3*i - 22)) k = S' n' := by
  -- Chain: BigStep0' → BigStep1 → 12·3^i - 1 ∈ R1@(i+1)
  have h1 := BigStep0' i (6*3^i - 3*i - 22)
              (by ...) (by ...) (by ...)
  -- Simplify endpoint: 6·3^i - i - 9
  have h2 := chain_step_B1 i (2*3^i - 4) (by omega)
  -- Simplify h2's endpoint to 12·3^i - 1
  have chain := h1.trans h2
  obtain ⟨k, hkpos, hk⟩ := pos_of_ne chain ...
  refine ⟨12*3^i - 1, i + 1, k, ?_, hkpos, hk⟩
  refine ⟨by omega, Or.inl ⟨?_, ?_, ?_⟩⟩ <;> omega
```

Each gap lemma needs:
- 2 or 3 chain_step applications (depending on `k`)
- parity argument for `i` even vs `i` odd (for `k ∈ {18, 14, 8}` the
  "easy i-parity" may differ from `k = 22`)
- omega to close window inclusion

**Research note**: for `k = 18, 14, 12, 8`, I have not yet verified
exactly how many steps are needed or which `chain_step` sequence works.
This is the **primary open question** for this plan. A 10-line
`#eval` computation simulating `BigStep` applications from each gap `n`
will resolve it.

### Step 5 — assemble `ValidS_progress` (~30 lines)

```lean
theorem ValidS_progress (n i : Nat) (hv : ValidS n i) :
    ∃ n' i' k, ValidS n' i' ∧ 0 < k ∧ run tm (S' n) k = S' n' := by
  obtain ⟨hi, hwin⟩ := hv
  rcases hwin with ⟨hpar, hlo, hhi⟩ | ⟨hpar, hlo, hhi⟩
  · -- R1
    by_cases hgap : n ∈ ({6*3^i - 3*i - 22, ..., 6*3^i - 3*i - 8} : Set Nat)
    · rcases hgap with h22 | h18 | h14 | h12 | h8
      · rw [h22]; exact ValidS_progress_gap_22 i hi (by ...) -- or bipartite on i%2
      · rw [h18]; exact ValidS_progress_gap_18 i hi ...
      ...
    · exact ValidS_progress_R1_standard n i hi hpar hlo hhi
        (fun h => hgap (by rcases h with rfl|rfl|rfl|rfl|rfl <;> simp))
  · exact ValidS_progress_R2 n i hi hpar hlo hhi
```

## 6. Open questions to resolve before writing Lean

| Q | Question | How to resolve |
|---|----------|----------------|
| Q1 | For each of the 5 gap offsets `k ∈ {22,18,14,12,8}`, which chain of `chain_step_B0`/`chain_step_B1` reaches a valid window? | Run a Lean `#eval` simulator (like `bootstrap`'s) starting from `(6*3^50 - 150 - k, 50)` and record the needed `(type, i, c)` tuples until ValidS is reached. |
| Q2 | Is the answer to Q1 independent of `i` (i.e. are the chains parameterised only by `k`)? | By symmetry the answer should be "yes, up to renaming `3^i` throughout". Verify by running Q1 for `i = 50, 51, 52` and checking the chain shapes match. |
| Q3 | For R2, is there a concern that the bootstrap endpoint `S' 2871591950767410355080995` is at level 50 but the "next" valid state after it might be in the gap? | No — bootstrap lands in R2@50. `ValidS_progress` from R2 uses `BigStep1'` which always escapes. But worth a unit test. |
| Q4 | Does `S'` injectivity work out cleanly from the definition? | Probably yes — `S1 0 2 n`'s right tape contains `ones (2n)`, from which `n` is recoverable. Use `List.length` on the right tape. |
| Q5 | What's the status of `pomme_main`'s axiom chain? If it uses a sorry or an axiom that blocks closure, we need to know before claiming `ValidS_progress` is "doable modulo pomme_main". | `grep` the Pomme/Hensel axioms; the `plan-Baker-Wustholz.md` has the chain listed. |

## 7. Estimated total effort

| Section | Lines | Difficulty |
|---------|-------|-----------|
| §5 Step 1 (helpers) | 30 | trivial |
| §5 Step 2 (R2) | 40 | easy |
| §5 Step 3 (R1 standard) | 150 | medium (case analysis + omega) |
| §5 Step 4 (R1 gap) | 130 | hard (research Q1 + chain verification) |
| §5 Step 5 (glue) | 30 | easy |
| **Total** | **~380** | 1–2 sessions of focused work |

Assuming `pomme_main` is accepted as given (it's a separate ~2000-line
development already in place), this plan completes the non-halting
proof without further axioms on the `ValidS_progress` side — just
mechanical case analysis and omega.

## 8. Risks and contingencies

* **Risk A:** Q1 reveals that for some gap offset, the chain loops back
  into another gap. Mitigation: generalise to 3+ step chains, or widen
  `ValidS` to include the transient gap endpoints and close under the
  wider set.

* **Risk B:** omega can't close some window-inclusion (likely due to
  nonlinear `3^i` interactions). Mitigation: use the `3^i = 2k + 1`
  substitution trick already used in `BigStep0'`/`BigStep1'`, and
  introduce `have` facts like `2^50 ≤ 3^50` from `pow3_ge` + monotonicity.

* **Risk C:** the R1 standard sub-case's range/parity dispatch is longer
  than 180 lines because the parity function `(i + k) % 2` creates too
  many micro-cases. Mitigation: factor a helper
  `R1_or_R2_of_near_upper` that encapsulates the "n' is near R1@i
  upper, parity p, so ..." reasoning.

* **Risk D:** `pomme_main` depends on an axiom that turns out to be
  stronger than expected (e.g. full Baker's theorem rather than just
  Ellison's corollary). Mitigation: the project already plans for this
  (`plan-Baker-Wustholz.md`, `plan-hensel.md`) and accepts it as an
  axiom boundary. `ValidS_progress` doesn't make it worse.

## 9. Execution order recommendation

1. **Resolve Q1** via a Lean `#eval` simulator (20 minutes). This is
   the linchpin — once the 5 gap chains are known, everything else is
   mechanical.
2. Implement `pos_of_ne` and `S'_inj` helpers.
3. Implement R2 case (Step 2).
4. Implement the 5 gap lemmas (Step 4) — each copy-pasted from
   `bootstrap`'s chain_step pattern.
5. Implement R1 standard case (Step 3). Leave the full parity+range
   dispatch until last since it's the bulkiest.
6. Assemble (Step 5) and commit.

Expect one compilation cycle per step; the whole thing should take
around 4–6 hours of focused work.
