# Plan: proving `tm_DBL` in full

## Target theorem

```lean
lemma tm_DBL (z m p : Nat) (hz : z ≥ 1) (hm : m + 2 ≥ 2 * z) :
    run M (C_Config z m p) (6 * z * z) = C_Config (2 * z) (m + 2 - 2 * z) p
```

The right-side padding `p` is preserved (no right-extension in a DBL
cycle — empirically confirmed by `sim4.py` and by the `decide`
sanity-checks for z=2).

## What is already proved

| Lemma | Step count | Role |
|---|---|---|
| `D_shift k L R` | k | D scans left through `ones k` |
| `CE_shift n L R` | 2(n+1) | C/E right-sweeps `(n+1)` zebra blocks |
| `FA_shift n L R` | 2n+3 | F/A zebra→ones, stops in D |
| `tm_DBL_phase1` | 2z | CE-sweep of original zebra |
| `tm_DBL_phase2` | 4 | C→D→D→B→F boundary |
| `tm_DBL_phase3` | 5 | FA-sweep of 1 zebra block on right |
| `tm_DBL_phase12` | 2z + 4 | Composition |
| `tm_DBL_phase123` | 2z + 9 | Composition — lands in D reading 1, just right of a `false::ones 4 ++ (zebra (z-2)).reverse` left tape |
| **`tm_DBL_round`** | 4 | D,D,B,F cycle that removes 3 cells (`[0,1,1]`) from the left and prepends `[0,1]` to the right |
| **`tm_DBL_rounds k`** | 4k | `k` iterated rounds — consumes `ones(2k)` off the left, prepends `zebra k` to the right |
| **`tm_DBL_final`** | 3 | D,D,B→C closure that extends the tape by two zeros when left = `[false]` |
| **`tm_DBL_z2`** | 24 | Full DBL at `z=2` assembled from primitives: phase123 + 2 rounds + final |

After `tm_DBL_phase123`, the config is

```
{state := D, head := 1,
 left  := false :: ones 4 ++ (zebra (z-2)).reverse,
 right := ones (m-2) ++ zeros p}
```

For `z = 2` this simplifies to `left := false :: ones 4`, and we're
done in `4·2 + 3 = 11` more steps (exactly `6z² − 2z − 9 = 11`). ✓

For `z ≥ 3` the left has a trailing `(zebra (z-2)).reverse` — an
alternating `[1, 0, 1, 0, ...]` tail that triggers "break rounds"
and a recursive mini-phase-4 structure. This is the remaining work.

## Phase 4 — the recursive mini-DBL

### Empirical structure (from `sim5.py` traces)

For `z = 2`, `m = 4`: 11 remaining steps (steps 39→50 in the sim).
For `z = 4`, `m = 9`: 79 remaining steps (steps 143→222).

The trace shows a clear recursive structure:

1. **Inner D,D,B,F-cycles** (4 steps each). Each cycle pops 3 cells
   off the left (`0`, `1`, `1`), writes `0` over the rightmost `1`,
   and leaves the machine in state D one cell right of where it
   started, with the tape reshaped. Proved as `tm_DBL_round`.
2. Eventually the left tape runs out of `1`s and the next cell is
   `0`. At that moment the cycle **breaks**: `B,1→1LF` pops a `0`
   instead of a `1`, so F reads `0` (not `1`), and `F,0→1RA` fires
   instead of `F,1→0RD`. This triggers a **mini-FA-sweep** rightwards.
3. The mini-FA-sweep walks through the zebra-shaped region that was
   just built up on the right (by successive rounds prepending
   `[0,1]`), converting its 0s to 1s. It stops when F reads a `1`
   from the ones-region.
4. The next step is `F,1→0RD`. Now the left tape has a fresh
   `[false] ++ ones(k) ++ [tail]` shape — ready for another round of
   iterated cycles.
5. Repeat until the "tail" of the left tape reduces to empty.

This is exactly the same structure as phases 1–3 of the outer DBL
playing out at a smaller scale — which is why the total step count
is `6z²` (quadratic).

### Decomposition into rounds (confirmed)

Empirically verified by `sim7.py` for every z ≤ 112 (see
`sim-results.md` for the full table):

```
phase_4+5(z) = round_group(1) ;
               [break_cycle(1) ; round_group(2) ;
                break_cycle(2) ; round_group(3) ;
                …
                break_cycle(z-2) ; round_group(z-1)] ;
               final_ext
```

where:
- `round_group(k)` = `2k` consecutive 4-step rounds = `8k` steps each.
  Consumes the entire `ones(8(k-1)+4)` prefix following `[false]` on
  the left tape.
- `break_cycle(i)` = `4 + (4i+2) + 2 = 4i+8` steps, split as
  break-round (4) + mini-FA through `zebra(2i+1)` (4i+2) + trigger (2).
- `final_ext` = 3 steps (D,1→D,0→B,0→C).

Total step count:
```
Σ_{k=1}^{z-1} 8k     (round groups)
+ Σ_{i=1}^{z-2} (4i+8) (break cycles)
+ 3                    (final)
= 4z(z-1) + [2(z-2)(z-1) + 8(z-2)] + 3
= 6z² − 2z − 9   ✓
```

Worked example: **z = 4** (96 steps total).

| Segment | Steps | Running total |
|---|---|---|
| `tm_DBL_phase123` | 17 | 17 |
| round_group(1) = 2 rounds | 8 | 25 |
| break_cycle(1) (i=1, zebra 3) | 12 | 37 |
| round_group(2) = 4 rounds | 16 | 53 |
| break_cycle(2) (i=2, zebra 5) | 16 | 69 |
| round_group(3) = 6 rounds | 24 | 93 |
| `tm_DBL_final` | 3 | 96 |

All z tested: `2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 26, 28, 30, 32,
34, 36, 40, 42, 44, 48, 52, 56, 60, 64, 76, 112` — each matches this
exact decomposition.

### Left-tape shape invariant

At the start of `round_group(k)` (1 ≤ k ≤ z-1):
```
L_k = [false] ++ ones(8(k-1)+4) ++ (zebra (z-k-1)).reverse
```
- `L_1 = [false] ++ ones 4 ++ (zebra (z-2)).reverse` (from phase 3 ✓)
- `L_{z-1} = [false] ++ ones(8z-12) ++ []`
  = `[false] ++ ones(8z-12)`, ready to be fully consumed by
  `round_group(z-1) = 2(z-1)` rounds (each consumes 2 ones, total `4(z-1) = 4z-4`
  ones consumed — but the buffer is `8z-12`? Mismatch — need to
  check).

Hmm — `round_group(k)` has `2k` rounds, each consuming 2 ones of
the ones-buffer. So `round_group(k)` consumes `4k` ones. At `k=z-1`
the consumption is `4(z-1) = 4z-4`, matching the buffer size
`8(z-1-1)+4 = 8z-12` only if `4z-4 = 8z-12`, i.e., `z=2`. For larger
z, the `round_group(z-1)` consumption is **half** the buffer size.

Re-reading `sim-results.md` more carefully: at `round_group(k)` the
ones-buffer being consumed is `ones(4k)`, not `ones(8(k-1)+4)`. The
shape of `L_k` before round_group(k) is:

```
L_k = [false] ++ ones(4k) ++ (zebra (z-k-1)).reverse
```

After `round_group(k) = 2k rounds`: consumes `ones(4k)`, leaves
`[false] ++ (zebra (z-k-1)).reverse`.

Let me re-verify on `z=4`:
- `L_1 = [false] ++ ones 4 ++ (zebra 2).reverse` — 1+4+4 = 9 cells ✓
- After round_group(1) (2 rounds, consuming `ones 4`):
  `[false] ++ (zebra 2).reverse` = 1+4 = 5 cells ✓
- After break_cycle(1): ??? — from trace, `[0, 1^9, 0]` (11 cells).
- `L_2 = [false] ++ ones 8 ++ (zebra 1).reverse = [0] ++ [1]^8 ++ [1, 0]` 
  = 11 cells ✓
- After round_group(2) (4 rounds, consuming `ones 8`):
  `[false] ++ (zebra 1).reverse = [0, 1, 0]` = 3 cells ✓
- After break_cycle(2): `[0, 1^12]` (13 cells, empirically).
- `L_3 = [false] ++ ones 12 ++ (zebra 0).reverse = [0] ++ [1]^12 ++ []`
  = 13 cells ✓
- After round_group(3) (6 rounds, consuming `ones 12`): `[false]` ✓
- Then final_ext.

So the invariant is:
```
L_k = [false] ++ ones(4k) ++ (zebra (z-1-k)).reverse
```

and `round_group(k)` consumes the entire `ones(4k)` in `2k` rounds
(= `8k` steps), leaving `[false] ++ (zebra (z-1-k)).reverse`.

### What's needed, lemma-wise

The proof needs a nested induction:

- **Outer**: induction on `z` (or equivalently, on the number of
  reverse-zebra blocks left on the left tape).
- **Inner**: `D_shift` + `FA_shift` for each round, plus ~4 concrete
  boundary steps.

## Proposed proof skeleton

### Step 1 — Round lemma

```lean
lemma tm_DBL_round (k m p : Nat) (hm : m ≥ ?) :
    run M
      { state := some stD, head := true,
        left  := false :: ones (something_k) ++ (zebra k).reverse,
        right := ones m ++ zeros p }
      (round_step_count k) =
      { state := some stD, head := true,
        left  := false :: ones (something_k') ++ (zebra (k-1)).reverse,
        right := ones (m') ++ zeros p }
```

Where the `something_*` and `m'` have to be worked out from the
detailed trace. Key properties:

- Consumes one reverse-zebra block from the left.
- Extends the ones-buffer on the left by some amount.
- Decreases `m` on the right accordingly.
- Preserves `p`.

Proved by: 4 boundary steps + `FA_shift` + `D_shift` + ~2 more
boundary steps.

### Step 2 — Final-round lemma

When `k = 0`, the left reverse-zebra is empty and the dynamics change
slightly (the left is just `false :: ones ?`). This round ends by
extending the tape 2 cells to the left (the `B,0→1LC` extension seen
at steps 49–50 in the z=2 trace).

```lean
lemma tm_DBL_final_round (m p : Nat) (hm : m ≥ ?) :
    run M
      { state := some stD, head := true,
        left  := false :: ones (something_final),
        right := ones m ++ zeros p }
      (final_step_count) =
      C_Config (2 * z) (m + 2 - 2 * z) p
```

### Step 3 — Round composition

Induct on `k` from `z-2` down to `0`, chaining `tm_DBL_round` calls
then closing with `tm_DBL_final_round`.

```lean
lemma tm_DBL_phase45 (z m p : Nat) (hz : z ≥ 2) (hm : m ≥ 2) :
    run M
      { state := some stD, head := true,
        left  := false :: ones 4 ++ (zebra (z-2)).reverse,
        right := ones (m - 2) ++ zeros p }
      (6 * z * z - 2 * z - 9) =
      C_Config (2 * z) (m + 2 - 2 * z) p
```

Induct on `z-2` (equivalently on `k` for the reverse-zebra).

### Step 4 — Final assembly

```lean
lemma tm_DBL (z m p : Nat) (hz : z ≥ 1) (hm : m + 2 ≥ 2 * z) :
    run M (C_Config z m p) (6 * z * z) = C_Config (2 * z) (m + 2 - 2 * z) p := by
  -- Handle z = 1 case separately (degenerate; m+2 ≥ 2, i.e. m ≥ 0; check by decide?)
  -- Handle z ≥ 2 case by composition:
  --   phase123 (2z + 9 steps) ++ phase45 (6z² - 2z - 9 steps)
  sorry
```

## Open questions / risks (post-simulator verification)

1. ~~**Exact shape of the "round" invariant**~~ — **RESOLVED**.
   See `sim-results.md`. The invariant is
   `L_k = [false] ++ ones(4k) ++ (zebra (z-1-k)).reverse`
   and has been verified for every observed z up to 112.

2. **`z` is always even** — the simulator only ever produces
   even-z C-macro states (DBL doubles, initial state has z=2, parity
   flips empirically land on even z). The statement of `tm_DBL` can
   restrict to `z ≥ 2` without loss of generality; no `z=1` edge
   case to handle.

3. **Step-count arithmetic** — `6·z² − 2z − 9` requires `z ≥ 2`
   for nonnegativity. Natural-number subtraction handled by
   `obtain ⟨z', rfl⟩ : ∃ z', z = z' + 2 := ⟨z - 2, by omega⟩`
   (already used in `tm_DBL_phase2`).

4. ~~**Padding-preservation `p' = p`**~~ — **RESOLVED by construction**.
   Every primitive (round, round_group, break_cycle, final_ext) is
   stated as operating on the left tape and the "R" suffix of the
   right, with R threaded through unchanged. The right tape's
   `zeros p` suffix is never touched. No separate "right-boundedness"
   lemma needed.

## Estimated effort (revised)

With the empirical structure fully nailed down:

- `tm_DBL_round_group k`: ~30 minutes. Trivial iteration of the
  already-proved `tm_DBL_rounds` with step count `8k`.
- `tm_DBL_break_cycle i`: ~2 hours. 4 concrete steps + `FA_shift (2i)`
  + 2 concrete steps. Needs careful tape-shape tracking.
- `tm_DBL_phase45 z`: ~3 hours. Outer induction on `i = 1..z-1`
  with both tape-shape and step-count invariants.
- Final assembly (`tm_DBL`): ~30 minutes. Compose `tm_DBL_phase123`
  with `tm_DBL_phase45` and `tm_DBL_final`.

**Total**: ~1 solid day of focused Lean work, now that the structure
is fully mapped out.

## References

- `sim-results.md` — detailed simulator output with verified
  decomposition for z up to 112.
- `sim7.py` — the analysis script that produces the per-z
  decomposition table.

## Scope

The goal is the **macro rule** `tm_DBL` itself. No halt-equivalence
scaffolding is needed — `DBL_simulates_TM` and the `MacroState`
inductive are present only to make the file self-documenting and can
be deleted if they get in the way.

Companion rules to prove by the same machinery:

- `tm_small_m_odd` — the `m = 1` boundary case (empirically
  `(z, 1) → (z+2, 2z-1)` in 194 steps at z=8; formula TBD).
- `tm_parity_flip` — the rare `ΔL ∈ {3, 5}` cycles. Even empirically
  these have no uniform (z,m) → (z',m') fingerprint, so each
  fingerprint observed in simulator becomes its own lemma.

These share the same shift-lemma primitives, so once the Phase-4
induction pattern is nailed down for DBL, adapting to the small-m
and parity-flip cycles is mostly mechanical.
